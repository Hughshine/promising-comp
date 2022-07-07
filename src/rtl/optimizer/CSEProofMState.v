Require Import RelationClasses.
Require Import List.
Require Import Basics.
Require Import Coqlib.

Require Import sflib.
From Paco Require Import paco.

Require Import Basic.
Require Import Axioms.
Require Import Loc.
Require Import DenseOrder.
Require Import Language.
Require Import ZArith.
Require Import Maps.
Require Import FSets.
Require Import FSetInterface.
Require Import Lattice.
Require Import Event.
Require Import Syntax.
Require Import Semantics.

Require Import Memory.
Require Import Cell.
Require Import Time.
Require Import Thread.
Require Import Local.
Require Import CompAuxDef.

Require Import Kildall.
Require Import AveAnalysis.
Require Import CorrectOpt.
Require Import MsgMapping.
Require Import CSE.
Require Import LocalSim.
Require Import LibTactics.
Require Import Event.
Require Import View.
Require Import TView.

(** * Definition of Common Subexpression Elimination's Match State *)

(** Invariant of Common Subexpression Elimination, for simulation framework 
- CSE preserve share memory's equality between src and tgt *)
Definition cse_invariant: Invariant := 
    fun lo phi rss => 
        <<SC_EQ: (T_SC rss) = (S_SC rss)>>
        /\ <<MEM_EQ: (T_MEM rss) = (S_MEM rss)>>
        /\ <<EQ_IDENT_MAP: eq_ident_mapping phi (T_MEM rss)>>.

Theorem wf_cse_invariant: 
    wf_I cse_invariant.
Proof.
    unfolds wf_I.
    unfolds cse_invariant.
    intros.  destruct H as [SC_EQ H]. destruct H as [MEM_EQ COMPLETE_ID].
    unfolds eq_ident_mapping. destruct COMPLETE_ID as [DOM_EQ ID_MAPPING].
    econs; eauto.
    - intros. exists t f R. inv DOM_EQ.
    pose proof (TMEM2INJ:= SOUND loc val f t R).
    pose proof (INJ:= TMEM2INJ MSG).
    destruct INJ as [t' H].
    splits; eauto.
      {
        pose proof (COMPLETE loc t t').
        pose proof (ID_MAPPING loc t t').
        pose proof H.
        eapply H1 in H2.
        rewrite <- H2 in H.
        trivial.
      }
      {
        rewrite <- MEM_EQ; eauto.
      }
    - intros. 
      inv DOM_EQ. 
      eapply COMPLETE in INJ; eauto.
    - unfolds; intros.
    pose proof (ID_MAPPING loc t1 t1').
    pose proof (ID_MAPPING loc t2 t2').
    pose proof (H INJ1).
    pose proof (H0 INJ2).
    rewrite H1 in TIME_LT. 
    rewrite H2 in TIME_LT. 
    trivial. 
Qed.

(** Invariant holds in init state *)
Theorem cse_invariant_init:
  forall lo,  
  cse_invariant lo 
      inj_init (Build_Rss TimeMap.bot Memory.init TimeMap.bot Memory.init).
Proof.
  intro. unfolds cse_invariant. splits; eauto.
  unfolds eq_ident_mapping. splits.
- econs.
  { intros.
    simpls. 
    exists Time.bot. 
    unfolds Memory.get.
    unfolds Memory.init.
    rewrite (Cell.init_get t) in MSG.
    des_ifH MSG.
    {
      unfolds inj_init. rewrite e. eauto.
    }
    {
      discriminate.
    }
  }
  {
    intros; simpls. 
    unfolds inj_init.
    des_ifH INJ.
    {
      inv INJ.
      repeat eexists.
    }
    {
      discriminate.
    }
  }
- intros.
  unfolds inj_init.
  des_ifH H.
  { inv H. eauto.
  }
  { discriminate. 
  }
Qed.

Lemma eq_inj_implies_invariant:  
  forall lo inj inj' rss,
    eq_inj inj inj' ->
    cse_invariant lo inj rss ->  
    cse_invariant lo inj' rss.
Proof.
  intros.
  unfolds cse_invariant.
  destruct H0 as (EQ_SC & EQ_MEM & EQ_INJ). splits; eauto.
  unfolds eq_ident_mapping. 
  destruct EQ_INJ.
  unfolds eq_inj.
  splits.
  -
    inv H0. 
    eapply mem_inj_dom_eq_intro; eauto.
    *
    intros.
    apply SOUND in MSG.
    destruct MSG as (x & H'). 
    apply H in H'.
    eexists; eauto.
    *
    intros.
    apply H in INJ.
    apply COMPLETE in INJ.
    trivial.
  -
    intros.
    apply H in H2.  
    apply H1 in H2. 
    trivial.
Qed.

(** Relation between analysis result and dynamic state *)
Definition match_abstract_fact (regs: RegFile.t) (tview: TView.t) (mem: Memory.t) (tu: AveTuple.t) (lo: Ordering.LocOrdMap): Prop := 
  match tu with 
  | AveTuple.AExpr reg expr
    => regs reg = RegFile.eval_expr expr regs   (** `(r, e)` means `regs r = eval r regs` *)
  | AveTuple.AVar reg loc  (** `(r, loc)` means thread can visit from a former visited message *)
    => lo loc = Ordering.nonatomic /\ (exists t f R, 
        ( Time.le (View.pln (TView.cur tview) loc) t)
        /\
        ( Time.le t (View.rlx (TView.cur tview) loc) )
        /\
        (Memory.get loc t mem = Some (f, Message.concrete (regs reg) R))
        )
  end.

Definition match_abstract_interp 
    (regs: RegFile.t) (tview: TView.t) (mem: Memory.t) 
    (lat: AveLat.t) (lo: Ordering.LocOrdMap): Prop := 
    match lat with 
    | AveLat.Bot => False
    | AveLat.Undef => False
    | AveLat.CSet tuples => 
      (forall tu, W.In tu tuples -> match_abstract_fact regs tview mem tu lo)
    end.

Theorem never_match_bot:
  forall regs tview mem lo,
    match_abstract_interp regs tview mem AveAI.bot lo -> False.
Proof.
  intros. 
  unfold match_abstract_interp; simpls. trivial.
Qed.

Theorem never_match_undef:
  forall regs tview mem lo,
    match_abstract_interp regs tview mem AveLat.Undef lo -> False.
Proof.
  intros. 
  unfold match_abstract_interp; simpls. trivial.
Qed.

Theorem always_match_top:
  forall regs tview mem lo,
    match_abstract_interp regs tview mem AveLat.top lo.
Proof.
  intros. 
  unfold match_abstract_interp; simpls. intros.
  pose proof W.empty_1. unfolds W.Empty.
  pose proof (H0 tu). contradiction.
Qed.

Theorem ge_prsv_match_ai:
  forall regs tview mem ai ai' lo,
    match_abstract_interp regs tview mem ai lo ->
    AveAI.ge ai' ai ->
    match_abstract_interp regs tview mem ai' lo.
Proof.
  intros.
  unfolds match_abstract_interp.
  destruct ai eqn:EqAi; destruct ai' eqn:EqAI'; try discriminate; try contradiction; eauto.
Qed.

Theorem generalize_no_expr_match_ai:
  forall regs tview mem ai ai' lo,
    match_abstract_interp regs tview mem ai' lo ->
    (exists tuples, ai = AveLat.CSet tuples) ->
    AveAI.ge ai' (AveLat.GetExprs ai) ->
    forall tview mem, match_abstract_interp regs tview mem ai' lo.
Proof.
  intros.
  unfolds match_abstract_interp.
  destruct ai eqn:EqAi; destruct ai' eqn:EqAI'; try discriminate; try contradiction; eauto; 
  try solve [ destruct H0; try discriminate ].
  clear H0. 
  intros.
  pose proof H0 as H0'.
  eapply H in H0'.
  (** prove: tu <> (r, loc) *)
  unfold AveAI.ge in H1. unfold AveDS.L.ge in H1. unfold AveLat.GetExprs in H1.
  unfold W.Subset in H1.  
  pose proof (H1 tu).
  eapply H2 in H0.
  pose proof H0.
  eapply W.filter_2 in H0; eauto.
  unfolds match_abstract_fact.
  destruct tu eqn:EqTu; eauto.
  unfold AveTuple.isExpr in H1. try discriminate.
  eapply AveTuple.compat_bool_isExpr.
Qed.


Theorem match_ai_implies_opt_expr_eval_eq:
  forall e regs tview mem ai lo,
  match_abstract_interp regs tview mem ai lo ->
  RegFile.eval_expr e regs = RegFile.eval_expr (AveLat.opt_expr_with_ave e ai) regs.
Proof.
  induction e.
  - 
    intros.
    unfolds match_abstract_interp.
    destruct ai; try contradiction.
    unfolds AveLat.opt_expr_with_ave.
    unfolds AveLat.GetRegByExpr.
    remember ( W.choose (W.filter (AveTuple.isSameExpr (Inst.expr_val val)) tuples)) as Choose.
    destruct Choose eqn:EqChoose; trivial.
    rename e into tu.
    specialize (H tu).
    eapply eq_sym in HeqChoose.
    eapply W.choose_1 in HeqChoose.
    pose proof HeqChoose.
    eapply W.filter_1 in HeqChoose.
    eapply W.filter_2 in H0. 
    unfolds AveTuple.isSameExpr.
    eapply H in HeqChoose.
    unfolds match_abstract_fact.
    clear H.
    unfolds AveTuple.get_reg.
    destruct tu eqn:EqTu; subst; eauto.
    eapply Inst.beq_expr_eq in H0. subst; eauto.
    discriminate.
    eapply AveTuple.compat_bool_isSameExpr.
    eapply AveTuple.compat_bool_isSameExpr.
  -
    intros.
    unfolds match_abstract_interp.
    destruct ai; try contradiction.
    unfolds AveLat.opt_expr_with_ave.
    unfolds AveLat.GetRegByExpr.
    remember ( W.choose (W.filter (AveTuple.isSameExpr (Inst.expr_reg reg)) tuples)) as Choose.
    destruct Choose eqn:EqChoose; trivial.
    rename e into tu.
    specialize (H tu).
    eapply eq_sym in HeqChoose.
    eapply W.choose_1 in HeqChoose.
    pose proof HeqChoose.
    eapply W.filter_1 in HeqChoose.
    eapply W.filter_2 in H0. 
    unfolds AveTuple.isSameExpr.
    eapply H in HeqChoose.
    unfolds match_abstract_fact.
    clear H.
    unfolds AveTuple.get_reg.
    destruct tu eqn:EqTu; subst; eauto.
    eapply Inst.beq_expr_eq in H0. subst; eauto.
    discriminate.
    eapply AveTuple.compat_bool_isSameExpr.
    eapply AveTuple.compat_bool_isSameExpr.
  -
    intros.
    unfolds RegFile.eval_expr. folds RegFile.eval_expr. 
    specialize (IHe1 regs tview mem ai lo).
    specialize (IHe2 regs tview mem ai lo).
    pose proof H.
    pose proof H as MATCH_AI.
    eapply IHe1 in H.
    eapply IHe2 in H0.
    unfold RegFile.eval_expr.
    unfold AveLat.opt_expr_with_ave.
    fold AveLat.opt_expr_with_ave.
    fold RegFile.eval_expr.
    remember (AveLat.GetRegByExpr (Inst.expr_op2 op e1 e2) ai ) as Get.
    destruct Get eqn:EqGet; try contradiction; eauto.
    2: { 
      rewrite H; rewrite H0.
      destruct op; unfold RegFile.eval_expr; folds RegFile.eval_expr; trivial. 
    }
    unfolds match_abstract_interp.
    destruct ai; try contradiction.
    unfolds AveLat.GetRegByExpr. 
    remember ( W.choose (W.filter (AveTuple.isSameExpr  (Inst.expr_op2 op e1 e2)) tuples)) as Choose.
    destruct Choose eqn:EqChoose; try discriminate.
    rename e into tu.
    specialize (MATCH_AI tu).
    eapply eq_sym in HeqChoose.
    eapply W.choose_1 in HeqChoose.
    pose proof HeqChoose.
    eapply W.filter_1 in HeqChoose.
    eapply W.filter_2 in H1. 
    unfolds AveTuple.isSameExpr.
    eapply MATCH_AI in HeqChoose.
    unfolds match_abstract_fact.
    unfolds AveTuple.get_reg.
    destruct tu eqn:EqTu; subst; eauto; try discriminate.
    eapply Inst.beq_expr_eq in H1. subst; eauto.
    unfold RegFile.eval_expr in HeqChoose.
    fold RegFile.eval_expr in HeqChoose.
    rewrite <- HeqChoose.
    inv HeqGet.
    unfold RegFile.eval_expr. trivial.
    eapply AveTuple.compat_bool_isSameExpr.
    eapply AveTuple.compat_bool_isSameExpr.
Qed.

Theorem transform_assign_rhs_eval_eq:
    forall (r: Reg.t) inst inst' e ai r regs tview mem lo,
        transform_inst inst ai = inst'
        -> 
        inst = @Inst.assign r e
        ->
        match_abstract_interp regs tview mem ai lo
        -> 
        (
        exists e',
            inst' = Inst.assign r e' 
            /\  
            RegFile.eval_expr e regs = RegFile.eval_expr e' regs
        ).
  Proof.
    intros.
    unfolds transform_inst.
    rewrite H0 in H; simpls; try discriminate; eauto.
    remember (AveLat.GetRegByExpr e ai) as cse.
    destruct cse eqn:EqCse.
    2: {
        exists e. 
        splits; eauto.
    }
    rename t into reg'.
    unfolds AveLat.GetRegByExpr.
    destruct ai; try discriminate; eauto.
    remember (W.filter (AveTuple.isSameExpr e) tuples) as filtered.
    destruct (W.choose filtered) eqn:EqChoose; try discriminate; eauto.
    pose proof (@W.choose_1 (W.filter (AveTuple.isSameExpr e) tuples) e0).
    pose proof EqChoose.
    rewrite Heqfiltered in H3.
    eapply H2 in H3.
    pose proof H3.
    pose proof AveTuple.compat_bool_isSameExpr e.
    eapply W.filter_2 in H3; eauto.
    eapply W.filter_1 in H4; eauto.
    inversion Heqcse.
    unfold AveTuple.isSameExpr in H3.
    unfold AveTuple.get_reg in H7.
    destruct e0 eqn:EqE0.
    - exists (Inst.expr_reg reg'). splits; eauto.
      rewrite H7.
      unfolds match_abstract_interp.
      eapply H1 in H4.
      simpls.
      unfold match_abstract_fact in H4.
      eapply Inst.beq_expr_eq in H3.
      rewrite H3.
      rewrite <- H4.
      trivial.
    - discriminate.
  Qed.

(** To justify `(r, x)` can read same message *)
Definition loc_fact_valid (ai: AveLat.t) :Prop :=
  match ai with 
  | AveLat.Bot => False
  | AveLat.Undef => False
  | AveLat.CSet tuples => 
    forall r r' loc,
      W.In (AveTuple.AVar r loc) tuples ->
      W.In (AveTuple.AVar r' loc) tuples ->   
      r = r'
  end.

Inductive cse_match_frame
  (tview_src: TView.t)
  (mem_src: Memory.t)
  (lo: Ordering.LocOrdMap) 
  (regs_tgt regs_src: RegFile.t)
  (blk_tgt blk_src: BBlock.t)
  (cdhp_tgt cdhp_src: CodeHeap):Prop := 
 | cse_match_frame_intro 
   enode analysis blk l i analysis_blk
  (** there may be analysis result for each function, [analysis] act as successful or default result *)
  (ANALYSIS: 
    let transf_blk := (fun n ai =>
    match (cdhp_src!n) with 
    | Some b => Ave_B.transf_blk ai b 
    | None => AveAI.Atom ai 
      end) in
    AveDS.fixpoint_blk (cdhp_src) succ enode AveLat.top transf_blk = Some analysis
    \/ analysis = PMap.init (AveDS.AI.Atom AveLat.top)
  )
  (** transform code heap  *)
  (TRANSL_CDHP: cdhp_tgt = transform_cdhp (cdhp_src) analysis)
  (** register file equality *)
  (REG_EQ: regs_tgt = regs_src)
  (** transform blk *)
  (BLK: cdhp_src!l = Some blk )
  (PARTIAL_BLK: BBlock.bb_from_i blk i = Some blk_src)
  (AI_BLK: AveAI.br_from_i (analysis!!l) i = analysis_blk)
  (TRANSF_BLK: transform_blk blk_src analysis_blk = blk_tgt)
  (** match ai interpretation *)
  (MATCH_AI: match_abstract_interp regs_src tview_src mem_src (AveAI.getFirst analysis_blk) lo)
  (** fixpoint theorem to link basic block *)
  (FIXPOINT: forall lp (SUCC: In lp (succ blk_src)), AveAI.ge (AveAI.getFirst analysis!!lp) (AveAI.getLast analysis_blk)
   )
  (** justify only one [(r, x)] for each [x] *)
  (LOC_FACT:  loc_fact_valid (AveAI.getFirst analysis_blk))
  :
  cse_match_frame tview_src mem_src lo 
      regs_tgt regs_src
      blk_tgt blk_src
      cdhp_tgt cdhp_src
  .
Inductive cse_match_cont 
  (lo: Ordering.LocOrdMap)
  (cont_tgt cont_src: Continuation.t): Prop := 
 | cse_match_cont_base
  (DONE: cont_tgt = Continuation.done 
      /\ cont_src = Continuation.done)
  :
  cse_match_cont lo cont_tgt cont_src  
 | cse_match_cont_step
  regs_t regs_s blk_t blk_s cdhp_t cdhp_s cont_tgt' cont_src'
  (CONT_T:  cont_tgt = Continuation.stack regs_t blk_t cdhp_t cont_tgt' )
  (CONT_S:  cont_src = Continuation.stack regs_s blk_s cdhp_s cont_src' )
  (FRAME_MATCH: forall tview mem_src, cse_match_frame tview mem_src lo regs_t regs_s blk_t blk_s cdhp_t cdhp_s)
  (REM_MATCH: cse_match_cont lo cont_tgt' cont_src')
  :
  cse_match_cont lo cont_tgt cont_src  
  .

Inductive cse_match_rtl_state 
  (tview_src: TView.t)
  (mem_src: Memory.t)
  (lo: Ordering.LocOrdMap)
  (st_tgt st_src: State.t)
  : Prop :=
 | cse_match_rtl_state_intro 
  aprog
  (ANALYZE: AveDS.analyze_program (State.code st_src) succ AveLat.top Ave_B.transf_blk = aprog) 
  (OPT: cse_optimizer lo (State.code st_src) = Some (State.code st_tgt))
  (MATCH_FRAME: cse_match_frame tview_src mem_src lo 
    (State.regs st_tgt) (State.regs st_src)
    (State.blk st_tgt) (State.blk st_src)
    (State.cdhp st_tgt) (State.cdhp st_src)
    )
  (MATCH_CONT: cse_match_cont lo (State.cont st_tgt) (State.cont st_src))
  :
  cse_match_rtl_state tview_src mem_src lo st_tgt st_src.


Inductive cse_match_local_state
    (lo: Ordering.LocOrdMap) 
    (rtl_st_tgt: State.t)
    (local_st_tgt: Local.t)
    (rtl_st_src: State.t)
    (local_st_src: Local.t)
    (mem_src: Memory.t)
    (inj: Mapping) : Prop := 
 | cse_match_local_state_intro 
  (MATCH_RTL_STATE: cse_match_rtl_state (Local.tview local_st_src) (mem_src) lo rtl_st_tgt rtl_st_src)
  (TVIEW_EQ: (TView.eq (Local.tview local_st_tgt) (Local.tview local_st_src)))
  (PROMISES_EQ: (Local.promises local_st_tgt = Local.promises local_st_src))
  (INJ_PROMISES: mem_injected inj (Local.promises local_st_tgt)) 
  :
  cse_match_local_state lo rtl_st_tgt local_st_tgt rtl_st_src local_st_src mem_src inj.   

Lemma cse_match_local_state_implies_eq_local:
  forall lo rtl_tgt lc_tgt rtl_src lc_src mem_src inj,
  cse_match_local_state lo rtl_tgt lc_tgt rtl_src lc_src mem_src inj
  -> 
  lc_src = lc_tgt.
Proof.
  intros.
  inv H.
  destruct lc_src; destruct lc_tgt.
  simpls. rewrite PROMISES_EQ; rewrite TVIEW_EQ. constructor.
Qed.

Inductive cse_match_state 
        (inj: Mapping) (lo: Ordering.LocOrdMap)
        (e_tgt e_src: Thread.t rtl_lang) (preempt: bool)
        : Prop := 
 | cse_match_state_intro
  inj'
  (INVARIANT: cse_invariant lo inj' (Build_Rss (Thread.sc e_tgt) (Thread.memory e_tgt) (Thread.sc e_src) (Thread.memory e_src)))
  (MATCH_LOCAL: cse_match_local_state lo 
                  (@Thread.state rtl_lang e_tgt) (Thread.local e_tgt) 
                  (@Thread.state rtl_lang e_src) (Thread.local e_src) (Thread.memory e_src) inj)
  (PREEMPT: (preempt = true /\ eq_inj inj inj') \/ (preempt = false /\ incr_inj inj inj'))
  (* wf local, closed sc, closed memory *)
  (LOCAL_WF: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
  (CLOSED_SC: Memory.closed_timemap (Thread.sc e_tgt) (Thread.memory e_tgt))
  (MEM_CLOSED: Memory.closed (Thread.memory e_tgt))
  :
  cse_match_state inj lo e_tgt e_src preempt.

Lemma ge_prsv_loc_fact_valid:
  forall ai ai',
  loc_fact_valid ai ->
  AveAI.ge ai' ai ->
  loc_fact_valid ai'.
Proof.
  intros.
  unfolds loc_fact_valid.
  destruct ai eqn:EqAi; try contradiction; trivial.
  {
    unfolds AveAI.ge. unfolds AveDS.L.ge.
    destruct ai'; try contradiction.
    intros.
    unfolds W.Subset.
    pose proof H0.
    specialize (H0 (AveTuple.AVar r loc) H1).
    specialize (H3 (AveTuple.AVar r' loc) H2).
    specialize (H r r' loc H0 H3). trivial.
  }
Qed.

Lemma top_is_loc_fact_valid:
  loc_fact_valid AveLat.top.
Proof.
  unfolds loc_fact_valid.
  unfold AveLat.top.
  intros.
  pose proof W.empty_1. unfolds W.Empty. 
  specialize (H1 (AveTuple.AVar r loc)). 
  contradiction.
Qed.

Lemma In_empty_implies_false:
forall e,
  W.In e W.empty -> False.
Proof.
  intros.
  pose proof W.empty_1. unfolds W.Empty. 
  specialize (H0 e). 
  contradiction.
Qed.


Lemma transf_step_psrv_loc_fact_valid:
  forall ai bb ai',
    loc_fact_valid ai ->
    Ave_B.transf_step ai bb = ai' -> 
    loc_fact_valid ai'.
  intros.
  unfolds loc_fact_valid.
  unfolds Ave_B.transf_step.
  destruct bb eqn:BB; subst; eauto.
  destruct ai eqn:Ai; eauto.
  - 
    unfolds AveLat.GetExprs. 
    intros.
    assert (W.In (AveTuple.AVar r loc) tuples). {
      eapply W.filter_1 in H0.  
      trivial.
      eapply AveTuple.compat_bool_isExpr.
    }
    assert (W.In (AveTuple.AVar r' loc) tuples). {
      eapply W.filter_1 in H1. trivial.
      eapply AveTuple.compat_bool_isExpr.
    }
    specialize (H r r' loc H2 H3). trivial.
  -
    unfold Ave_I.transf. destruct c eqn:C; try contradiction; try solve [subst; eauto].
    { (** assign *)
      destruct (AveLat.GetRegByExpr
      (AveLat.opt_expr_with_ave rhs (AveLat.kill_reg ai lhs))
      (AveLat.kill_reg ai lhs)) eqn:GetReg;
      destruct (AveLat.kill_reg ai lhs) eqn:KillReg; try contradiction; trivial.
      {
        des_ifs; intros.
      }
      {
        des_ifs; intros.
      }
      {
        des_ifs; intros.
        {
          eapply W.add_3 in H0. 
          eapply W.add_3 in H1. 
          unfold AveLat.kill_reg in KillReg. 
          inv KillReg.
          eapply W.filter_1 in H0.
          eapply W.filter_1 in H1.
          specialize (H r r' loc H0 H1). trivial.
          eapply AveTuple.compat_bool_freeOfReg.
          eapply AveTuple.compat_bool_freeOfReg.
          intro; discriminate.
          intro; discriminate.
        }
        {
          unfold AveLat.kill_reg in KillReg. 
          inv KillReg.
          eapply W.filter_1 in H0.
          eapply W.filter_1 in H1.
          specialize (H r r' loc H0 H1). trivial.
          eapply AveTuple.compat_bool_freeOfReg.
          eapply AveTuple.compat_bool_freeOfReg.
        }
      }
      {
        unfolds AveLat.kill_reg. 
        destruct ai; try discriminate; eauto.
      }
      {
        unfolds AveLat.kill_reg. 
        destruct ai; try discriminate; try contradiction; eauto.
      }
      {
        des_ifs; intros.
        {
          eapply W.add_3 in H0. 
          eapply W.add_3 in H1. 
          unfold AveLat.kill_reg in KillReg. 
          inv KillReg.
          eapply W.filter_1 in H0.
          eapply W.filter_1 in H1.
          specialize (H r r' loc H0 H1). trivial.
          eapply AveTuple.compat_bool_freeOfReg.
          eapply AveTuple.compat_bool_freeOfReg.
          intro; discriminate.
          intro; discriminate.
        }
        {
          unfold AveLat.kill_reg in KillReg. 
          inv KillReg.
          eapply W.filter_1 in H0.
          eapply W.filter_1 in H1.
          specialize (H r r' loc H0 H1). trivial.
          eapply AveTuple.compat_bool_freeOfReg.
          eapply AveTuple.compat_bool_freeOfReg.
        }
      }
    }
    { (** load *)
      destruct or eqn:EqOr; eauto.
      remember (AveLat.GetRegByLoc loc (AveLat.kill_reg ai lhs)) as GetReg.
      remember (AveLat.kill_reg ai lhs) as KillReg.
      destruct GetReg eqn:EqGetReg; destruct KillReg eqn:EqKillReg; try discriminate; try contradiction; eauto.
      {
        intros.
        eapply W.add_3 in H0. 
        eapply W.add_3 in H1.
        destruct ai; unfolds AveLat.kill_reg; try discriminate. 
        inv HeqKillReg.
        eapply W.filter_1 in H0.
        eapply W.filter_1 in H1.

        specialize (H r r' loc0 H0 H1). trivial.
        eapply AveTuple.compat_bool_freeOfReg.
        eapply AveTuple.compat_bool_freeOfReg.
        intro; discriminate.
        intro; discriminate.
      }
      {
        destruct ai; try contradiction.
        unfolds AveLat.kill_reg. try discriminate.
      }
      {
        intros.
        pose proof (classic ((AveTuple.AVar r loc0) = (AveTuple.AVar lhs loc))).
        destruct H2. 2: {
          eapply W.add_3 in H0; try eauto.
          pose proof W.empty_1. unfolds W.Empty. 
          specialize (H3 (AveTuple.AVar r loc0)). 
          contradiction.
        }
        pose proof (classic ((AveTuple.AVar r' loc0) = (AveTuple.AVar lhs loc))).
        destruct H3. 2: {
          eapply W.add_3 in H1; try eauto.
          pose proof W.empty_1. unfolds W.Empty. 
          specialize (H4 (AveTuple.AVar r' loc0)). 
          contradiction.
        }
        inv H2; inv H3; trivial.
      }
      {
        intros.
        pose proof (classic ((AveTuple.AVar r loc0) = (AveTuple.AVar lhs loc))).
        pose proof (classic ((AveTuple.AVar r' loc0) = (AveTuple.AVar lhs loc))).
        destruct H2; destruct H3.
        {
          inv H2; inv H3; eauto.
        }
        {
          eapply W.add_3 in H1. 
          2: {intro G. rewrite G in H3; try contradiction. }
          pose proof (classic (loc = loc0)).
          destruct H4.
          {
            subst loc0.
            unfolds AveLat.GetRegByLoc.
            remember (W.choose (W.filter (AveTuple.isSameLoc loc) tuples)) as Choose.
            destruct Choose eqn:EqChoose; try discriminate.
            eapply eq_sym in HeqChoose.
            eapply W.choose_2 in HeqChoose.
            unfold W.Empty in HeqChoose.
            specialize (HeqChoose (AveTuple.AVar r' loc)).
            exfalso.
            eapply HeqChoose; eauto.
            eapply W.filter_3; eauto.
            eapply AveTuple.compat_bool_isSameLoc.
            unfold AveTuple.isSameLoc.
            eapply Pos.eqb_eq; trivial.
          }
          {inv H2. contradiction. }
        }
        { 
          eapply W.add_3 in H0. 
          2: {intro G. rewrite G in H2; try contradiction. }
          pose proof (classic (loc = loc0)).
          destruct H4.
          {
            subst loc0.
            unfolds AveLat.GetRegByLoc.
            remember (W.choose (W.filter (AveTuple.isSameLoc loc) tuples)) as Choose.
            destruct Choose eqn:EqChoose; try discriminate.
            eapply eq_sym in HeqChoose.
            eapply W.choose_2 in HeqChoose.
            unfold W.Empty in HeqChoose.
            specialize (HeqChoose (AveTuple.AVar r loc)).
            exfalso.
            eapply HeqChoose; eauto.
            eapply W.filter_3; eauto.
            eapply AveTuple.compat_bool_isSameLoc.
            unfold AveTuple.isSameLoc.
            eapply Pos.eqb_eq; trivial.
          }
          {inv H3. contradiction. }
        }
        {
          eapply W.add_3 in H0. 
          2: {intro G. rewrite G in H2; try contradiction. }
          eapply W.add_3 in H1. 
          2: {intro G. rewrite G in H3; try contradiction. }
          destruct ai eqn:EqAi; try discriminate; eauto.
          inv HeqKillReg.
          eapply W.filter_1 in H0.
          eapply W.filter_1 in H1.
          specialize (H r r' loc0 H0 H1). trivial.
          eapply AveTuple.compat_bool_freeOfReg.
          eapply AveTuple.compat_bool_freeOfReg.
        }
      }
      {
        remember (AveLat.kill_reg ai lhs) as KillReg.
        destruct KillReg eqn:EqKill; eauto.
        intros.
        destruct ai eqn:EqAi; unfolds AveLat.kill_reg; try discriminate; try contradiction; eauto.
        destruct ai eqn:EqAi; unfolds AveLat.kill_reg; try discriminate; try contradiction; eauto.
        destruct ai eqn:EqAi; unfolds AveLat.kill_reg; try discriminate; try contradiction; eauto.
        inv HeqKillReg.
        intros.
        eapply W.filter_1 in H0.
        eapply W.filter_1 in H1.
        specialize (H r r' loc0 H0 H1); trivial.
        eapply AveTuple.compat_bool_freeOfReg.
        eapply AveTuple.compat_bool_freeOfReg.
      }
      {
        remember (AveLat.kill_reg ai lhs) as KillReg.
        destruct KillReg eqn:EqKill; eauto.
        intros.
        destruct ai eqn:EqAi; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct ai eqn:EqAi; unfolds AveLat.kill_reg; try discriminate; try contradiction; eauto.
        destruct ai eqn:EqAi; unfolds AveLat.kill_reg; try discriminate; try contradiction; eauto.
        inv HeqKillReg.
        intros.
        eapply W.filter_1 in H0.
        eapply W.filter_1 in H1.
        specialize (H r r' loc0 H0 H1); trivial.
        eapply AveTuple.compat_bool_freeOfReg.
        eapply AveTuple.compat_bool_freeOfReg.
      }
      {
        remember (AveLat.kill_reg (AveLat.GetExprs ai) lhs) as KillReg.
        destruct KillReg eqn:EqKill; eauto.
        intros.
        destruct ai eqn:EqAi; unfolds AveLat.kill_reg; unfolds AveLat.GetExprs; try discriminate; eauto.
        destruct ai eqn:EqAi; unfolds AveLat.kill_reg; unfolds AveLat.GetExprs; try discriminate; eauto.
        destruct ai eqn:EqAi; unfolds AveLat.kill_reg; unfolds AveLat.GetExprs; try discriminate; eauto.

        inv HeqKillReg.
        intros.
        eapply W.filter_1 in H0.
        eapply W.filter_1 in H1.
        eapply W.filter_1 in H0.
        eapply W.filter_1 in H1.
        specialize (H r r' loc0 H0 H1); trivial.
        eapply AveTuple.compat_bool_isExpr.
        eapply AveTuple.compat_bool_isExpr.
        eapply AveTuple.compat_bool_freeOfReg.
        eapply AveTuple.compat_bool_freeOfReg.
      }
      {
        destruct ai eqn:EqAi; unfolds AveLat.top; eauto.
        {
          intros.
          pose proof W.empty_1. unfolds W.Empty. 
          specialize (H2 (AveTuple.AVar r loc0)). 
          contradiction.
        }
        {
          intros.
          pose proof W.empty_1. unfolds W.Empty. 
          specialize (H2 (AveTuple.AVar r loc0)). 
          contradiction.
        }
      }
    }
    { (** store *)
      destruct ow eqn:Ow. 

      destruct (AveLat.kill_var  ai lhs) eqn:Kill; eauto.
      intros.
      unfolds AveLat.kill_var.
      destruct ai; try discriminate; try contradiction; eauto.
      destruct ai; try discriminate; try contradiction; eauto.
      {
        destruct ai; try discriminate; try contradiction; eauto.
        remember (AveLat.GetExprs (AveLat.CSet tuples0)) as GetExprs.
        destruct GetExprs eqn:EqGetExprs; try discriminate; eauto.
        unfolds AveLat.GetExprs.
        inv HeqGetExprs.
        inv Kill.
        intros.
        assert (W.In (AveTuple.AVar r loc) tuples0). {
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
        }
        assert (W.In (AveTuple.AVar r' loc) tuples0). {
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
        }
        specialize (H r r' loc H2 H3); trivial.
      }
      {
        unfolds AveLat.kill_var.
        destruct ai; try discriminate; try contradiction; eauto.
        remember (AveLat.GetExprs (AveLat.CSet tuples)) as GetExprs.
        destruct GetExprs eqn:EqGetExprs; try discriminate; eauto.
        unfolds AveLat.GetExprs.
        inv HeqGetExprs.
        intros.
        assert (W.In (AveTuple.AVar r loc) tuples). {
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
        }
        assert (W.In (AveTuple.AVar r' loc) tuples). {
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
        }
        specialize (H r r' loc H2 H3); trivial.
      }
      {
        unfolds AveLat.kill_var.
        destruct ai; try discriminate; try contradiction; eauto.
        remember (AveLat.GetExprs (AveLat.CSet tuples)) as GetExprs.
        destruct GetExprs eqn:EqGetExprs; try discriminate; eauto.
        unfolds AveLat.GetExprs.
        inv HeqGetExprs.
        intros.
        assert (W.In (AveTuple.AVar r loc) tuples). {
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
        }
        assert (W.In (AveTuple.AVar r' loc) tuples). {
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
        }
        specialize (H r r' loc H2 H3); trivial.
      }
      {
        unfolds AveLat.kill_var.
        destruct ai; try discriminate; try contradiction; eauto.
        remember (AveLat.GetExprs (AveLat.CSet tuples)) as GetExprs.
        destruct GetExprs eqn:EqGetExprs; try discriminate; eauto.
        unfolds AveLat.GetExprs.
        inv HeqGetExprs.
        intros.
        assert (W.In (AveTuple.AVar r loc) tuples). {
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
        }
        assert (W.In (AveTuple.AVar r' loc) tuples). {
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
        }
        specialize (H r r' loc H2 H3); trivial.
      }
      {
        unfolds AveLat.kill_var.
        destruct ai; try discriminate; try contradiction; eauto.
        unfolds AveLat.top.
        intros.
        pose proof W.empty_1. unfolds W.Empty. 
        specialize (H2 (AveTuple.AVar r loc)). 
        contradiction.
      }
    }
    {
      destruct ai eqn:EqAi; try contradiction.
      destruct (AveLat.GetExprs ai) eqn:EqGetExprs; unfolds AveLat.GetExprs; subst; try discriminate; try contradiction; eauto.
      intros.
      unfolds AveLat.GetExprs.
      inv EqGetExprs.
      eapply W.filter_1 in H0.
      eapply W.filter_1 in H1.
      specialize (H  r r' loc H0 H1). trivial.
      eapply AveTuple.compat_bool_isExpr.
      eapply AveTuple.compat_bool_isExpr.
    }
    { (** cas *)

      destruct ow eqn:OW; 
      destruct or eqn:OR;
      destruct ai eqn:AI;
      unfolds AveLat.top;
      try discriminate; eauto; try solve [intros; exfalso; eapply In_empty_implies_false; eauto].
      {
        remember (AveLat.kill_reg (AveLat.GetExprs (AveLat.CSet tuples)) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg. 
        intros.

        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
      {
        remember (AveLat.kill_reg (AveLat.kill_var (AveLat.CSet tuples) loc) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg.
        intros. 
        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
      {
        remember (AveLat.kill_reg (AveLat.kill_var (AveLat.CSet tuples) loc) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg.
        intros. 
        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isExpr.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isExpr.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
      {
        remember (AveLat.kill_reg (AveLat.kill_var (AveLat.CSet tuples) loc) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg.
        intros. 
        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
      {
        remember (AveLat.kill_reg (AveLat.kill_var (AveLat.CSet tuples) loc) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg.
        intros. 
        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
      {
        remember (AveLat.kill_reg (AveLat.kill_var (AveLat.CSet tuples) loc) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg.
        intros. 
        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isExpr.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isExpr.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
      {
        remember (AveLat.kill_reg (AveLat.kill_var (AveLat.CSet tuples) loc) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg.
        intros. 
        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
      {
        remember (AveLat.kill_reg (AveLat.kill_var (AveLat.CSet tuples) loc) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg.
        intros. 
        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
      {
        remember (AveLat.kill_reg (AveLat.kill_var (AveLat.CSet tuples) loc) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg.
        intros. 
        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isExpr.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isExpr.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
      {
        remember (AveLat.kill_reg (AveLat.kill_var (AveLat.CSet tuples) loc) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg.
        intros. 
        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
      {
        remember (AveLat.kill_reg (AveLat.kill_var (AveLat.CSet tuples) loc) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg.
        intros. 
        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.union_1 in H0.
          destruct H0.
          {
            eapply W.filter_1 in H0; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.union_1 in H1.
          destruct H1.
          {
            eapply W.filter_1 in H1; trivial.
            eapply AveTuple.compat_bool_isExpr.
          }
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isNotSameLoc.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
      {
        remember (AveLat.kill_reg (AveLat.kill_var (AveLat.CSet tuples) loc) lhs) as KillReg.
        destruct KillReg eqn:EqKill; unfolds AveTuple.get_reg; unfolds AveLat.kill_var; unfolds AveLat.kill_reg; try discriminate; eauto.
        destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExprs; unfolds AveLat.GetExprs; try discriminate; eauto.
        inv EqGetExprs. inv HeqKillReg.
        intros. 
        assert (W.In (AveTuple.AVar r loc0) tuples). {
          eapply W.filter_1 in H0.
          eapply W.filter_1 in H0; trivial.
          eapply AveTuple.compat_bool_isExpr.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        assert (W.In (AveTuple.AVar r' loc0) tuples). {
          eapply W.filter_1 in H1.
          eapply W.filter_1 in H1; trivial.
          eapply AveTuple.compat_bool_isExpr.
          eapply AveTuple.compat_bool_freeOfReg.
        }
        specialize (H r r' loc0 H2 H3); trivial.
      }
    }
    { 
      destruct ai eqn:EqAi; try contradiction.
      destruct (AveLat.GetExprs ai) eqn:EqGetExprs; unfolds AveLat.GetExprs; subst; try discriminate; try contradiction; eauto.
      intros.
      unfolds AveLat.GetExprs.
      inv EqGetExprs.
      eapply W.filter_1 in H0.
      eapply W.filter_1 in H1.
      specialize (H  r r' loc H0 H1). trivial.
      eapply AveTuple.compat_bool_isExpr.
      eapply AveTuple.compat_bool_isExpr.
    }
    {
      destruct ai eqn:EqAi; try contradiction.
      destruct (AveLat.GetExprs ai) eqn:EqGetExprs; unfolds AveLat.GetExprs; subst; try discriminate; try contradiction; eauto.
      intros.
      unfolds AveLat.GetExprs.
      inv EqGetExprs.
      eapply W.filter_1 in H0.
      eapply W.filter_1 in H1.
      specialize (H  r r' loc H0 H1). trivial.
      eapply AveTuple.compat_bool_isExpr.
      eapply AveTuple.compat_bool_isExpr.
    }
Qed.
