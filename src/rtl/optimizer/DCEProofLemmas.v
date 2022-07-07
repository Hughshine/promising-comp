Require Import RelationClasses.        
Require Import List. 

Require Import sflib. 
From Paco Require Import paco.

Require Import Basic.
Require Import Axioms.
Require Import Loc.
Require Import LibTactics.
Require Import Integers.
Require Import Language.
Require Import ZArith.
Require Import Maps.
Require Import FSets.
Require Import FSetInterface.
Require Import Lattice.
Require Import Event.
Require Import Syntax.
Require Import Semantics.

Require Import Kildall.
Require Import LiveAnalysis.
Require Import CorrectOpt.
Require Import DCE.

Require Import Language.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import MsgMapping.
Require Import DelaySet.
Require Import LocalSim.

Require Import WFConfig.
Require Import CompAuxDef.
Require Import DCEProofMState.
Require Import MemoryProps.
Require Import promiseCertifiedAux.
Require Import Mem_at_eq_lemmas.
Require Import PromiseInjectionWeak.
Require Import CompThreadSteps.

Require Import Lib_Ordering.
Require Import Lib_MsgMapping.
Require Import Lib_View.
Require Import Lib_Memory.
Require Import Lib_Step.

Lemma split_add_msgInj_stable_concrete
      mem1 loc from to ts val R msg1 mem1'
      mem2 from' to' R' mem2'
      inj inj'
      (MEM_INJ: MsgInj inj mem1 mem2)
      (ADD: Memory.split mem1 loc from to ts (Message.concrete val R) msg1 mem1')
      (SPLIT: Memory.add mem2 loc from' to' (Message.concrete val R') mem2')
      (VIEW_INJ: opt_ViewInj inj' R R')
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj')
      (INJ_LOC: inj' loc to = Some to')
      (COMPLETE_INJ': forall loc0 to0 to0',
          inj' loc0 to0 = Some to0' ->
          exists from0 val0 R0, Memory.get loc0 to0 mem1' = Some (from0, Message.concrete val0 R0))
      (CLOSED_MEM: Memory.closed mem1):
  MsgInj inj' mem1' mem2'.
Proof.
  inv MEM_INJ.
  econs; eauto.
  - ii.
    erewrite Memory.split_o in MSG; eauto. des_ifH MSG; ss.
    des; subst. inv MSG.
    exploit Memory.add_get0; eauto. ii; des.
    do 3 eexists. splits; eauto. 
    des_ifH MSG; ss. des; subst; ss.
    inv MSG.
    exploit Memory.split_get0; eauto. ii; des.
    exploit SOUND; eauto. ii; des.
    do 3 eexists. splits; eauto.
    2: {  eapply Memory.add_get1; eauto. }
    eapply incr_inj_opt_ViewInj; eauto.
    eapply closed_optview_msginj_implies_closed_viewInj; eauto.
    2: { econs; eauto. }
    eapply closed_mem_implies_closed_msg; eauto.
    exploit SOUND; eauto. i. do 5 des1.
    do 3 eexists. splits; eauto.
    2: {  eapply Memory.add_get1; eauto. }
    eapply incr_inj_opt_ViewInj; eauto.
    eapply closed_optview_msginj_implies_closed_viewInj; eauto.
    2: { econs; eauto. }
    eapply closed_mem_implies_closed_msg; eauto.
  - ii.
    exploit COMPLETE_INJ'; eauto. ii; des. eauto.
Qed.

(** * View lemmas *)
Lemma write_cur_view_to
      tview sc loc to ord
      (WRITEABLE: Time.lt (View.rlx (TView.cur tview) loc) to)
      (TVIEW_LE: TView.wf tview):
  <<VIEW_CUR_RLX: View.rlx (TView.cur (TView.write_tview tview sc loc to ord)) loc = to>> /\
  <<VIEW_CUR_PLN: View.pln (TView.cur (TView.write_tview tview sc loc to ord)) loc = to>>.
Proof.
  unfold TView.write_tview; ss. unfold TimeMap.singleton.
  unfold TimeMap.join.
  rewrite Loc_add_eq. split.
  rewrite TimeFacts.le_join_r; eauto. eapply Time.le_lteq; eauto.
  inv TVIEW_LE. inv CUR. unfold TimeMap.le in PLN_RLX.
  specialize (PLN_RLX loc).
  rewrite TimeFacts.le_join_r; eauto.
  eapply Time.le_lteq. left. auto_solve_time_rel.
Qed.

(** * DCE ai lemmas *)
Lemma ai_interp_live_loc_cur
      inj R_tgt tview_tgt R_src tview_src nr nm loc
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (nr, nmem_remove_dead nm loc)):
  <<CUR_PLN_INJ: inj loc (View.pln (TView.cur tview_tgt) loc) = Some (View.pln (TView.cur tview_src) loc)>> /\
  <<CUR_RLX_INJ: inj loc (View.rlx (TView.cur tview_tgt) loc) = Some (View.rlx (TView.cur tview_src) loc)>> /\
  <<ACQ_PLN_INJ: inj loc (View.pln (TView.acq tview_tgt) loc) = Some (View.pln (TView.acq tview_src) loc)>> /\
  <<ACQ_RLX_INJ: inj loc (View.rlx (TView.acq tview_tgt) loc) = Some (View.rlx (TView.acq tview_src) loc)>>.
Proof.
  unfold ai_interp in *; ss. des. unfold sem_live_loc in *; ss.
  specialize (AI_INTERP0 loc). unfold nmem_remove_dead in *. destruct nm; ss; eauto.
  exploit AI_INTERP0; eauto. ii; des; splits; eauto.
  assert (LocSet.mem loc (LocSet.remove loc locs) = false).
  {
    eapply LocSet.Facts.not_mem_iff. ii.
    eapply LocSet.remove_spec in H. des; ss.
  }
  rewrite H in AI_INTERP0. ss.
  exploit AI_INTERP0; eauto. ii; des; splits; eauto.
Qed.

Lemma ai_interp_nmem_remove_dead
      inj R_tgt tview_tgt R_src tview_src nr nm loc
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (nr, nmem_remove_dead nm loc)):
  ai_interp inj R_tgt tview_tgt R_src tview_src (nr, nm).
Proof.
  unfold ai_interp in *. des; split; eauto.
  clear AI_INTERP.
  unfold sem_live_loc in *. ii.
  unfold is_dead_loc, nmem_remove_dead in *. destruct nm; ss; eauto.
  eapply AI_INTERP0; eauto.
  rewrite RegSet.Facts.remove_b.
  destruct (LocSet.mem loc0 locs) eqn:Heqe; ss.
Qed.

Lemma ai_interp_read_prsv'
      R_tgt tview_tgt R_src tview_src r v loc to to' R R' or nr nm inj
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (set_reg_dead r nr, nm))
      (INJ_TO: inj loc to = Some to')
      (VIEW_INJ: opt_ViewInj inj R R')
      (CLOSED_VIEW: closed_opt_viewinj inj R)
      (MONOTONIC_INJ: monotonic_inj inj)
  :
  ai_interp inj (RegFun.add r v R_tgt) (TView.read_tview tview_tgt loc to R or) 
            (RegFun.add r v R_src) (TView.read_tview tview_src loc to' R' or) (nr, nm).
Proof.
  unfold ai_interp in *; ss. des.
  split.
  - clear - AI_INTERP. unfold sem_live_reg in *; ss. ii.
    destruct (Reg.eq_dec r r0); subst.
    {
      do 2 (rewrite RegFun.add_spec_eq). eauto.
    }
    {
      do 2 (rewrite RegFun.add_spec_neq; eauto).      
      eapply AI_INTERP; eauto.
      unfold set_reg_dead. rewrite NREG.gsspec.
      des_if; eauto.
    }
  - clear AI_INTERP.
    unfold sem_live_loc in *; ss. ii.
    destruct (is_dead_loc loc0 nm) eqn:IS_DEAD_LOC; ss.
    exploit AI_INTERP0; eauto. rewrite IS_DEAD_LOC. eauto. ii; des.
    clear AI_INTERP0.

    unfold TimeMap.join; ss. unfold View.singleton_ur_if; ss.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED.
    {
      destruct (Ordering.le Ordering.acqrel or) eqn:LE_ACQREL.
      {
        destruct R, R'; ss.

        unfold TimeMap.singleton.
        destruct (Loc.eq_dec loc loc0); subst.
        {
          repeat (rewrite Loc_add_eq; eauto).
          splits.
          eapply inj_join_comp; eauto.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_pln; eauto.
          eapply inj_join_comp; eauto.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_pln; eauto.
          eapply inj_join_comp; eauto.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_rlx; eauto.
          eapply inj_join_comp; eauto.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_rlx; eauto.
        }
        {
          repeat (rewrite Loc_add_neq; eauto).
          unfold LocFun.init. repeat (rewrite Time_join_bot).
          splits.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_pln; eauto.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_pln; eauto.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_rlx; eauto.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_rlx; eauto.
        }

        unfold TimeMap.singleton.
        destruct (Loc.eq_dec loc loc0); subst.
        {
          repeat (rewrite Loc_add_eq; eauto).
          unfold TimeMap.bot. repeat (rewrite Time_join_bot).
          splits; try solve [do 2 (eapply inj_join_comp; eauto)].
        }
        {
          repeat (rewrite Loc_add_neq; eauto).
          unfold LocFun.init, TimeMap.bot. repeat (rewrite Time_join_bot).
          splits; eauto.
        }
      }
      {
        unfold View.singleton_ur; ss.
        unfold TimeMap.singleton, TimeMap.bot; ss.

        destruct (Loc.eq_dec loc loc0); subst.
        {
          repeat (rewrite Loc_add_eq; eauto).
          repeat (rewrite Time_join_bot; eauto).
          splits; try solve [eapply inj_join_comp; eauto].
          destruct R, R'; ss.
          eapply inj_join_comp; eauto.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_pln; eauto.
          unfold TimeMap.bot.
          repeat (rewrite Time_join_bot; eauto).
          eapply inj_join_comp; eauto.
          destruct R, R'; ss.
          eapply inj_join_comp; eauto.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_rlx; eauto.
          unfold TimeMap.bot.
          repeat (rewrite Time_join_bot; eauto).
          eapply inj_join_comp; eauto.
        }
        {
          repeat (rewrite Loc_add_neq; eauto).
          repeat (rewrite Time_join_bot; eauto).
          splits; eauto.
          destruct R, R'; ss.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_pln; eauto.
          unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).
          destruct R, R'; ss.
          eapply inj_join_comp; eauto.
          eapply view_inj_prop_rlx; eauto.
          unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).
        }
      }
    }
    {
      destruct (Ordering.le Ordering.acqrel or) eqn:LE_ACQREL; tryfalse.
      {
        clear - LE_RELAXED LE_ACQREL.
        destruct or; ss.
      }
      {
        ss. unfold TimeMap.bot; ss.
        repeat (rewrite Time_join_bot; eauto).
        unfold TimeMap.singleton; eauto.
        destruct (Loc.eq_dec loc loc0); subst.
        {
          repeat (rewrite Loc_add_eq); eauto.
          splits; eauto.
          eapply inj_join_comp; eauto.
          eapply inj_join_comp; eauto.
        }
        {
          repeat (rewrite Loc_add_neq); eauto.
          unfold LocFun.init; ss. repeat (rewrite Time_join_bot; eauto).
        }
      }
    }
Qed.

Lemma ai_interp_read_prsv
      R_tgt tview_tgt R_src tview_src r v loc to to' R R' or nr nm inj
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src
                            (set_reg_dead r nr, nmem_remove_dead nm loc))
      (INJ_TO: inj loc to = Some to')
      (VIEW_INJ: opt_ViewInj inj R R')
      (CLOSED_VIEW: closed_opt_viewinj inj R)
      (MONOTONIC_INJ: monotonic_inj inj):
  ai_interp inj (RegFun.add r v R_tgt) (TView.read_tview tview_tgt loc to R or) 
            (RegFun.add r v R_src) (TView.read_tview tview_src loc to' R' or) (nr, nm).
Proof.
  eapply ai_interp_read_prsv'; eauto.
  eapply ai_interp_nmem_remove_dead; eauto.
Qed.

Lemma NREG_GET_INCR_stable:
  forall e r nr
    (GET: NREG.get r nr = true),
    NREG.get r (set_expr_live e nr) = true.
Proof.
  induction e; ss; ii.
  - unfold set_reg_live.
    rewrite NREG.gsspec; eauto. des_if; eauto.
  - eapply IHe2 in GET. eapply IHe1 in GET. eauto.
Qed.

Lemma reg_set_in_eq:
  forall e r nr
    (REG_LIVE: RegSet.In r (Inst.regs_of_expr e)),
    NREG.get r (set_expr_live e nr) = true.
Proof.
  induction e; ss; eauto; ii.
  - eapply RegSet.Facts.empty_iff in REG_LIVE. ss.
  - eapply RegSet.Facts.singleton_1 in REG_LIVE. subst.
    unfold set_reg_live. rewrite NREG.gsspec; eauto. des_if; eauto.
  - eapply RegSet.union_spec in REG_LIVE. des; eauto.
    eapply IHe2  with (nr := nr) in REG_LIVE; eauto.
    eapply NREG_GET_INCR_stable; eauto.
Qed.

Lemma sem_live_reg_regs_eq':
  forall e R_tgt R_src
    (REGS_EQ: forall r, RegSet.In r (Inst.regs_of_expr e) -> RegFun.find r R_tgt = RegFun.find r R_src),
    RegFile.eval_expr e R_tgt = RegFile.eval_expr e R_src.
Proof.
  induction e; ss; eauto; ii.
  - eapply REGS_EQ; eauto.
    eapply RegSet.singleton_spec. eauto.
  - exploit IHe1.
    {
      instantiate (2 := R_tgt). instantiate (1 := R_src). ii.
      eapply REGS_EQ; eauto. eapply RegSet.union_spec; eauto.
    }
    exploit IHe2.
    {
      instantiate (2 := R_tgt). instantiate (1 := R_src). ii.
      eapply REGS_EQ; eauto. eapply RegSet.union_spec; eauto.
    }
    ii.
    rewrite x0. rewrite x. eauto.
Qed.

Lemma sem_live_reg_regs_eq:
  forall e R_tgt R_src nr
    (SEM_REG_EQ: sem_live_reg R_tgt R_src (set_expr_live e nr)),
    RegFile.eval_expr e R_tgt = RegFile.eval_expr e R_src.
Proof.
  ii.
  unfold sem_live_reg in *.
  assert (forall r, RegSet.In r (Inst.regs_of_expr e) -> RegFun.find r R_tgt = RegFun.find r R_src).
  {
    ii. eapply reg_set_in_eq in H. eauto.
  }
  eapply sem_live_reg_regs_eq'; eauto.
Qed.

Lemma ai_interp_live_regs_eq
      inj R_tgt tview_tgt R_src tview_src e nr nm
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (set_expr_live e nr, nm)):
  RegFile.eval_expr e R_tgt = RegFile.eval_expr e R_src.
Proof.
  unfold ai_interp in *. des.
  eapply sem_live_reg_regs_eq; eauto.
Qed.

Lemma NREG_get_set_live:
  forall e nr r
    (GET: NREG.get r nr = true),
    NREG.get r (set_expr_live e nr) = true.
Proof.
  induction e; ii; eauto.
  unfold set_expr_live. unfold set_reg_live.
  rewrite NREG.gsspec; eauto.
  des_if; eauto.
Qed.

Lemma sem_live_reg_less
      e nr R_tgt R_src
      (SEM_LIVE_REG: sem_live_reg R_tgt R_src (set_expr_live e nr)):
  sem_live_reg R_tgt R_src nr.
Proof.
  unfold sem_live_reg in *; ss. ii.
  eapply NREG_get_set_live with (e := e) in H.
  eapply SEM_LIVE_REG in H; eauto.
Qed.

Lemma sem_live_loc_write_na_loc
      inj tview_tgt sc_tgt to tview_src sc_src to' nm inj' ow loc lo
      (SEM_LIVE_LOC: sem_live_loc inj tview_tgt tview_src (nmem_add_dead nm loc))
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj')
      (INJ_TO: inj' loc to = Some to')
      (WRITABLE_TGT: Time.lt (View.rlx (TView.cur tview_tgt) loc) to)
      (TVIEW_WF_TGT: TView.wf tview_tgt)
      (WRITABLE_SRC: Time.lt (View.rlx (TView.cur tview_src) loc) to')
      (TVIEW_WF_SRC: TView.wf tview_src)
      (CUR_ACQ: cur_acq lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                        (TView.cur tview_src) (TView.acq tview_src))
      (CUR_ACQ_PLN: cur_acq_pln lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                                (TView.cur tview_src) (TView.acq tview_src))
      (NA_LOC: lo loc = Ordering.nonatomic):
  sem_live_loc inj'
               (TView.write_tview tview_tgt sc_tgt loc to ow)
               (TView.write_tview tview_src sc_src loc to' ow) nm.
Proof.
  unfold sem_live_loc in *. ii.
  unfold TView.write_tview; ss. unfold TimeMap.join, TimeMap.singleton; ss.
  destruct (Loc.eq_dec loc loc0); subst.
  - repeat (rewrite Loc_add_eq; eauto).
    clear SEM_LIVE_LOC. inv TVIEW_WF_TGT. inv TVIEW_WF_SRC.
    inv CUR; ss. inv CUR0; ss.
    splits.
    {
      unfold Time.join. des_if; eauto.
      des_if; eauto.
      clear - l0 PLN_RLX0 WRITABLE_SRC.
      unfold TimeMap.le in PLN_RLX0. specialize (PLN_RLX0 loc0).
      cut (Time.le to' (View.rlx (TView.cur tview_src) loc0)). ii.
      clear - WRITABLE_SRC H. auto_solve_time_rel.
      econs; eauto. auto_solve_time_rel.
      clear - l WRITABLE_TGT PLN_RLX. unfold TimeMap.le in PLN_RLX.
      specialize (PLN_RLX loc0).
      cut (Time.le to (View.rlx (TView.cur tview_tgt) loc0)). ii.
      auto_solve_time_rel. econs; eauto. auto_solve_time_rel.
    }
    {
      unfold cur_acq_pln in CUR_ACQ_PLN. exploit CUR_ACQ_PLN; eauto. clear CUR_ACQ_PLN.
      ii; des.
      {
        unfold Time.join. des_if; eauto.
        {
          des_if; eauto.
          eapply INCR_INJ in LT0.
          exploit monotonic_inj_implies_le_prsv; [ | eapply l | eapply LT0 | eapply INJ_TO | eauto..]; eauto.
          ii. clear - l0 x0. auto_solve_time_rel.
        }
        {
          des_if; eauto.
          eapply INCR_INJ in LT0.
          exploit MON_INJ; eauto. ii. auto_solve_time_rel.
        }
      }
      {
        rewrite TimeFacts.le_join_r; eauto.
        rewrite TimeFacts.le_join_r; eauto.
        econs. auto_solve_time_rel.
        econs. auto_solve_time_rel.
      }
    }
    {
      rewrite TimeFacts.le_join_r; eauto.
      rewrite TimeFacts.le_join_r; eauto.
      econs. eauto.
      econs. eauto.
    }
    {
      unfold cur_acq in CUR_ACQ. exploit CUR_ACQ; eauto. clear CUR_ACQ.
      ii; des.
      {
        unfold Time.join. des_if; eauto.
        {
          des_if; eauto.
          eapply INCR_INJ in LT0.
          exploit monotonic_inj_implies_le_prsv; [ | eapply l | eapply LT0 | eapply INJ_TO | eauto..]; eauto.
          ii. auto_solve_time_rel.
        }
        {
          des_if; eauto.
          exploit MON_INJ; [eapply l | eauto..]. ii. auto_solve_time_rel.
        }
      }
      {
        rewrite <- EQ. rewrite <- EQ0.
        rewrite TimeFacts.le_join_r; eauto.
        rewrite TimeFacts.le_join_r; eauto.
        econs. eauto.
        econs. eauto.
      }
    }
  - repeat (rewrite Loc_add_neq; eauto).
    unfold LocFun.init; ss.
    repeat (rewrite Time_join_bot); eauto.
    exploit SEM_LIVE_LOC; eauto.
    instantiate (1 := loc0).
    clear - H n. unfold is_dead_loc in *; ss. destruct nm; ss.
    rewrite LocSet.Facts.add_neq_b; eauto.
    ii; des. splits; eauto.
Qed.

Lemma sem_live_loc_write_at_loc
      inj tview_tgt sc_tgt to tview_src sc_src to' nm inj' ow loc
      (SEM_LIVE_LOC: sem_live_loc inj tview_tgt tview_src nm)
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj')
      (INJ_TO: inj' loc to = Some to'):
  sem_live_loc inj'
               (TView.write_tview tview_tgt sc_tgt loc to ow)
               (TView.write_tview tview_src sc_src loc to' ow) nm.
Proof.
  unfold sem_live_loc in *. ii.
  exploit SEM_LIVE_LOC; eauto. ii; des.
  unfold TView.write_tview; eauto; ss.
  unfold TimeMap.join, TimeMap.singleton; eauto.
  destruct (Loc.eq_dec loc loc0); subst.
  - repeat (rewrite Loc_add_eq; eauto).
    splits; try solve [eapply inj_join_comp; eauto].
  - repeat (rewrite Loc_add_neq; eauto). repeat (rewrite Time_join_bot in *; ss).
    splits; eauto.
Qed.

Lemma sem_live_reg_set_reg_dead
      R_tgt R_src nr r
      (SEM_LIVE_REG: sem_live_reg R_tgt R_src nr):
  sem_live_reg R_tgt R_src (set_reg_dead r nr).
Proof.
  unfold sem_live_reg in *. ii.
  unfold set_reg_dead in *. rewrite NREG.gsspec in H.
  des_ifH H; ss. eauto.
Qed.

Lemma ai_interp_set_reg_dead
      inj R_tgt R_src tview_tgt tview_src nr nm r
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (nr, nm)):
  ai_interp inj R_tgt tview_tgt R_src tview_src (set_reg_dead r nr, nm).
Proof.
  unfold ai_interp in *. des; eauto. split; eauto.
  eapply sem_live_reg_set_reg_dead; eauto.
Qed.

Lemma sem_live_loc_all
      inj tview tview'
      (SEM_LIVE_LOC: sem_live_loc inj tview tview' (NMem LocSet.empty)):
  ViewInj inj (TView.cur tview) (TView.cur tview').
Proof.
  unfold sem_live_loc in *. ss.
  unfold ViewInj. destruct tview, tview'; ss.
  destruct cur, cur0; ss.
  split.
  unfold TMapInj. ii.
  specialize (SEM_LIVE_LOC loc). exploit SEM_LIVE_LOC; eauto. ii; des.
  rewrite injDom in x. inv x; eauto.
  unfold TMapInj. ii.
  specialize (SEM_LIVE_LOC loc). exploit SEM_LIVE_LOC; eauto. ii; des.
  rewrite injDom in x1. inv x1; eauto.
Qed.

Lemma sem_live_loc_all'
      inj tview tview'
      (SEM_LIVE_LOC: sem_live_loc inj tview tview' (NMem LocSet.empty)):
  ViewInj inj (TView.acq tview) (TView.acq tview').
Proof.
  unfold sem_live_loc in *. ss.
  unfold ViewInj. destruct tview, tview'; ss.
  destruct acq, acq0; ss.
  split.
  unfold TMapInj. ii.
  specialize (SEM_LIVE_LOC loc). exploit SEM_LIVE_LOC; eauto. ii; des.
  rewrite injDom in x0. inv x0; eauto.
  unfold TMapInj. ii.
  specialize (SEM_LIVE_LOC loc). exploit SEM_LIVE_LOC; eauto. ii; des.
  rewrite injDom in x2. inv x2; eauto.
Qed.

Lemma ai_interp_rely_stable
      inj inj' R_tgt tview_tgt R_src tview_src nr nm
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (nr, nm))
      (INCR_INJ: incr_inj inj inj'):
  ai_interp inj' R_tgt tview_tgt R_src tview_src (nr, nm).
Proof.
  unfold ai_interp in *. des. split; eauto.
  unfold sem_live_loc in *. ii. exploit AI_INTERP0; eauto.
  ii; des.
  splits; eauto.
Qed.

Lemma ai_interp_write_stable
      inj R_tgt tview_tgt sc_tgt R_src to tview_src sc_src to' inj' ow loc e nr nm
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (set_expr_live e nr, nm))
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj')
      (INJ_TO: inj' loc to = Some to'):
  ai_interp inj' R_tgt (TView.write_tview tview_tgt sc_tgt loc to ow)
            R_src (TView.write_tview tview_src sc_src loc to' ow) (nr, nm).
Proof.
  unfold ai_interp in *; ss.
  des; splits; eauto.
  eapply sem_live_reg_less; eauto.
  eapply sem_live_loc_write_at_loc; eauto.
Qed.

Lemma ai_interp_write_stable'
      inj R_tgt tview_tgt sc_tgt R_src to tview_src sc_src to' inj' ow loc nr nm
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (nr, nm))
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj')
      (INJ_TO: inj' loc to = Some to'):
  ai_interp inj' R_tgt (TView.write_tview tview_tgt sc_tgt loc to ow)
            R_src (TView.write_tview tview_src sc_src loc to' ow) (nr, nm).
Proof.
  unfold ai_interp in *; ss.
  des; splits; eauto.
  eapply sem_live_loc_write_at_loc; eauto.
Qed.

Lemma ge_sem_live_reg
      nr nr' R_tgt R_src
      (LIVE_REG: sem_live_reg R_tgt R_src nr)
      (GE: NREG.ge nr nr'):
  sem_live_reg R_tgt R_src nr'.
Proof.
  unfold sem_live_reg in *. ii.
  unfold NREG.ge in *.
  specialize (GE r). rewrite H in GE.
  destruct (NREG.get r nr) eqn:Heqe; ss; tryfalse; eauto.
  inv GE; ss.
Qed.

Lemma ge_sem_live_loc
      inj tview_tgt tview_src nm nm'
      (LIVE_LOC: sem_live_loc inj tview_tgt tview_src nm)
      (GE: nmem_ge nm nm'):
  sem_live_loc inj tview_tgt tview_src nm'.
Proof.
  unfold sem_live_loc in *; ss.
  ii. unfold nmem_ge in GE. destruct nm, nm'; ss.
  destruct (LocSet.mem loc locs0) eqn:LOCS; ss.
  destruct (LocSet.mem loc locs) eqn:LOCS'; ss.
  unfold LocSet.Subset in *.
  eapply LocSet.Facts.mem_2 in LOCS'.
  eapply GE in LOCS'.
  eapply LocSet.Facts.mem_1 in LOCS'.
  rewrite LOCS in LOCS'. ss.
  exploit LIVE_LOC; eauto. rewrite LOCS'. ss.
Qed.

Lemma ge_ai_interp_prsv
      ai ai'
      inj R_tgt tview_tgt R_src tview_src
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src ai)
      (GE: LvLat.ge ai ai'):
  ai_interp inj R_tgt tview_tgt R_src tview_src ai'.
Proof.
  destruct ai, ai'; ss.
  des. inv GE; ss.
  splits.
  eapply ge_sem_live_reg; eauto.
  eapply ge_sem_live_loc; eauto.
Qed.

Lemma ai_interp_write_fence
      inj R_tgt tview_tgt sc_tgt R_src tview_src sc_src nr nm ow
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (nr, nm))
      (ORD: ow <> Ordering.seqcst):
  ai_interp inj
            R_tgt (TView.write_fence_tview tview_tgt sc_tgt ow)
            R_src (TView.write_fence_tview tview_src sc_src ow)
            (nr, nm).
Proof.
  unfold ai_interp in *. des.
  econs; eauto.
  rewrite write_fence_tview_not_sc; eauto.
  unfold sem_live_loc in *; ss.
  assert (Ordering.le Ordering.seqcst ow = false).
  {
    destruct ow; ss.
  }
  repeat (rewrite H). ii.
  unfold View.bot; ss.
  unfold TimeMap.join, TimeMap.bot; ss.
  repeat (rewrite Time_join_bot; ss).
  exploit AI_INTERP0; eauto.
Qed.

Lemma ai_interp_read_fence
      inj R_tgt tview_tgt R_src tview_src nr nm or
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (nr, nm)):
  ai_interp inj
            R_tgt (TView.read_fence_tview tview_tgt or)
            R_src (TView.read_fence_tview tview_src or)
            (nr, nm).
Proof.
  unfold ai_interp in *. des. split; eauto.
  unfold TView.read_fence_tview, sem_live_loc in *; ss.
  des_if; eauto. ii.
  exploit AI_INTERP0; eauto. ii; clear AI_INTERP0. des.
  splits; eauto.
Qed.

Lemma ViewInj_implies_ai_interp
      R_tgt tview_tgt R_src tview_src inj nr nm
      (SEM_REG: sem_live_reg R_tgt R_src nr)
      (VIEW_INJ_CUR: ViewInj inj (TView.cur tview_tgt) (TView.cur tview_src))
      (VIEW_INJ_ACQ: ViewInj inj (TView.acq tview_tgt) (TView.acq tview_src))
      (CLOSED_TVIEW_INJ: closed_tviewInj inj tview_tgt):
  ai_interp inj R_tgt tview_tgt R_src tview_src (nr, nm).
Proof.
  unfold ai_interp. split; eauto.
  unfold ViewInj in *. destruct tview_tgt, tview_src; ss.
  destruct cur, cur0; ss. destruct acq, acq0; ss. des.
  unfold closed_tviewInj in *; ss. des.
  unfold closed_viewInj in *; ss. des.
  unfold TMapInj in *; ss.
  econs; try splits; ss.
  unfold closed_TMapInj in CLOSED_TVIEW_INJ0.
  specialize (CLOSED_TVIEW_INJ0 loc). des. exploit VIEW_INJ_CUR; eauto. ii; subst; eauto.
  unfold closed_TMapInj in CLOSED_TVIEW_INJ1.
  specialize (CLOSED_TVIEW_INJ1 loc). des. exploit VIEW_INJ_ACQ; eauto. ii; subst; eauto.
  unfold closed_TMapInj in CLOSED_TVIEW_INJ3.
  specialize (CLOSED_TVIEW_INJ3 loc). des. exploit VIEW_INJ_CUR0; eauto. ii; subst; eauto.
  unfold closed_TMapInj in CLOSED_TVIEW_INJ2.
  specialize (CLOSED_TVIEW_INJ2 loc). des. exploit VIEW_INJ_ACQ0; eauto. ii; subst; eauto.
Qed.

Lemma ai_interp_scfence_prsv
      R_tgt tview_tgt sc_tgt R_src tview_src sc_src inj nr nm
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (nr, NMem LocSet.empty))
      (CLOSED_TVIEW_INJ: closed_tviewInj inj tview_tgt)
      (CLOSED_SC_INJ: closed_TMapInj inj sc_tgt)
      (SC_INJ: TMapInj inj sc_tgt sc_src)
      (MON_INJ: monotonic_inj inj):
  ai_interp inj R_tgt (TView.write_fence_tview tview_tgt sc_tgt Ordering.seqcst)
            R_src (TView.write_fence_tview tview_src sc_src Ordering.seqcst)
            (nr, nm).
Proof.
  unfold ai_interp in AI_INTERP. des. 
  exploit sem_live_loc_all; eauto. i.
  exploit sem_live_loc_all'; eauto. i.
  assert (SEQ_SC: Ordering.le Ordering.seqcst Ordering.seqcst). eauto.
  unfold ViewInj in x0, x1.
  destruct tview_tgt, tview_src; ss.
  destruct cur, cur0; ss. des.
  destruct acq, acq0; ss. des.
  unfold closed_tviewInj in CLOSED_TVIEW_INJ. ss. des.
  unfold closed_viewInj in *; ss. des.
  eapply ViewInj_implies_ai_interp; eauto; ss.
  - rewrite SEQ_SC. unfold TView.write_fence_sc.
    rewrite SEQ_SC. ss.
    split.
    eapply Montonic_TMapInj_join; eauto.
    eapply Montonic_TMapInj_join; eauto.
  - repeat (rewrite SEQ_SC); ss.
    unfold TView.write_fence_sc; ss.
    repeat (rewrite SEQ_SC); ss.
    split.
    eapply Montonic_TMapInj_join; eauto.
    eapply closed_TMapInj_join; eauto.
    eapply Montonic_TMapInj_join; eauto.
    eapply Montonic_TMapInj_join; eauto.
    eapply closed_TMapInj_join; eauto.
    eapply Montonic_TMapInj_join; eauto.
  - unfold TView.write_fence_tview; ss.
    repeat (rewrite SEQ_SC); ss.
    unfold TView.write_fence_sc; ss.
    repeat (rewrite SEQ_SC); ss.
    econs; eauto; ss.
    ii.
    assert (Ordering.le Ordering.acqrel Ordering.seqcst). eauto.
    rewrite H.
    unfold closed_viewInj; ss. split.
    eapply closed_TMapInj_join; eauto.
    eapply closed_TMapInj_join; eauto.
    split.
    unfold closed_viewInj; ss. split.
    eapply closed_TMapInj_join; eauto.
    eapply closed_TMapInj_join; eauto.
    unfold closed_viewInj; ss. split.
    eapply closed_TMapInj_join; eauto.
    eapply closed_TMapInj_join; eauto.
    eapply closed_TMapInj_join; eauto.
    eapply closed_TMapInj_join; eauto.
Qed.

Lemma ai_interp_set_expr_live
      inj R_tgt tview_tgt R_src tview_src e nr nm
      (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src (set_expr_live e nr, nm)):
  ai_interp inj R_tgt tview_tgt R_src tview_src (nr, nm).
Proof.
  unfold ai_interp in *. des.
  split; eauto.
  eapply sem_live_reg_less; eauto.
Qed.
  
(** * DCE specific lemmas *)
Lemma InvView_dce_na_loc
      lo loc inj tview_tgt tview_src mem_src
      (NA_LOC: lo loc = Ordering.nonatomic)
      (INV_VIEW: InvView_dce inj lo tview_tgt tview_src mem_src):
  <<NA_CUR_RLX: TM inj loc (View.rlx (TView.cur tview_tgt)) (View.rlx (TView.cur tview_src)) mem_src>> /\
  <<NA_ACQ_RLX: TM inj loc (View.rlx (TView.acq tview_tgt)) (View.rlx (TView.acq tview_src)) mem_src>>.
Proof.
  inv INV_VIEW; ss. splits; eauto.
Qed.

Lemma I_dce_add_src_concrete_prsv
      lo inj sc_tgt mem_tgt sc_src mem_src mem_src'
      loc from to val R to'
      (INV: I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (ADD: Memory.add mem_src loc from to (Message.concrete val R) mem_src')
      (LT: Time.lt to to')
      (ITV: forall ts, Interval.mem (to, to') ts -> ~ Cover.covered loc ts mem_src')
      (CLOSED_SRC_MEM: Memory.closed mem_src'):
  I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src').
Proof.
  inv INV. des; ss; eauto.
  splits; eauto.
  eapply MsgInj_add_src_concrete_prsv; eauto.

  ii.
  destruct (Loc.eq_dec loc loc0); subst.
  {
    erewrite Memory.add_o in H0; eauto. des_ifH H0; ss; des; subst; ss.
    inv INJ_MEM. exploit COMPLETE; eauto. ii; des.
    exploit SOUND; eauto. ii; des. rewrite H1 in x0. inv x0.
    eapply Memory.add_get0 in ADD; eauto. des. rewrite GET in x2. ss.

    destruct (Time.le_lt_dec to to'0); subst.
    {
      eapply Time.le_lteq in l. des; subst; ss.
      exploit Memory.add_get0; eauto. ii; des.
      lets GET_RSV: H0.
      eapply Memory.add_get1 in H0; eauto.
      exploit Memory_get_disj_proper; [ | | eapply l | eauto..]; eauto.
      ii.  
      eapply Time.le_lteq in x0. des; subst.
      {
        eapply TS_RSV in GET_RSV; eauto. des.
        exists (Time.join to_r to). split.
        eapply lt_lt_join; eauto.
        introv ITV''.
        assert (ITV_origin: Interval.mem (to_r, from') ts).
        {
          inv ITV''; ss. econs; ss; eauto.
          cut (Time.le to_r (Time.join to_r to)). ii.
          auto_solve_time_rel. eapply Time.join_l.
        }
        introv COVER. eapply GET_RSV0 in ITV_origin. contradiction ITV_origin. clear ITV_origin.
        clear - ITV'' COVER ADD. inv COVER.
        erewrite Memory.add_o in GET; eauto.
        des_ifH GET; ss; eauto.
        2: { econs; eauto. }
        des; subst. inv GET. inv ITV''; ss. inv ITV; ss.
        clear - FROM TO0. eapply Time_lt_join in FROM. des.
        auto_solve_time_rel.
      }
      {
        (* contradiction *)
        clear - ITV H0 GET0 LT l.
        destruct (Time.le_lt_dec to' to'0); subst.
        {
          specialize (ITV to'). exploit ITV; eauto.
          econs; ss; eauto. eapply Time.le_lteq. eauto.
          econs. eapply H0. econs; eauto. ii; ss.
        }
        {
          specialize (ITV to'0). exploit ITV; eauto.
          econs; eauto; ss. eapply Time.le_lteq; eauto.
          econs. eapply H0. econs; ss; eauto. eapply Time.le_lteq; eauto.
          ii; ss.
        }
      }
    }
    {
      exploit TS_RSV; eauto. ii; des.
      exists to_r. split; eauto. 
      introv ITV''. introv COVER'.
      lets COVER: ITV''. eapply x0 in COVER. contradiction COVER. clear COVER.
      inv COVER'. erewrite Memory.add_o in GET; eauto. des_ifH GET; ss.
      {
        eapply Memory.add_get1 in H0; eauto.
        des; subst. inv GET.
        exploit Memory.add_get0; eauto. ii; des. 
        exploit Memory_get_disj_proper; [ | | eapply l | eauto..]; eauto. introv LE.
        clear - ITV'' ITV0 LE H0. inv ITV''; ss. inv ITV0; ss.
        eapply memory_get_ts_le in H0.
        clear - LE TO FROM0 H0.
        cut (Time.le from' from0). ii. clear H0 LE.
        cut (Time.le ts from0). ii. auto_solve_time_rel.
        auto_solve_time_rel.
        clear - H0 LE. auto_solve_time_rel.
      }
      {
        econs; eauto.
      }
    }
  }
  {
    erewrite Memory.add_o in H0; eauto. des_ifH H0; eauto; ss.
    des; subst; ss.
    exploit TS_RSV; eauto. clear o. ii; des.
    exists to_r. split; eauto.
    introv ITV' COVER'. exploit x0; eauto.
    eapply Cover.add_covered in COVER'; eauto. des; eauto; subst; ss.
  }

  introv GET_RSV.
  erewrite Memory.add_o in GET_RSV; eauto.
  des_ifH GET_RSV; eauto. ss.
Qed.

Lemma tm_loc_eq_TM_prsv
      tm tm' tm'' loc mem inj
      (TM_LOC: tm' loc = tm'' loc)
      (TM_H: TM inj loc tm tm' mem):
  TM inj loc tm tm'' mem.
Proof.
  unfold TM in *; ss. des.
  split; eauto.
  rewrite <- TM_LOC; eauto.
  rewrite <- TM_LOC; eauto.
Qed. 

Lemma mem_write_disj_loc_TM_prsv
      inj loc0 tm tm' prom mem prom' mem' loc from to val R kind
      (TM_H: TM inj loc0 tm tm' mem)
      (WRITE: Memory.write prom mem loc from to val R prom' mem' kind)
      (DISJ_LOC: loc <> loc0):
  TM inj loc0 tm tm' mem'.
Proof.
  exploit Memory_write_disj_loc_stable; eauto. 
  ii; des; eauto.
  inv TM_H. econs; eauto.
  des. exists to'. splits; eauto.
  ii. eapply H2 in H3. inv H3.
  econs; eauto.
  unfold Memory.get in *. rewrite <- x1; eauto.
Qed.

Lemma inj_tm_join_prsv
      tm tm' tm0 tm0' mem inj loc
      (CLOSED_TM: closed_TMapInj inj tm0)
      (TM_INJ: TMapInj inj tm0 tm0')
      (TM_H: TM inj loc tm tm' mem)
      (MONOTONIC_INJ: monotonic_inj inj):
  TM inj loc (TimeMap.join tm tm0) (TimeMap.join tm' tm0') mem.
Proof.
  inv TM_H. des.
  econs; eauto.
  - ii. unfold TimeMap.join in *.
    rewrite Time.join_comm in H4.
    rewrite Time.join_comm.
    unfold Time.join in H4.
    des_ifH H4.
    {
      assert (LE: Time.le (tm0' loc) (tm' loc)).
      {
        exploit monotonic_inj_implies_le_prsv; [ | eapply l | eauto..]; eauto.
        instantiate (1 := (tm0' loc)).
        clear - CLOSED_TM TM_INJ.
        eapply TMapInj_lower; eauto.
        ii. auto_solve_time_rel.
      }
      unfold Time.join. des_if; eauto.
      auto_solve_time_rel.
    }
    {
      assert (Time.lt (tm' loc) (tm0' loc)).
      {
        eapply H in l; eauto.
        eapply TMapInj_lower; eauto.
      }
      unfold Time.join. des_if; eauto.
      auto_solve_time_rel.
      eapply MONOTONIC_INJ. eapply H4. 2: eauto.
      eapply TMapInj_lower; eauto.
    }
  - unfold TimeMap.join.
    rewrite Time.join_comm.
    unfold Time.join at 1.
    des_if.
    {
      assert (LE: Time.le (tm0' loc) (tm' loc)).
      {
        exploit monotonic_inj_implies_le_prsv; [ | eapply l | eauto..]; eauto.
        instantiate (1 := (tm0' loc)).
        clear - CLOSED_TM TM_INJ.
        eapply TMapInj_lower; eauto.
        ii. auto_solve_time_rel.
      }
      exists to'. split; eauto.
      rewrite TimeFacts.le_join_l; eauto.
    }
    {
      assert (Time.lt (tm' loc) (tm0' loc)).
      {
        eapply H in l; eauto.
        eapply TMapInj_lower; eauto.
      }
      exists (tm0' loc). split.
      eapply TMapInj_lower; eauto.
      rewrite TimeFacts.le_join_r; eauto.
      split; eauto. eapply Time.le_lteq; eauto.
      introv ITV. inv ITV; ss. auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
    }
Qed.

Lemma inj_tm_join_singleton_prsv
      tm tm' to to' loc loc0 inj mem
      (INJ_TO: inj loc to = Some to')
      (TM_H: TM inj loc0 tm tm' mem)
      (MONOTONIC_INJ: monotonic_inj inj):
  TM inj loc0 (TimeMap.join tm (TimeMap.singleton loc to))
     (TimeMap.join tm' (TimeMap.singleton loc to')) mem.
Proof.
  inv TM_H. des.
  unfold TimeMap.singleton.
  econs; eauto.
  - destruct (Loc.eq_dec loc loc0); subst. ii.
    
    unfold TimeMap.join in *.
    repeat (rewrite Loc_add_eq in *; eauto).
    rewrite Time.join_comm in H4.
    unfold Time.join in H4.
    des_ifH H4; eauto.
    {
      assert (LE: Time.le to' (tm' loc0)).
      {
        exploit monotonic_inj_implies_le_prsv; [ | eapply l | eauto..]; eauto.
        ii. auto_solve_time_rel.
      }
      rewrite TimeFacts.le_join_l; eauto.
    }
    {
      assert (Time.lt (tm' loc0) to').
      {
        eapply H in l; eauto.
      }
      rewrite TimeFacts.le_join_r; eauto.
      eapply Time.le_lteq; eauto.
    }

    ii. unfold TimeMap.join in *.
    repeat (rewrite Loc_add_neq in *; eauto).
    unfold LocFun.init in *; ss.
    repeat (rewrite Time_join_bot in *). eauto.
  - unfold TimeMap.join.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq in *; eauto).
    rewrite Time.join_comm. unfold Time.join at 1.
    des_if.
    {
      assert (LE: Time.le to' (tm' loc0)).
      {
        exploit monotonic_inj_implies_le_prsv; [ | eapply l | eauto..]; eauto.
        ii. auto_solve_time_rel.
      }
      rewrite TimeFacts.le_join_l; eauto.
    }
    {
      assert (Time.lt (tm' loc0) to').
      {
        eapply H in l; eauto.
      }
      exists to'. split; eauto. 
      rewrite TimeFacts.le_join_r; eauto.
      split. eapply Time.le_lteq; eauto.
      introv ITV. inv ITV; ss. auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
    }

    repeat (rewrite Loc_add_neq in *; eauto).
    unfold LocFun.init.
    repeat (rewrite Time_join_bot in *). eauto.
Qed.
    
Lemma TM_I_dce_to_write
      inj loc tview_tgt tview_src mem_src lo
      sc_tgt mem_tgt sc_src prm_src val
      (TM_H: TM inj loc (View.rlx (TView.cur tview_tgt)) (View.rlx (TView.cur tview_src)) mem_src)
      (INV: I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (LOC: lo loc = Ordering.nonatomic)
      (TGT_TVIEW_CLOSED: TView.closed tview_tgt mem_tgt)
      (SRC_TVIEW_CLOSED: TView.closed tview_src mem_src)
      (PRM_LESS_SRC: Memory.le prm_src mem_src):
  exists mem_src' from to,
    <<LOCAL_WRITE: Local.write_step (Local.mk tview_src prm_src) sc_src mem_src loc from to val
                                    None None Ordering.plain
                                    (Local.mk (TView.write_tview tview_src sc_src loc to Ordering.plain) prm_src)
                                    sc_src mem_src' Memory.op_kind_add lo>> /\
    <<TM_H': TM inj loc (View.rlx (TView.cur tview_tgt))
                (View.rlx (TView.cur (TView.write_tview tview_src sc_src loc to Ordering.plain))) mem_src'>> /\
    <<INV': I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src')>>.
Proof.
  inv TM_H. des. 
  inv INV. renames H3 to SC_MAP_INJ. des.
  (* target current view message *)
  assert (TGT_CUR_MSG: exists val R from, Memory.get loc (View.rlx (TView.cur tview_tgt) loc) mem_tgt
                                     = Some (from, Message.concrete val R)).
  {
    clear - TGT_TVIEW_CLOSED.
    inv TGT_TVIEW_CLOSED. inv CUR. unfold Memory.closed_timemap in RLX.
    specialize (RLX loc). des. eauto.
  }
  des.
  (* source current view message *)
  assert (SRC_CUR_MSG: exists val_s R_s f_s, Memory.get loc (View.rlx (TView.cur tview_src) loc) mem_src
                                        = Some (f_s, Message.concrete val_s R_s)).
  {
    clear - SRC_TVIEW_CLOSED. inv SRC_TVIEW_CLOSED. inv CUR.
    unfold Memory.closed_timemap in RLX.
    specialize (RLX loc). des. eauto.
  }
  des. 
  (* we discuss whether the target thread view the largest message *)
  destruct (classic (exists to from val R, Memory.get loc to mem_tgt = Some (from, Message.concrete val R) /\
                                      Time.lt (View.rlx (TView.cur tview_tgt) loc) to)).
  {
    (* not the last, find the next one *)
    des.
    exploit next_concrete_ext_loc0; eauto. instantiate (1 := View.rlx (TView.cur tview_tgt) loc).
    instantiate (1 := mem_tgt). instantiate (1 := loc). 
    introv MEM_NXT_GET. destruct MEM_NXT_GET.
    {
      (* next target exists *)
      des.
      (* getting the next source injection message *) 
      assert (exists f0' R0' nxt_ts' to_r,
                 <<SRC_NXT: Memory.get loc nxt_ts' mem_src = Some (f0', Message.concrete val2 R0')>> /\
                 <<INJ: inj loc nxt_ts = Some nxt_ts'>> /\
                 <<ITV: Time.lt to_r f0'>> /\
                 <<ITV_NOTCOVER: forall ts, Interval.mem (to_r, f0') ts -> ~ Cover.covered loc ts mem_src>>).
      {
        clear - H6 INJ_MEM TS_RSV H5 LOC. lets GET: H6. inv INJ_MEM.
        eapply SOUND in H6; eauto. des.
        exploit TS_RSV; [eapply H1 | eapply H6 | eauto..].
        eapply Memory.get_ts in GET. des; subst; eauto.
        auto_solve_time_rel.
        cut (Time.le Time.bot (View.rlx (TView.cur tview_tgt) loc)). ii. auto_solve_time_rel.
        eapply Time.bot_spec.
        ii; des.
        do 4 eexists.
        split. eauto. split. eauto. split; eauto.
      }
      des.
      (* find the first unused intervals *)
      exploit find_first_unused_timestamps; [eapply SRC_CUR_MSG | eapply SRC_NXT | eauto..].
      {
        clear - NO_RSVs LOC. introv GET. eapply NO_RSVs in GET; eauto.
        rewrite LOC in GET. ss.
      }
      ii; des.

      (* Memory add *) 
      assert (MEM_ADD: exists mem_src', Memory.write prm_src mem_src loc to1 (Time.middle to1 to2) val
                                                None prm_src mem_src' Memory.op_kind_add).
      {
        eapply write_succeed_valid; eauto; ss.
  
        clear - RSV_ITV RSV. introv COVER ITV.
        specialize (RSV_ITV t). eapply RSV_ITV in COVER; eauto.
        inv ITV; ss. econs; ss; eauto.
        cut (Time.le (Time.middle to1 to2) to2). ii. auto_solve_time_rel.
        eapply Time.le_lteq. left. eapply Time.middle_spec in RSV. des; eauto.

        unfold TimeMap.bot. eapply Time.bot_spec.

        eapply Time.middle_spec in RSV. des. eauto.

        introv ATTACH_TIME.
        eapply RSV_ITV_insert_middle_not_attach in ATTACH_TIME; eauto.

        econs. eauto.
      }
      des.

      exists mem_src' to1 (Time.middle to1 to2).
      split. econs; eauto.
      {
        rewrite LOC. ss.
      }
      { 
        ss. econs. clear - RSV IS_LAST.
        eapply Time.middle_spec in RSV. des.
        auto_solve_time_rel.
      }
      ii; ss.

      split.
      econs.
      {
        introv INJ' LT'. 
        assert (GE_NXT: Time.le nxt_ts to0).
        {
          clear - H6 H7 INJ' LT' INJ_MEM. inv INJ_MEM.
          exploit COMPLETE; eauto. ii; des.
          destruct (Time.le_lt_dec nxt_ts to0); eauto.
          eapply H7 in x; eauto. des.
          auto_solve_time_rel. auto_solve_time_rel. ii. auto_solve_time_rel.
          ii; subst. auto_solve_time_rel.
        }
        assert (GE_NXT': Time.le nxt_ts' to'0).
        {
          clear - INJ' INJ GE_NXT INJ_MEM. inv INJ_MEM. clear SOUND COMPLETE.
          exploit monotonic_inj_implies_le_prsv;
            [eapply MONOTONIC | eapply GE_NXT | eapply INJ | eapply INJ' | eauto..].
        }

        unfold TView.write_tview; ss. unfold TimeMap.singleton.
        unfold TimeMap.join. rewrite Loc_add_eq.
        cut (Time.lt (Time.middle to1 to2) to'0). introv LT''.
        eapply lt_lt_join; eauto.
        clear - LE_NXT SRC_NXT GE_NXT' RSV. eapply Time.middle_spec in RSV. des.
        eapply memory_get_ts_le in SRC_NXT. 
        cut (Time.le to2 nxt_ts'). introv LE0. clear - RSV0 LE0 GE_NXT'.
        cut (Time.le to2 to'0). introv LE1. auto_solve_time_rel.
        auto_solve_time_rel.
        clear - SRC_NXT LE_NXT. auto_solve_time_rel.
      }
      { 
        exists to'. split; eauto.
        split. clear - H1. unfold TView.write_tview; ss.
        unfold TimeMap.singleton, TimeMap.join. rewrite Loc_add_eq.
        eapply le_join; eauto.
        introv ITV'. unfold TView.write_tview in ITV'; ss.
        unfold TimeMap.join, TimeMap.singleton in ITV'. rewrite Loc_add_eq in ITV'.  
        eapply concrete_cover_prsv with (from := to') (mem' := mem_src').
        Focus 2. inv MEM_ADD. inv PROMISE; eauto.
        introv ITV''.
  
        exploit concrete_covered_merge; [eapply H2 | eapply CONCRETE_COVER | eauto..].
        assert (LT': Time.lt (View.rlx (TView.cur tview_src) loc) (Time.middle to1 to2)).
        {
          clear - RSV IS_LAST.
          eapply Time.middle_spec in RSV. des.
          auto_solve_time_rel.
        }  
        erewrite TimeFacts.le_join_r in ITV'; eauto.
        eapply Time.le_lteq. eauto.
      }

      (* I_dce preservation *)
      assert (RSV_ITV': forall ts, Interval.mem (Time.middle to1 to2, to2) ts -> ~ Cover.covered loc ts mem_src').
      { 
        clear - RSV_ITV MEM_ADD RSV. inv MEM_ADD. inv PROMISE; ss.
        clear REMOVE PROMISES TS ATTACH.
        introv ITV.
        cut (Interval.mem (to1, to2) ts). introv ITV'.
        lets COVER: ITV'. eapply RSV_ITV in COVER. introv COVER'.
        contradiction COVER. clear COVER. inv COVER'.
        erewrite Memory.add_o in GET; eauto. des_ifH GET; ss.
        des; subst. inv GET. inv ITV; ss. inv ITV'; ss. inv ITV0; ss.
        clear - FROM TO1. auto_solve_time_rel.
        des; ss. econs; eauto.
        inv ITV; ss. econs; eauto; ss.
        eapply Time.middle_spec in RSV. des.
        auto_solve_time_rel.
      }
      inv MEM_ADD. inv PROMISE.
      eapply I_dce_add_src_concrete_prsv; eauto.
      {
        econs; eauto.
      }
      {
        eapply Time.middle_spec in RSV. des; eauto.
      }
      {
        eapply Memory.add_closed; eauto.
      }
    }
    {
      (* next target not exist: contradiction *)
      eapply H5 in H3; eauto. auto_solve_time_rel.
    }
  }
  {
    (* last concrete *) 
    exploit find_first_unused_timestamps_general; [eapply SRC_CUR_MSG | eauto..].
    {
      introv GET_RSV. eapply NO_RSVs in GET_RSV. rewrite LOC in GET_RSV. ss.
    }
    ii. des.

    (* Memory add *) 
    assert (MEM_ADD: exists mem_src', Memory.write prm_src mem_src loc to1 (Time.middle to1 to2) val
                                              None prm_src mem_src' Memory.op_kind_add).
    {
      eapply write_succeed_valid; eauto; ss.
      
      clear - RSV_ITV RSV. introv COVER ITV.
      specialize (RSV_ITV t). eapply RSV_ITV in COVER; eauto.
      inv ITV; ss. econs; ss; eauto.
      cut (Time.le (Time.middle to1 to2) to2). ii. auto_solve_time_rel.
      eapply Time.le_lteq. left. eapply Time.middle_spec in RSV. des; eauto.

      unfold TimeMap.bot. eapply Time.bot_spec.

      eapply Time.middle_spec in RSV. des. eauto.

      introv ATTACH_TIME.
      eapply RSV_ITV_insert_middle_not_attach in ATTACH_TIME; eauto.

      econs. eauto.
    }
    des.

    exists mem_src' to1 (Time.middle to1 to2).
    split.
    {
      econs; eauto. rewrite LOC. ss.

      ss. econs. clear - RSV IS_LAST.
      eapply Time.middle_spec in RSV. des.
      auto_solve_time_rel.

      ii; ss.
    }
    {
      split.
      econs; eauto.
      {
        (* contradiction *)
        introv INJ' LT.
        clear - INJ' LT TGT_CUR_MSG H3 INJ_MEM. inv INJ_MEM.
        eapply COMPLETE in INJ'; eauto. des.
        contradiction H3; eauto.
        do 4 eexists. split; eauto.
      }
      { 
        exists to'. split; eauto.

        split.
        unfold TView.write_tview; ss.
        unfold TimeMap.join, TimeMap.singleton; ss. rewrite Loc_add_eq.
        eapply le_join; eauto.

        unfold TView.write_tview; ss.
        unfold TimeMap.join, TimeMap.singleton; ss. rewrite Loc_add_eq.
        introv ITV'.
        eapply concrete_cover_prsv with (from := to') (mem' := mem_src').
        Focus 2. inv MEM_ADD. inv PROMISE; eauto.
        introv ITV''.
        exploit concrete_covered_merge; [eapply H2 | eapply CONCRETE_COVER | eauto..].
        assert (LT': Time.lt (View.rlx (TView.cur tview_src) loc) (Time.middle to1 to2)).
        {
          clear - RSV IS_LAST.
          eapply Time.middle_spec in RSV. des.
          auto_solve_time_rel.
        }
        erewrite TimeFacts.le_join_r in ITV'; eauto.
        eapply Time.le_lteq. eauto.
      }

      (* I_dce preservation *)
      assert (RSV_ITV': forall ts, Interval.mem (Time.middle to1 to2, to2) ts -> ~ Cover.covered loc ts mem_src').
      { 
        clear - RSV_ITV MEM_ADD RSV. inv MEM_ADD. inv PROMISE; ss.
        clear REMOVE PROMISES TS ATTACH.
        introv ITV.
        cut (Interval.mem (to1, to2) ts). introv ITV'.
        lets COVER: ITV'. eapply RSV_ITV in COVER. introv COVER'.
        contradiction COVER. clear COVER. inv COVER'.
        erewrite Memory.add_o in GET; eauto. des_ifH GET; ss.
        des; subst. inv GET. inv ITV; ss. inv ITV'; ss. inv ITV0; ss.
        clear - FROM TO1. auto_solve_time_rel.
        des; ss. econs; eauto.
        inv ITV; ss. econs; eauto; ss.
        eapply Time.middle_spec in RSV. des.
        auto_solve_time_rel.
      }
      inv MEM_ADD. inv PROMISE.
      eapply I_dce_add_src_concrete_prsv; eauto.
      {
        econs; eauto.
      }
      {
        eapply Time.middle_spec in RSV. des; eauto.
      }
      {
        eapply Memory.add_closed; eauto.
      }
    }
  }
Qed. 

Lemma TM_I_dce_cur_acq_to_write
      inj loc tview_tgt tview_src mem_src lo
      sc_tgt mem_tgt sc_src prm_src val
      (TM_H_CUR: TM inj loc (View.rlx (TView.cur tview_tgt)) (View.rlx (TView.cur tview_src)) mem_src)
      (TM_H_ACQ: TM inj loc (View.rlx (TView.acq tview_tgt)) (View.rlx (TView.acq tview_src)) mem_src)
      (INV: I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (LOC: lo loc = Ordering.nonatomic)
      (TGT_TVIEW_CLOSED: TView.closed tview_tgt mem_tgt)
      (SRC_TVIEW_CLOSED: TView.closed tview_src mem_src)
      (PRM_LESS_SRC: Memory.le prm_src mem_src)
      (CUR_ACQ: cur_acq lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                        (TView.cur tview_src) (TView.acq tview_src))
      (CUR_ACQ_PLN: cur_acq_pln lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                                (TView.cur tview_src) (TView.acq tview_src)):
  exists mem_src' from to,
    <<LOCAL_WRITE: Local.write_step (Local.mk tview_src prm_src) sc_src mem_src loc from to val
                                    None None Ordering.plain
                                    (Local.mk (TView.write_tview tview_src sc_src loc to Ordering.plain) prm_src)
                                    sc_src mem_src' Memory.op_kind_add lo>> /\
    <<TM_H_CUR': TM inj loc (View.rlx (TView.cur tview_tgt))
                    (View.rlx (TView.cur (TView.write_tview tview_src sc_src loc to Ordering.plain))) mem_src'>> /\ 
    <<TM_H_ACQ': TM inj loc (View.rlx (TView.acq tview_tgt))
                    (View.rlx (TView.acq (TView.write_tview tview_src sc_src loc to Ordering.plain))) mem_src'>> /\
    <<CUR_ACQ': cur_acq lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                        (TView.cur (TView.write_tview tview_src sc_src loc to Ordering.plain))
                        (TView.acq (TView.write_tview tview_src sc_src loc to Ordering.plain))>> /\
    <<CUR_ACQ': cur_acq_pln lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                            (TView.cur (TView.write_tview tview_src sc_src loc to Ordering.plain))
                            (TView.acq (TView.write_tview tview_src sc_src loc to Ordering.plain))>> /\
    <<INV': I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src')>>.
Proof.
  exploit TM_I_dce_to_write; eauto.
  instantiate (1 := val). ii; des.
  exists mem_src' from to. split; eauto. split; eauto.
  unfold cur_acq in CUR_ACQ. lets CUR_ACQ': CUR_ACQ. 
  specialize (CUR_ACQ loc).
  exploit CUR_ACQ; eauto. clear CUR_ACQ. ii; des.
  - inv TM_H'; ss.
    unfold TimeMap.join, TimeMap.singleton in *; ss. try rewrite Loc_add_eq in *.
    assert (TO_LT_ACQ: Time.lt to (View.rlx (TView.acq tview_src) loc)).
    {
      clear H0. eapply H in LT0; eauto.
      eapply Time_lt_join in LT0; eauto. des; eauto.
    } 
    splits. 
    {
      econs; try rewrite Loc_add_eq; eauto.
      {
        introv INJ LT'.
        rewrite TimeFacts.le_join_l; eauto. 2: eapply Time.le_lteq; eauto.
        inv TM_H_ACQ; ss. des. rewrite LT0 in H2. inv H2. eauto.
      }
      {
        rewrite TimeFacts.le_join_l; eauto. 2: eapply Time.le_lteq; eauto.
        inv TM_H_ACQ; ss. des. rewrite LT0 in H2. inv H2.
        eexists. split. eauto. split. eauto.
        introv ITV. eapply H4 in ITV.
        eapply concrete_covered_concrete_mem_incr_prsv; eauto.
        clear - LOCAL_WRITE. inv LOCAL_WRITE; ss. inv LC2; ss. inv WRITE; ss.
        inv PROMISE; ss.
        eapply memory_add_concrete_mem_incr; eauto.
      }
    }
    {
      unfold cur_acq. introv LOC0.
      specialize (CUR_ACQ' loc0). exploit CUR_ACQ'; eauto. ii; des.
      {
        left. split; eauto.
        unfold View.join, View.singleton_ur; ss.
        unfold TimeMap.join, TimeMap.singleton; ss.

        destruct (Loc.eq_dec loc loc0); subst.
        {
          rewrite Loc_add_eq.
          rewrite TimeFacts.le_join_l; eauto. eapply Time.le_lteq; eauto.
        }
        {
          rewrite Loc_add_neq; eauto; ss.
          unfold LocFun.init; ss. rewrite Time_join_bot; eauto.
        }
      }
      {
        right.
        split; eauto.
        unfold View.join, View.singleton_ur; ss.
        unfold TimeMap.join, TimeMap.singleton; ss.
        destruct (Loc.eq_dec loc loc0); subst.
        {
          rewrite Loc_add_eq.
          rewrite EQ0; eauto.
        }
        {
          rewrite Loc_add_neq; eauto. unfold LocFun.init; ss.
          rewrite TimeFacts.le_join_l.
          rewrite TimeFacts.le_join_l. eauto.
          eapply Time.bot_spec. eapply Time.bot_spec.
        }
      }
    } 
    {
      unfold cur_acq_pln in *; ss. introv LOC0.
      destruct (Time.le_lt_dec (View.pln (TView.acq tview_tgt) loc0) (View.rlx (TView.cur tview_tgt) loc0)).
      {
        right. split; eauto.
        specialize (CUR_ACQ_PLN loc0). exploit CUR_ACQ_PLN; eauto. ii; des.
        clear - l LT1. auto_solve_time_rel.
        unfold TimeMap.join, TimeMap.singleton.
        eapply time_join_mon; eauto.
        destruct (Loc.eq_dec loc loc0); subst.
        rewrite Loc_add_eq; eauto. eapply Time.le_lteq; eauto.
        rewrite Loc_add_neq; eauto. unfold LocFun.init. eapply Time.le_lteq; eauto.
      }
      { 
        exploit CUR_ACQ_PLN; eauto. ii; des.
        
        left. split; eauto. unfold TimeMap.join, TimeMap.singleton; ss.
        destruct (Loc.eq_dec loc loc0); subst.
        {
          rewrite Loc_add_eq; eauto. unfold Time.join.
          des_if; eauto. eapply H in LT2; eauto.
          eapply Time_lt_join in LT2. des. clear - LT3 l0. auto_solve_time_rel.
        }
        {
          rewrite Loc_add_neq; eauto. unfold LocFun.init; ss.
          rewrite Time_join_bot; eauto.
        }

        right. split; eauto.
        unfold TimeMap.join.
        eapply time_join_mon; eauto. unfold TimeMap.singleton; eauto.
        destruct (Loc.eq_dec loc loc0); subst.
        rewrite Loc_add_eq; eauto. eapply Time.le_lteq; eauto.
        rewrite Loc_add_neq; eauto. unfold LocFun.init. eapply Time.le_lteq; eauto.
      }
    }
    des; splits; eauto.
  - split.
    inv TM_H'; ss.
    unfold TimeMap.join, TimeMap.singleton in *; ss.
    econs; eauto.
    {
      introv INJ LT.
      rewrite <- EQ0. rewrite <- EQ in LT. eauto.
    }
    {
      rewrite <- EQ0. rewrite <- EQ. eauto.
    }
    split; eauto.
    
    unfold cur_acq. introv LOC0.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      unfold TView.write_tview; ss. unfold TimeMap.join, TimeMap.singleton; ss.
      rewrite Loc_add_eq.
      rewrite <- EQ0. rewrite <- EQ. eauto.
    }
    {
      unfold TView.write_tview; ss. unfold TimeMap.join, TimeMap.singleton; ss.
      rewrite Loc_add_neq; eauto. unfold LocFun.init; ss; eauto.
      rewrite TimeFacts.le_join_l; eauto. rewrite TimeFacts.le_join_l; eauto.
      eapply Time.bot_spec. eapply Time.bot_spec.
    }

    split.
    unfold cur_acq_pln in *. introv LOC0.
    exploit CUR_ACQ_PLN; eauto. ii; des; ss.
    {
      left. split; eauto.
      inv TM_H'. unfold TimeMap.singleton, TimeMap.join.
      destruct (Loc.eq_dec loc loc0); subst.
      {
        rewrite Loc_add_eq; eauto.
        unfold Time.join. des_if; eauto.
        eapply H in LT0; eauto. clear - LT0 l.
        unfold TimeMap.join, TimeMap.singleton in *.
        rewrite Loc_add_eq in LT0. eapply Time_lt_join in LT0. des.
        auto_solve_time_rel.
      }
      {
        rewrite Loc_add_neq; eauto.
        unfold LocFun.init. rewrite Time_join_bot; eauto.
      }
    }
    {
      right. split; eauto.
      unfold TimeMap.join, TimeMap.singleton.
      eapply time_join_mon; eauto.
      destruct (Loc.eq_dec loc loc0); subst.
      rewrite Loc_add_eq; eauto. eapply Time.le_lteq; eauto.
      rewrite Loc_add_neq; eauto. unfold LocFun.init. eapply Time.le_lteq; eauto.
    }
    eauto.
Qed. 

Lemma InvView_dce_read_prsv
      tview_tgt tview_src mem_src loc to R to' R' or inj lo
      (INV_VIEW: InvView_dce inj lo tview_tgt tview_src mem_src)
      (INJ_TO: inj loc to = Some to')
      (VIEW_INJ: opt_ViewInj inj R R')
      (CLOSED_VIEW: closed_opt_viewinj inj R)
      (MONOTONIC_INJ: monotonic_inj inj):
  InvView_dce inj lo (TView.read_tview tview_tgt loc to R or)
              (TView.read_tview tview_src loc to' R' or) mem_src.
Proof.
  inv INV_VIEW.
  econs; eauto. 
  - ii. exploit ATM_LOC_CUR_PLN; eauto. ii; des.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL.
    destruct tview_tgt, tview_src; ss.
    unfold TimeMap.join.
    destruct (Ordering.le Ordering.acqrel or) eqn:LE_ACQREL; ss. 
    unfold View.singleton_ur_if; ss.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    unfold TimeMap.singleton; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq). destruct R, R'; ss.
    repeat (eapply inj_join_comp; eauto). eapply view_inj_prop_pln; eauto.
    unfold TimeMap.bot. repeat (rewrite Time_join_bot).
    repeat (eapply inj_join_comp; eauto).
    repeat (rewrite Loc_add_neq; eauto). unfold LocFun.init; ss. destruct R, R'; ss.
    repeat (rewrite Time_join_bot).
    eapply inj_join_comp; eauto. eapply view_inj_prop_pln; eauto.
    unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).
    destruct or; ss.
    unfold TimeMap.bot; ss. repeat (rewrite Time_join_bot; eauto).
    unfold View.singleton_ur_if.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    unfold TimeMap.singleton.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq). eapply inj_join_comp; eauto.
    repeat (rewrite Loc_add_neq; eauto). unfold LocFun.init; ss.
    repeat (rewrite Time_join_bot; eauto).
    unfold TimeMap.bot; eauto.
    repeat (rewrite Time_join_bot; eauto).
  - ii. exploit ATM_LOC_CUR_RLX; eauto. ii; des.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL.
    destruct tview_tgt, tview_src; ss.
    unfold TimeMap.join.
    destruct (Ordering.le Ordering.acqrel or) eqn:LE_ACQREL; ss. 
    unfold View.singleton_ur_if; ss.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    unfold TimeMap.singleton; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq). destruct R, R'; ss.
    repeat (eapply inj_join_comp; eauto). eapply view_inj_prop_rlx; eauto.
    unfold TimeMap.bot. repeat (rewrite Time_join_bot).
    repeat (eapply inj_join_comp; eauto).
    repeat (rewrite Loc_add_neq; eauto). unfold LocFun.init; ss. destruct R, R'; ss.
    repeat (rewrite Time_join_bot).
    eapply inj_join_comp; eauto. eapply view_inj_prop_rlx; eauto.
    unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).
    destruct or; ss.
    unfold TimeMap.bot; ss. repeat (rewrite Time_join_bot; eauto).
    unfold View.singleton_ur_if.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    unfold TimeMap.singleton.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq). eapply inj_join_comp; eauto.
    repeat (rewrite Loc_add_neq; eauto). unfold LocFun.init; ss.
    repeat (rewrite Time_join_bot; eauto).
    unfold TimeMap.singleton.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq). eapply inj_join_comp; eauto.
    repeat (rewrite Loc_add_neq; eauto). unfold LocFun.init; ss.
    repeat (rewrite Time_join_bot; eauto).
  - ii. exploit NA_LOC_CUR_RLX; eauto. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL.
    destruct tview_tgt, tview_src; ss.
    unfold View.singleton_ur_if; ss.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    destruct (Ordering.le Ordering.acqrel or) eqn:LE_ACQREL; ss.
    destruct R, R'; ss.
    eapply inj_tm_join_prsv; eauto.
    {
      unfold closed_viewInj in *. des; eauto.
    }
    {
      unfold ViewInj in *. destruct t, t0; ss; eauto.
      des; eauto.
    }
    eapply inj_tm_join_singleton_prsv; eauto.
    repeat (rewrite TimeMap.join_bot; eauto).
    eapply inj_tm_join_singleton_prsv; eauto.
    repeat (rewrite TimeMap.join_bot; eauto).
    eapply inj_tm_join_singleton_prsv; eauto.
    destruct (Ordering.le Ordering.acqrel or) eqn:LE_ACQREL; ss.
    destruct R, R'; ss.
    eapply inj_tm_join_prsv; eauto.
    {
      unfold closed_viewInj in *. des; eauto.
    }
    {
      unfold ViewInj in *. destruct t, t0; ss; eauto.
      des; eauto.
    }
    eapply inj_tm_join_singleton_prsv; eauto.
    repeat (rewrite TimeMap.join_bot; eauto).
    eapply inj_tm_join_singleton_prsv; eauto.
    repeat (rewrite TimeMap.join_bot; eauto).
    eapply inj_tm_join_singleton_prsv; eauto. 
  - ii. exploit ATM_LOC_ACQ_PLN; eauto. ii; des. 
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL.
    destruct tview_tgt, tview_src; ss.
    unfold TimeMap.join.
    unfold View.singleton_ur_if; ss.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    unfold TimeMap.singleton; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq). destruct R, R'; ss.
    repeat (eapply inj_join_comp; eauto). eapply view_inj_prop_pln; eauto.
    unfold TimeMap.bot. repeat (rewrite Time_join_bot).
    repeat (eapply inj_join_comp; eauto).
    repeat (rewrite Loc_add_neq; eauto). unfold LocFun.init; ss. destruct R, R'; ss.
    repeat (rewrite Time_join_bot).
    eapply inj_join_comp; eauto. eapply view_inj_prop_pln; eauto.
    unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).
    unfold TimeMap.bot; ss. repeat (rewrite Time_join_bot; eauto).
  - ii. exploit ATM_LOC_ACQ_RLX; eauto. ii; des.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL.
    destruct tview_tgt, tview_src; ss.
    unfold TimeMap.join. 
    unfold View.singleton_ur_if; ss.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    unfold TimeMap.singleton; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq). destruct R, R'; ss.
    repeat (eapply inj_join_comp; eauto). eapply view_inj_prop_rlx; eauto.
    unfold TimeMap.bot. repeat (rewrite Time_join_bot).
    repeat (eapply inj_join_comp; eauto).
    repeat (rewrite Loc_add_neq; eauto). unfold LocFun.init; ss. destruct R, R'; ss.
    repeat (rewrite Time_join_bot).
    eapply inj_join_comp; eauto. eapply view_inj_prop_rlx; eauto.
    unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).
    unfold TimeMap.singleton.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq).
    repeat (rewrite Time_join_bot; eauto).
    eapply inj_join_comp; eauto.
    unfold TimeMap.bot.
    repeat (rewrite Loc_add_neq; eauto). unfold LocFun.init; ss.
    repeat (rewrite Time_join_bot; eauto).
  - ii. exploit NA_LOC_CUR_RLX0; eauto. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL.
    destruct tview_tgt, tview_src; ss.
    unfold View.singleton_ur_if; ss.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    destruct R, R'; ss.
    eapply inj_tm_join_prsv; eauto.
    {
      unfold closed_viewInj in *. des; eauto.
    }
    {
      unfold ViewInj in *. destruct t, t0; ss; eauto.
      des; eauto.
    }
    eapply inj_tm_join_singleton_prsv; eauto.
    repeat (rewrite TimeMap.join_bot; eauto).
    eapply inj_tm_join_singleton_prsv; eauto.
    repeat (rewrite TimeMap.join_bot; eauto).
    eapply inj_tm_join_singleton_prsv; eauto.
Qed.

Lemma InvView_dce_write_fence_prsv
      tview_tgt sc_tgt tview_src sc_src mem_src ow inj lo
      (INV_VIEW: InvView_dce inj lo tview_tgt tview_src mem_src)
      (NOT_SC: ow <> Ordering.seqcst)
      (REL: ow = Ordering.acqrel ->
            ViewInj inj (TView.cur tview_tgt) (TView.cur tview_src)):
  InvView_dce inj lo
              (TView.write_fence_tview tview_tgt sc_tgt ow)
              (TView.write_fence_tview tview_src sc_src ow) mem_src.
Proof.
  rewrite write_fence_tview_not_sc; eauto.
  rewrite write_fence_tview_not_sc; eauto.
  inv INV_VIEW. econs; eauto; ss.
  ii. exploit ATM_LOC_REL; eauto. ii.
  destruct ow; ss.
  des_if; ss. eauto.
Qed.

Lemma InvView_dce_write_fence
      inj tview_tgt sc_tgt tview_src sc_src lo mem_src
      (VIEW_INJ_CUR: ViewInj inj (TView.cur tview_tgt) (TView.cur tview_src))
      (VIEW_INJ_ACQ: ViewInj inj (TView.acq tview_tgt) (TView.acq tview_src))
      (SC_INJ: TMapInj inj sc_tgt sc_src)
      (CLOSED_VIEW: closed_tviewInj inj tview_tgt)
      (CLOSED_SC: closed_TMapInj inj sc_tgt)
      (MON_INJ: monotonic_inj inj):
  InvView_dce inj lo
              (TView.write_fence_tview tview_tgt sc_tgt Ordering.seqcst)
              (TView.write_fence_tview tview_src sc_src Ordering.seqcst) mem_src.
Proof.
  unfold ViewInj in *. destruct tview_tgt, tview_src; ss.
  destruct cur, cur0; ss. destruct acq, acq0; ss. des.
  unfold closed_tviewInj in CLOSED_VIEW; ss. des.
  unfold closed_viewInj in *; ss. des.
  unfold TView.write_fence_tview; ss.
  assert (SEQ_CST: Ordering.le Ordering.seqcst Ordering.seqcst). eauto.
  repeat (rewrite SEQ_CST).
  assert (ORD: Ordering.le Ordering.acqrel Ordering.seqcst). eauto.
  repeat (rewrite ORD).
  unfold TView.write_fence_sc; ss.
  repeat (rewrite SEQ_CST).
  unfold closed_TMapInj, TMapInj in *. 
  econs; eauto; ss; unfold TimeMap.join; ss; ii.
  - eapply inj_join_comp; eauto.
    specialize (CLOSED_SC loc). des.
    exploit SC_INJ; eauto. ii; subst; eauto.
    specialize (CLOSED_VIEW3 loc). des.
    exploit VIEW_INJ_CUR0; eauto. ii; subst; eauto.
  - eapply inj_join_comp; eauto.
    specialize (CLOSED_SC loc). des.
    exploit SC_INJ; eauto. ii; subst; eauto.
    specialize (CLOSED_VIEW3 loc). des.
    exploit VIEW_INJ_CUR0; eauto. ii; subst; eauto.
  - econs; eauto. ii.
    eapply Time_lt_join in H1. des.
    eapply lt_lt_join; eauto. 
    clear H2. eapply MON_INJ; eauto. 
    specialize (CLOSED_SC loc). des. 
    exploit SC_INJ; eauto. ii; subst; eauto.
    clear H1. eapply MON_INJ; eauto. 
    specialize (CLOSED_VIEW3 loc). des. 
    exploit VIEW_INJ_CUR0; eauto. ii; subst; eauto.
    exists (Time.join (sc_src loc) (rlx0 loc)).
    split. eapply inj_join_comp; eauto.
    specialize (CLOSED_SC loc). des.
    exploit SC_INJ; eauto. ii; subst; eauto.
    specialize (CLOSED_VIEW3 loc). des.
    exploit VIEW_INJ_CUR0; eauto. ii; subst; eauto.
    split. eapply Time.le_lteq; eauto.
    ii. inv H0; ss. auto_solve_time_rel.
  - eapply inj_join_comp; eauto.
    specialize (CLOSED_VIEW1 loc). des.
    exploit VIEW_INJ_ACQ; eauto. ii; subst; eauto.
    eapply inj_join_comp; eauto.
    specialize (CLOSED_SC loc). des.
    exploit SC_INJ; eauto. ii; subst; eauto.
    specialize (CLOSED_VIEW3 loc). des.
    exploit VIEW_INJ_CUR0; eauto. ii; subst; eauto.
  - eapply inj_join_comp; eauto.
    specialize (CLOSED_VIEW2 loc). des.
    exploit VIEW_INJ_ACQ0; eauto. ii; subst; eauto.
    eapply inj_join_comp; eauto.
    specialize (CLOSED_SC loc). des.
    exploit SC_INJ; eauto. ii; subst; eauto.
    specialize (CLOSED_VIEW3 loc). des.
    exploit VIEW_INJ_CUR0; eauto. ii; subst; eauto.
  - econs; eauto. ii.
    eapply Time_lt_join in H1. des.
    eapply lt_lt_join; eauto. 
    clear H2. eapply MON_INJ; eauto.
    specialize (CLOSED_VIEW2 loc). des. 
    exploit VIEW_INJ_ACQ0; eauto. ii; subst; eauto.
    eapply Time_lt_join in H2. des.
    eapply lt_lt_join; eauto. 
    clear H3. eapply MON_INJ; eauto.
    specialize (CLOSED_SC loc). des. 
    exploit SC_INJ; eauto. ii; subst; eauto.
    eapply MON_INJ; eauto. 
    specialize (CLOSED_VIEW3 loc). des. 
    exploit VIEW_INJ_CUR0; eauto. ii; subst; eauto.
    exists (Time.join (rlx2 loc) (Time.join (sc_src loc) (rlx0 loc))).
    split. eapply inj_join_comp; eauto.
    specialize (CLOSED_VIEW2 loc). des.
    exploit VIEW_INJ_ACQ0; eauto. ii; subst; eauto.
    eapply inj_join_comp; eauto.
    specialize (CLOSED_SC loc). des.  
    exploit SC_INJ; eauto. ii; subst; eauto.
    specialize (CLOSED_VIEW3 loc). des.
    exploit VIEW_INJ_CUR0; eauto. ii; subst; eauto.
    split. eapply Time.le_lteq; eauto.
    introv ITV. inv ITV; ss. auto_solve_time_rel.
  - split.
    unfold TMapInj; ss. ii.
    assert (inj loc0 (Time.join (sc_tgt loc0) (rlx loc0)) = Some (Time.join (sc_src loc0) (rlx0 loc0))).
    {
      eapply inj_join_comp; eauto.
      specialize (CLOSED_SC loc0). des.  
      exploit SC_INJ; eauto. ii; subst; eauto.
      specialize (CLOSED_VIEW3 loc0). des.  
      exploit VIEW_INJ_CUR0; eauto. ii; subst; eauto.
    }
    rewrite injDom in H0. inv H0; eauto.
    unfold TMapInj; ss. ii.
    assert (inj loc0 (Time.join (sc_tgt loc0) (rlx loc0)) = Some (Time.join (sc_src loc0) (rlx0 loc0))).
    {
      eapply inj_join_comp; eauto.
      specialize (CLOSED_SC loc0). des.  
      exploit SC_INJ; eauto. ii; subst; eauto.
      specialize (CLOSED_VIEW3 loc0). des.  
      exploit VIEW_INJ_CUR0; eauto. ii; subst; eauto.
    }
    rewrite injDom in H0. inv H0; eauto.
Qed.

Lemma InvView_dce_read_fence_prsv
      tview_tgt tview_src mem_src or inj lo
      (INV_VIEW: InvView_dce inj lo tview_tgt tview_src mem_src):
  InvView_dce inj lo (TView.read_fence_tview tview_tgt or) (TView.read_fence_tview tview_src or) mem_src.
Proof.
  unfold TView.read_fence_tview.
  destruct tview_tgt, tview_src; ss.
  des_if; eauto. inv INV_VIEW; ss.
Qed.
      
Definition cur_acq_aux (inj: Mapping) (loc: Loc.t)
           (to_cur to_acq to_cur' to_acq': Time.t) :=
  (Time.lt to_cur to_acq /\ inj loc to_acq = Some to_acq') \/
  (to_cur = to_acq /\ to_cur' = to_acq').

Lemma cur_acq_aux_eq
      lo inj cur_tgt acq_tgt cur_src acq_src:
  (cur_acq lo inj cur_tgt acq_tgt cur_src acq_src)
  <->
  (forall loc, lo loc = Ordering.nonatomic ->
          cur_acq_aux inj loc
                      (View.rlx cur_tgt loc) (View.rlx acq_tgt loc)
                      (View.rlx cur_src loc) (View.rlx acq_src loc)).
Proof.
  split; eauto.
Qed. 

Lemma cur_acq_aux_incr_both_side
      to1 to2 to1' to2' inj loc to to' ts0
      (MONOTONIC_INJ: monotonic_inj inj)
      (INJ_TO: inj loc to = Some to')
      (INJ_TO1: inj loc to1 = Some ts0)
      (LESS: forall ts ts', inj loc ts = Some ts' -> Time.lt to1 ts -> Time.lt to1' ts')
      (CUR_ACQ_AUX: cur_acq_aux inj loc to1 to2 to1' to2'):
  cur_acq_aux inj loc (Time.join to1 to) (Time.join to2 to) (Time.join to1' to') (Time.join to2' to').
Proof.
  unfold cur_acq_aux in *; ss.
  des; subst.
  - destruct (Time.le_lt_dec to to2); subst.
    {
      eapply Time.le_lteq in l. des; subst.
      {
        left.
        split. eapply lt_join_l. eapply lt_lt_join; eauto.
        eapply inj_join_comp; eauto.
      }
      {
        right.
        split. rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto.
        rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto.
        eapply Time.le_lteq; eauto. eapply Time.le_lteq; eauto.
        rewrite INJ_TO in CUR_ACQ_AUX0. inv CUR_ACQ_AUX0.
        rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto.
        rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto.
        eapply Time.le_lteq; eauto.
        eapply Time.le_lteq. left.
        eapply LESS; eauto.
      }
    }
    {
      right.
      rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto.
      rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto.
      rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto.
      rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto.
      eapply Time.le_lteq. left. eauto.
      eapply Time.le_lteq. left. eapply LESS; eauto. auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
      eapply Time.le_lteq. left. auto_solve_time_rel.
    }
  - right. split; eauto.
Qed.

Lemma cur_acq_aux_incr_right_side
      to1 to2 to1' to2' inj loc to to' ts0
      (MONOTONIC_INJ: monotonic_inj inj)
      (INJ_TO: inj loc to = Some to')
      (INJ_TO1: inj loc to1 = Some ts0)
      (LESS: forall ts ts', inj loc ts = Some ts' -> Time.lt to1 ts -> Time.lt to1' ts')
      (LE: Time.le ts0 to1')
      (CUR_ACQ_AUX: cur_acq_aux inj loc to1 to2 to1' to2'):
  cur_acq_aux inj loc to1 (Time.join to2 to) to1' (Time.join to2' to').
Proof.
  unfold cur_acq_aux in *; ss.
  des; subst.
  - left. split. eapply lt_join_l; eauto.
    eapply inj_join_comp; eauto.
  - destruct (Time.le_lt_dec to to2).
    right.
    rewrite TimeFacts.le_join_l; eauto.
    split; eauto.
    rewrite TimeFacts.le_join_l; eauto.
    exploit monotonic_inj_implies_le_prsv;
      [eapply MONOTONIC_INJ | eapply l | eapply INJ_TO | eapply INJ_TO1 | eauto..].
    ii. auto_solve_time_rel.
    left.
    rewrite TimeFacts.le_join_r; eauto.
    split; eauto.
    rewrite TimeFacts.le_join_r; eauto.
    eapply Time.le_lteq; eauto.
    eapply Time.le_lteq; eauto.
Qed.
    
Lemma cur_acq_read_prsv
      lo inj tview_tgt tview_src mem_src loc to to' R R' or
      (CUR_ACQ: cur_acq lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                        (TView.cur tview_src) (TView.acq tview_src))
      (INV_VIEW: InvView_dce inj lo tview_tgt tview_src mem_src)
      (INJ_TO: inj loc to = Some to')
      (VIEW_INJ: opt_ViewInj inj R R')
      (CLOSED_VIEW: closed_opt_viewinj inj R)
      (MONOTONIC_INJ: monotonic_inj inj):
  cur_acq lo inj (TView.cur (TView.read_tview tview_tgt loc to R or))
          (TView.acq (TView.read_tview tview_tgt loc to R or))
          (TView.cur (TView.read_tview tview_src loc to' R' or))
          (TView.acq (TView.read_tview tview_src loc to' R' or)).
Proof.
  eapply cur_acq_aux_eq.
  rewrite cur_acq_aux_eq in CUR_ACQ.
  ii. exploit CUR_ACQ; eauto. ii. clear CUR_ACQ.
  destruct tview_tgt, tview_src; ss.
  unfold TimeMap.join.
  destruct (Ordering.le Ordering.acqrel or) eqn:LE_ACQREL; ss.
  {
    unfold View.singleton_ur_if; ss.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    unfold TimeMap.singleton; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq; eauto).
    destruct R, R'; ss.

    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des. 
    eapply cur_acq_aux_incr_both_side; eauto.
    eapply TMapInj_lower; eauto.
    unfold closed_viewInj in CLOSED_VIEW. des; eauto.
    unfold ViewInj in *. destruct t, t0; ss; des; eauto.
    eapply inj_join_comp; eauto.
    ii. eapply Time_lt_join in H5; des.
    eapply lt_lt_join; eauto.
    eapply cur_acq_aux_incr_both_side; eauto.

    unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des. 
    eapply cur_acq_aux_incr_both_side; eauto.

    repeat (rewrite Loc_add_neq; eauto).
    destruct R, R'; ss.
    unfold LocFun.init; ss. repeat (rewrite Time_join_bot; eauto).
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des. 
    eapply cur_acq_aux_incr_both_side; eauto.
    eapply TMapInj_lower; eauto.
    unfold closed_viewInj in CLOSED_VIEW. des; eauto.
    unfold ViewInj in *. destruct t, t0; ss; des; eauto.

    
    unfold TimeMap.bot, LocFun.init; ss. repeat (rewrite Time_join_bot; eauto).

    destruct or; ss.
  }
  {
    unfold View.singleton_ur_if; ss.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    unfold TimeMap.singleton; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq; eauto).
    destruct R, R'; ss.

    unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des.
    eapply cur_acq_aux_incr_right_side; eauto.
    eapply TMapInj_lower; eauto.
    unfold closed_viewInj in CLOSED_VIEW. des; eauto.
    unfold ViewInj in *. destruct t, t0; ss; des; eauto.
    eapply inj_join_comp; eauto.
    ii.  eapply Time_lt_join in H5; des.
    eapply lt_lt_join; eauto.
    eapply time_join_mon; eauto. eapply Time.le_lteq; eauto.
    eapply cur_acq_aux_incr_both_side; eauto.

    unfold TimeMap.bot; ss.
    repeat (rewrite Time_join_bot; eauto).
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des.
    eapply cur_acq_aux_incr_both_side; eauto.

    unfold TimeMap.bot; ss.
    repeat (rewrite Loc_add_neq; eauto).
    unfold LocFun.init. repeat (rewrite Time_join_bot; eauto).
    destruct R, R'; ss.
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des.
    eapply cur_acq_aux_incr_right_side; eauto.
    eapply TMapInj_lower; eauto.
    unfold closed_viewInj in CLOSED_VIEW. des; eauto.
    unfold ViewInj in *. destruct t, t0; ss; des; eauto.

    unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).

    unfold TimeMap.singleton, TimeMap.bot; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq; eauto).
    repeat (rewrite Time_join_bot; eauto).
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des.
    eapply cur_acq_aux_incr_both_side; eauto.

    repeat (rewrite Loc_add_neq; eauto).
    repeat (rewrite Time_join_bot; eauto).
  }
Qed.

Lemma cur_acq_write_fence
      tview_tgt sc_tgt tview_src sc_src ow lo inj
      (CUR_ACQ: cur_acq lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                        (TView.cur tview_src) (TView.acq tview_src))
      (NOT_SC: ow <> Ordering.seqcst):
  cur_acq lo inj
          (TView.cur (TView.write_fence_tview tview_tgt sc_tgt ow))
          (TView.acq (TView.write_fence_tview tview_tgt sc_tgt ow))
          (TView.cur (TView.write_fence_tview tview_src sc_src ow))
          (TView.acq (TView.write_fence_tview tview_src sc_src ow)).
Proof.
  repeat (rewrite write_fence_tview_not_sc); eauto; ss.
Qed.

Lemma cur_acq_read_fence
      tview_tgt tview_src or lo inj
      (CUR_ACQ: cur_acq lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                        (TView.cur tview_src) (TView.acq tview_src)):
  cur_acq lo inj
          (TView.cur (TView.read_fence_tview tview_tgt or))
          (TView.acq (TView.read_fence_tview tview_tgt or))
          (TView.cur (TView.read_fence_tview tview_src or))
          (TView.acq (TView.read_fence_tview tview_src or)).
Proof.
  unfold TView.read_fence_tview; ss.
  des_if; eauto.
  unfold cur_acq in *.
  ii. right; eauto.
Qed. 

Lemma cur_acq_write_sc_fence
      lo inj tview_tgt sc_tgt tview_src sc_src
      (CUR_ACQ: cur_acq lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                        (TView.cur tview_src) (TView.acq tview_src))
      (LOCAL_WF_SRC: TView.wf tview_src)
      (SC_INJ: TMapInj inj sc_tgt sc_src)
      (CLOSED_SC: closed_TMapInj inj sc_tgt)
      (MON_INJ: monotonic_inj inj):
  cur_acq lo inj
          (TView.cur (TView.write_fence_tview tview_tgt sc_tgt Ordering.seqcst))
          (TView.acq (TView.write_fence_tview tview_tgt sc_tgt Ordering.seqcst))
          (TView.cur (TView.write_fence_tview tview_src sc_src Ordering.seqcst))
          (TView.acq (TView.write_fence_tview tview_src sc_src Ordering.seqcst)).
Proof.
  unfold cur_acq; ss. ii.
  assert (Ordering.le Ordering.seqcst Ordering.seqcst = true). eauto.
  repeat (rewrite H); ss.
  unfold cur_acq in *. exploit CUR_ACQ; eauto. clear CUR_ACQ. ii.
  des.
  - unfold TView.write_fence_sc; ss.
    repeat (rewrite H); ss. unfold TimeMap.join; ss.
    destruct (Time.le_lt_dec (View.rlx (TView.acq tview_tgt) loc) (sc_tgt loc)).
    {
      right. unfold TMapInj in SC_INJ.
      unfold closed_TMapInj in *.
      specialize (CLOSED_SC loc). des. exploit SC_INJ; eauto. ii; subst.
      assert (LE_ACQ_SC_SRC: Time.le (View.rlx (TView.acq tview_src) loc) (sc_src loc)).
      {
        eapply monotonic_inj_implies_le_prsv; eauto.
      }
      repeat (rewrite Time.join_comm with (lhs := (sc_tgt loc))).  
      rewrite <- Time.join_assoc.
      rewrite Time.join_comm with (lhs := (sc_src loc)).
      rewrite <- Time.join_assoc.
      rewrite TimeFacts.le_join_l with
          (lhs := (View.rlx (TView.acq tview_tgt) loc)) (rhs := (View.rlx (TView.cur tview_tgt) loc)); eauto.
      rewrite TimeFacts.le_join_l with
          (lhs := (View.rlx (TView.acq tview_src) loc)) (rhs := (View.rlx (TView.cur tview_src) loc)); eauto.
      repeat (rewrite TimeFacts.le_join_r); eauto.
      clear - LOCAL_WF_SRC LE_ACQ_SC_SRC. inv LOCAL_WF_SRC. inv CUR_ACQ.
      unfold TimeMap.le in RLX. specialize (RLX loc).
      auto_solve_time_rel.
      clear - LT l. eapply Time.le_lteq. left. auto_solve_time_rel.
      clear - LOCAL_WF_SRC. inv LOCAL_WF_SRC. inv CUR_ACQ.
      unfold TimeMap.le in RLX. specialize (RLX loc). eauto.
      eapply Time.le_lteq; eauto.
    }
    {
      left.
      unfold TMapInj in SC_INJ.
      unfold closed_TMapInj in *.
      specialize (CLOSED_SC loc). des. exploit SC_INJ; eauto. ii; subst.
      assert (LT_ACQ_SC_SRC: Time.lt (sc_src loc) (View.rlx (TView.acq tview_src) loc)).
      {
        eapply MON_INJ; eauto.
      }
      repeat (rewrite Time.join_comm with (lhs := (sc_tgt loc))).
      repeat (rewrite Time.join_comm with (lhs := (sc_src loc))).
      rewrite <- Time.join_assoc. rewrite <- Time.join_assoc.
      rewrite TimeFacts.le_join_l with
          (lhs := (View.rlx (TView.acq tview_tgt) loc)) (rhs := (View.rlx (TView.cur tview_tgt) loc)); eauto.
      rewrite TimeFacts.le_join_l with
          (lhs := (View.rlx (TView.acq tview_src) loc)) (rhs := (View.rlx (TView.cur tview_src) loc)); eauto.
      destruct (Time.le_lt_dec (View.rlx (TView.cur tview_tgt) loc) (sc_tgt loc)).
      {
        repeat (rewrite TimeFacts.le_join_r with
                    (lhs := (View.rlx (TView.cur tview_tgt) loc)) (rhs := sc_tgt loc); eauto).
        repeat (rewrite TimeFacts.le_join_l with
                    (lhs := (View.rlx (TView.acq tview_tgt) loc)) (rhs := sc_tgt loc); eauto).
        repeat (rewrite TimeFacts.le_join_l with
                    (lhs := (View.rlx (TView.acq tview_src) loc)) (rhs := sc_src loc); eauto).
        eapply Time.le_lteq; eauto.
        eapply Time.le_lteq; eauto.
      }
      {
        repeat (rewrite TimeFacts.le_join_l with
                    (lhs := (View.rlx (TView.cur tview_tgt) loc)) (rhs := sc_tgt loc); eauto).
        repeat (rewrite TimeFacts.le_join_l with
                    (lhs := (View.rlx (TView.acq tview_tgt) loc)) (rhs := sc_tgt loc); eauto).
        repeat (rewrite TimeFacts.le_join_l with
                    (lhs := (View.rlx (TView.acq tview_src) loc)) (rhs := sc_src loc); eauto).
        eapply Time.le_lteq; eauto.
        eapply Time.le_lteq; eauto.
        eapply Time.le_lteq; eauto.
      }
      clear - LOCAL_WF_SRC. inv LOCAL_WF_SRC.
      inv CUR_ACQ. unfold TimeMap.le in RLX.
      specialize (RLX loc). eauto.
      eapply Time.le_lteq; eauto.
    }
  - right.
    unfold TView.write_fence_sc; ss.
    repeat (rewrite H); ss. unfold TimeMap.join; ss.
    repeat (rewrite EQ). repeat (rewrite EQ0).
    repeat (rewrite Time.join_comm with (lhs := (sc_tgt loc))).  
    rewrite <- Time.join_assoc.
    rewrite Time.join_comm with (lhs := (sc_src loc)).
    rewrite <- Time.join_assoc.
    repeat (rewrite Time_join_same). eauto.
Qed.

Definition cur_acq_pln_aux (inj: Mapping) (loc: Loc.t)
           (to_cur to_acq to_cur' to_acq': Time.t) :=
  (Time.lt to_cur to_acq /\ inj loc to_acq = Some to_acq') \/
  (Time.le to_acq to_cur /\ Time.le to_acq' to_cur').

Lemma cur_acq_pln_aux_eq
      lo inj cur_tgt acq_tgt cur_src acq_src:
  (cur_acq_pln lo inj cur_tgt acq_tgt cur_src acq_src)
  <->
  (forall loc, lo loc = Ordering.nonatomic ->
          cur_acq_pln_aux inj loc
                          (View.rlx cur_tgt loc) (View.pln acq_tgt loc)
                          (View.rlx cur_src loc) (View.pln acq_src loc)).
Proof.
  split; eauto. 
Qed.

Lemma cur_acq_pln_aux_incr_both_side
      to1 to2 to1' to2' inj loc pln pln' rlx rlx' ts0
      (MONOTONIC_INJ: monotonic_inj inj)
      (INJ_TO_pln: inj loc pln = Some pln')
      (INJ_TO_rlx: inj loc rlx = Some rlx')
      (INJ_TO1: inj loc to1 = Some ts0)
      (LE: Time.le ts0 to1')
      (LESS: forall ts ts', inj loc ts = Some ts' -> Time.lt to1 ts -> Time.lt to1' ts')
      (CUR_ACQ_AUX: cur_acq_pln_aux inj loc to1 to2 to1' to2'):
  cur_acq_pln_aux inj loc (Time.join to1 rlx) (Time.join to2 pln) (Time.join to1' rlx') (Time.join to2' pln').
Proof.
  unfold cur_acq_pln_aux in *; ss.
  des; subst.
  - destruct (Time.le_lt_dec rlx to2).
    {
      eapply Time.le_lteq in l. des; subst.
      {
        left. split.
        eapply lt_lt_join.
        eapply lt_join_l; eauto. eapply lt_join_l; eauto.
        eapply inj_join_comp; eauto.
      }
      {
        destruct (Time.le_lt_dec pln to2).
        {
          right.
          rewrite TimeFacts.le_join_l; eauto.
          rewrite Time.join_comm. split. eapply le_join; eauto.
          eapply Time.le_lteq; eauto.
          rewrite INJ_TO_rlx in CUR_ACQ_AUX0. inv CUR_ACQ_AUX0.
          rewrite TimeFacts.le_join_l; eauto.
          rewrite TimeFacts.le_join_r; eauto.
          eapply Time.le_lteq; eauto.
          eapply Time.le_lteq. left. eauto.
          eapply monotonic_inj_implies_le_prsv; eauto.
        }
        {
          left.
          rewrite TimeFacts.le_join_r; eauto.
          rewrite TimeFacts.le_join_r; eauto.
          split; eauto.
          rewrite TimeFacts.le_join_r; eauto.
          eapply Time.le_lteq. left. eauto.
          econs; eauto. econs; eauto.
        }
      }
    }
    {
      destruct (Time.le_lt_dec pln rlx).
      {
        right.
        split. rewrite Time.join_comm with (rhs := rlx). eapply le_join. 
        eapply Time.join_spec; eauto. econs; eauto.
        rewrite Time.join_comm with (rhs := rlx'). eapply le_join.
        eapply Time.join_spec; eauto. econs; eauto.
        eapply monotonic_inj_implies_le_prsv; eauto.
      }
      {
        left.
        split.
        rewrite TimeFacts.le_join_r with (rhs := pln); eauto.
        eapply lt_lt_join. clear - CUR_ACQ_AUX l l0.
        cut (Time.lt to1 rlx). ii.
        auto_solve_time_rel. clear l0. auto_solve_time_rel. eauto.
        econs; eauto. auto_solve_time_rel. 
        rewrite TimeFacts.le_join_r; eauto.
        rewrite TimeFacts.le_join_r; eauto.
        econs; eauto. cut (Time.lt to2 pln). ii. eauto.
        auto_solve_time_rel.
        econs; eauto. auto_solve_time_rel.
      }
    }
  - destruct (Time.le_lt_dec pln to1).
    {
      right.
      split. eapply le_join.
      eapply Time.join_spec; eauto.
      eapply le_join.
      eapply Time.join_spec; eauto. 
      eapply monotonic_inj_implies_le_prsv with (t2' := ts0) in l; eauto.
      auto_solve_time_rel.
    }
    {
      destruct (Time.le_lt_dec rlx pln).
      {
        eapply Time.le_lteq in l0. des; subst.
        {
          left.
          rewrite TimeFacts.le_join_r with (rhs := pln); eauto.
          rewrite TimeFacts.le_join_r with (rhs := pln'); eauto.
          split; eauto.
          eapply lt_lt_join; eauto.
          eapply LESS in l; eauto.
          econs; eauto. auto_solve_time_rel.
          econs; eauto. auto_solve_time_rel.
        }
        {
          right. rewrite INJ_TO_pln in INJ_TO_rlx. inv INJ_TO_rlx.
          rewrite TimeFacts.le_join_r with (rhs := pln); eauto.
          rewrite TimeFacts.le_join_r with (rhs := pln); eauto.
          split. eapply Time.le_lteq; eauto.
          eapply time_join_mon; eauto. eapply Time.le_lteq; eauto.
          econs; eauto. econs; eauto.
          auto_solve_time_rel.
        }
      }
      {
        right.
        rewrite TimeFacts.le_join_r with (rhs := rlx); eauto.
        rewrite TimeFacts.le_join_r with (rhs := rlx'); eauto.
        split.
        eapply Time.join_spec; eauto.
        econs; eauto. cut (Time.lt to2 pln). ii. auto_solve_time_rel.
        auto_solve_time_rel.
        econs; eauto.
        eapply Time.join_spec; eauto.
        econs; eauto.
        cut (Time.lt to1' rlx'). ii. auto_solve_time_rel.
        eapply LESS; eauto. auto_solve_time_rel.
        econs; eauto.
        econs; eauto. eapply LESS; eauto. auto_solve_time_rel.
        econs; eauto. auto_solve_time_rel.
      }
    }
Qed.

Lemma cur_acq_pln_aux_incr_right_side
      to1 to2 to1' to2' inj loc to to' ts0
      (MONOTONIC_INJ: monotonic_inj inj)
      (INJ_TO: inj loc to = Some to')
      (INJ_TO1: inj loc to1 = Some ts0)
      (LESS: forall ts ts', inj loc ts = Some ts' -> Time.lt to1 ts -> Time.lt to1' ts')
      (LE: Time.le ts0 to1')
      (CUR_ACQ_AUX: cur_acq_pln_aux inj loc to1 to2 to1' to2'):
  cur_acq_pln_aux inj loc to1 (Time.join to2 to) to1' (Time.join to2' to').
Proof.
  unfold cur_acq_pln_aux in *; ss.
  des; subst.
  - left.
    split. eapply lt_join_l; eauto.
    eapply inj_join_comp; eauto.
  - destruct (Time.le_lt_dec to to1).
    {
      right.
      split. eapply Time.join_spec; eauto.
      eapply Time.join_spec; eauto.
      eapply monotonic_inj_implies_le_prsv with (t2' := ts0) in l; eauto.
      auto_solve_time_rel.
    }
    {
      left.
      split. rewrite Time.join_comm. eapply lt_join_l; eauto.
      rewrite TimeFacts.le_join_r; eauto. 
      rewrite TimeFacts.le_join_r; eauto.
      eapply LESS in l; eauto. econs; eauto. auto_solve_time_rel.
      econs; eauto. auto_solve_time_rel.
    }
Qed.

Lemma cur_acq_pln_aux_incr_left_side
      to1 to2 to1' to2' inj loc to to' ts0
      (MONOTONIC_INJ: monotonic_inj inj)
      (INJ_TO: inj loc to = Some to')
      (INJ_TO1: inj loc to1 = Some ts0)
      (LESS: forall ts ts', inj loc ts = Some ts' -> Time.lt to1 ts -> Time.lt to1' ts')
      (LE: Time.le ts0 to1')
      (CUR_ACQ_AUX: cur_acq_pln_aux inj loc to1 to2 to1' to2'):
  cur_acq_pln_aux inj loc (Time.join to1 to) to2 (Time.join to1' to') to2'.
Proof.
  unfold cur_acq_pln_aux in *; ss.
  des; subst.
  - destruct (Time.le_lt_dec to to2).
    {
      eapply Time.le_lteq in l. des; subst.
      {
        left. split; eauto.
        eapply lt_lt_join; eauto.
      }
      {
        right.
        split; eauto.
        eapply Time.join_r.
        rewrite INJ_TO in CUR_ACQ_AUX0. inv CUR_ACQ_AUX0.
        eapply Time.join_r.
      }
    }
    {
      right.
      split; eauto.
      rewrite Time.join_comm. eapply le_join; eauto.
      econs; eauto.
      rewrite Time.join_comm. eapply le_join; eauto.
      econs; eauto.
    }
  - right. split.
    eapply le_join; eauto.
    eapply le_join; eauto.
Qed.
    
Lemma cur_acq_pln_read_prsv
      lo inj tview_tgt tview_src mem_src loc to to' R R' or
      (CUR_ACQ: cur_acq_pln lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                            (TView.cur tview_src) (TView.acq tview_src))
      (INV_VIEW: InvView_dce inj lo tview_tgt tview_src mem_src)
      (INJ_TO: inj loc to = Some to')
      (VIEW_INJ: opt_ViewInj inj R R')
      (CLOSED_VIEW: closed_opt_viewinj inj R)
      (MONOTONIC_INJ: monotonic_inj inj):
  cur_acq_pln lo inj (TView.cur (TView.read_tview tview_tgt loc to R or))
              (TView.acq (TView.read_tview tview_tgt loc to R or))
              (TView.cur (TView.read_tview tview_src loc to' R' or))
              (TView.acq (TView.read_tview tview_src loc to' R' or)).
Proof.
  eapply cur_acq_pln_aux_eq.
  rewrite cur_acq_pln_aux_eq in CUR_ACQ.
  ii. exploit CUR_ACQ; eauto. ii. clear CUR_ACQ.
  destruct tview_tgt, tview_src; ss.
  unfold TimeMap.join.
  destruct (Ordering.le Ordering.acqrel or) eqn:LE_ACQREL; ss.
  {
    unfold View.singleton_ur_if; ss.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    unfold TimeMap.singleton; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq; eauto).
    destruct R, R'; ss.
 
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des. 
    eapply cur_acq_pln_aux_incr_both_side; eauto.
    {
      eapply TMapInj_lower; eauto.
      unfold closed_viewInj in CLOSED_VIEW. des; eauto.
      unfold ViewInj in *. destruct t, t0; ss; des; eauto.
    }
    {
      eapply TMapInj_lower; eauto.
      unfold closed_viewInj in CLOSED_VIEW. des; eauto.
      unfold ViewInj in *. destruct t, t0; ss; des; eauto.
    }
    {
      eapply inj_join_comp; eauto.
    }
    {
      eapply time_join_mon; eauto.
      eapply Time.le_lteq; eauto.
    }
    {
      ii. eapply Time_lt_join in H5; des.
      eapply lt_lt_join; eauto.
    }
    {
      eapply cur_acq_pln_aux_incr_both_side; eauto.
    }

    unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des. 
    eapply cur_acq_pln_aux_incr_both_side; eauto.

    repeat (rewrite Loc_add_neq; eauto).
    destruct R, R'; ss.
    unfold LocFun.init; ss. repeat (rewrite Time_join_bot; eauto).
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des. 
    eapply cur_acq_pln_aux_incr_both_side; eauto.
    {
      eapply TMapInj_lower; eauto.
      unfold closed_viewInj in CLOSED_VIEW. des; eauto.
      unfold ViewInj in *. destruct t, t0; ss; des; eauto.
    }
    {
      eapply TMapInj_lower; eauto.
      unfold closed_viewInj in CLOSED_VIEW. des; eauto.
      unfold ViewInj in *. destruct t, t0; ss; des; eauto.
    }
        
    unfold TimeMap.bot, LocFun.init; ss. repeat (rewrite Time_join_bot; eauto).

    destruct or; ss.
  }
  {
    unfold View.singleton_ur_if; ss.
    destruct (Ordering.le Ordering.relaxed or) eqn:LE_RELAXED; ss.
    unfold TimeMap.singleton; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    repeat (rewrite Loc_add_eq; eauto).
    destruct R, R'; ss.

    unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des.
    eapply cur_acq_pln_aux_incr_right_side; eauto.
    {
      eapply TMapInj_lower; eauto.
      unfold closed_viewInj in CLOSED_VIEW. des; eauto.
      unfold ViewInj in *. destruct t, t0; ss; des; eauto.
    }
    {
      eapply inj_join_comp; eauto.
    }
    {
      ii. eapply Time_lt_join in H5; des.
      eapply lt_lt_join; eauto.
    }
    {
      eapply time_join_mon; eauto. eapply Time.le_lteq; eauto.
    }
    {
      eapply cur_acq_pln_aux_incr_both_side; eauto.
    }    

    unfold TimeMap.bot; ss.
    repeat (rewrite Time_join_bot; eauto).
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des.
    eapply cur_acq_pln_aux_incr_both_side; eauto.

    unfold TimeMap.bot; ss.
    repeat (rewrite Loc_add_neq; eauto).
    unfold LocFun.init. repeat (rewrite Time_join_bot; eauto).
    destruct R, R'; ss.
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des.
    eapply cur_acq_pln_aux_incr_right_side; eauto.
    {
      eapply TMapInj_lower; eauto.
      unfold closed_viewInj in CLOSED_VIEW. des; eauto.
      unfold ViewInj in *. destruct t, t0; ss; des; eauto.
    }
    {
      unfold TimeMap.bot. repeat (rewrite Time_join_bot; eauto).
    }

    unfold TimeMap.singleton, TimeMap.bot; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    
    repeat (rewrite Loc_add_eq; eauto).
    repeat (rewrite Time_join_bot; eauto).
    inv INV_VIEW. exploit NA_LOC_CUR_RLX; eauto. simpl. ii.
    clear ATM_LOC_CUR_PLN ATM_LOC_CUR_RLX NA_LOC_CUR_RLX ATM_LOC_ACQ_PLN
          ATM_LOC_ACQ_RLX NA_LOC_CUR_RLX0 ATM_LOC_REL. 
    inv x0. des.
    eapply cur_acq_pln_aux_incr_left_side; eauto.
    
    repeat (rewrite Loc_add_neq; eauto).
    repeat (rewrite Time_join_bot; eauto).
  }
Qed.


Lemma cur_acq_pln_write_fence
      tview_tgt sc_tgt tview_src sc_src ow lo inj
      (CUR_ACQ: cur_acq_pln lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                            (TView.cur tview_src) (TView.acq tview_src))
      (NOT_SC: ow <> Ordering.seqcst):
  cur_acq_pln lo inj
              (TView.cur (TView.write_fence_tview tview_tgt sc_tgt ow))
              (TView.acq (TView.write_fence_tview tview_tgt sc_tgt ow))
              (TView.cur (TView.write_fence_tview tview_src sc_src ow))
              (TView.acq (TView.write_fence_tview tview_src sc_src ow)).
Proof.
  repeat (rewrite write_fence_tview_not_sc); eauto; ss.
Qed. 

Lemma cur_acq_pln_read_fence
      tview_tgt tview_src or lo inj
      (CUR_ACQ_PLN: cur_acq_pln lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                                (TView.cur tview_src) (TView.acq tview_src))
      (CUR_ACQ: cur_acq lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                        (TView.cur tview_src) (TView.acq tview_src))
      (TVIEW_WF_TGT: TView.wf tview_tgt)
      (TVIEW_WF_SRC: TView.wf tview_src):
  cur_acq_pln lo inj
              (TView.cur (TView.read_fence_tview tview_tgt or))
              (TView.acq (TView.read_fence_tview tview_tgt or))
              (TView.cur (TView.read_fence_tview tview_src or))
              (TView.acq (TView.read_fence_tview tview_src or)).
Proof.
  unfold TView.read_fence_tview; ss.
  des_if; eauto.
  unfold cur_acq_pln. ii.
  right.
  inv TVIEW_WF_TGT. inv ACQ.
  unfold TimeMap.le in PLN_RLX.
  inv TVIEW_WF_SRC. inv ACQ.
  unfold TimeMap.le in PLN_RLX0.
  split; eauto.
Qed.

Lemma cur_acq_pln_sc_fence_write
      tview_tgt sc_tgt tview_src sc_src lo inj
      (VIEW_INJ_CUR: ViewInj inj (TView.cur tview_tgt) (TView.cur tview_src))
      (CLOSED_TVIEW: closed_tviewInj inj tview_tgt)
      (SC_INJ: TMapInj inj sc_tgt sc_src)
      (CLOSED_SC: closed_TMapInj inj sc_tgt)
      (MON_INJ: monotonic_inj inj)
      (CUR_ACQ_PLN: cur_acq_pln lo inj
                                (TView.cur tview_tgt) (TView.acq tview_tgt)
                                (TView.cur tview_src) (TView.acq tview_src)):
  cur_acq_pln lo inj
              (TView.cur (TView.write_fence_tview tview_tgt sc_tgt Ordering.seqcst))
              (TView.acq (TView.write_fence_tview tview_tgt sc_tgt Ordering.seqcst))
              (TView.cur (TView.write_fence_tview tview_src sc_src Ordering.seqcst))
              (TView.acq (TView.write_fence_tview tview_src sc_src Ordering.seqcst)).
Proof.
  unfold ViewInj in VIEW_INJ_CUR. destruct tview_tgt, tview_src; ss.
  destruct cur, cur0; ss. des.
  unfold closed_tviewInj in CLOSED_TVIEW; ss. des.
  assert (Ordering.le Ordering.seqcst Ordering.seqcst = true).
  {
    eauto.
  }
  repeat (rewrite H); ss.
  unfold TView.write_fence_sc; ss.
  repeat (rewrite H); ss.
  unfold cur_acq_pln in *; ss. ii.
  unfold TMapInj in VIEW_INJ_CUR0.
  unfold closed_viewInj in CLOSED_TVIEW0; ss. des.
  unfold closed_TMapInj in CLOSED_TVIEW2.
  specialize (CLOSED_TVIEW2 loc). des. exploit VIEW_INJ_CUR0; eauto. ii; subst.
  unfold TimeMap.join; ss.
  unfold TMapInj in SC_INJ.
  unfold closed_TMapInj in CLOSED_SC.
  specialize (CLOSED_SC loc). des. exploit SC_INJ; eauto. ii; subst.
  exploit CUR_ACQ_PLN; eauto. ii; clear CUR_ACQ_PLN.
  des.
  - destruct (Time.le_lt_dec (View.pln acq loc) (sc_tgt loc)).
    {
      assert (LT_CUR_RLX_SC_T: Time.lt (rlx loc) (sc_tgt loc)).
      {
        auto_solve_time_rel.
      }
      assert (LE_ACQ_PLN_SC_S: Time.le (View.pln acq0 loc) (sc_src loc)).
      {
        eapply monotonic_inj_implies_le_prsv; eauto.
      }
      assert (LT_CUR_RLX_SC_S: Time.lt (rlx0 loc) (sc_src loc)).
      {
        eapply MON_INJ; eauto.
      }
      right.
      repeat (rewrite TimeFacts.le_join_l with (lhs := sc_tgt loc); eauto).
      repeat (rewrite TimeFacts.le_join_r with (rhs := sc_tgt loc); eauto).
      repeat (rewrite TimeFacts.le_join_l with (lhs := sc_src loc); eauto).
      repeat (rewrite TimeFacts.le_join_r with (lhs := View.pln acq0 loc); eauto).
      split; try solve [eapply Time.le_lteq; eauto].
      eapply Time.le_lteq; eauto. eapply Time.le_lteq; eauto.
    }
    {
      repeat (rewrite TimeFacts.le_join_l with (lhs := View.pln acq loc); eauto).
      rewrite TimeFacts.le_join_l with (lhs := View.pln acq0 loc); eauto.
      left. split; eauto.
      eapply lt_lt_join; eauto.
      eapply Time.join_spec; eauto.
      eapply Time.le_lteq. left; eauto.
      eapply Time.le_lteq; left; eauto.
      eapply Time.join_spec; eauto.
      eapply Time.le_lteq. left; eauto.
      eapply Time.le_lteq; left; eauto.
    }
  - destruct (Time.le_lt_dec (rlx loc) (sc_tgt loc)).
    {
      assert (LE_CUR_RLX_SC_S: Time.le (rlx0 loc) (sc_src loc)).
      {
        eapply monotonic_inj_implies_le_prsv; eauto.
      }
      right.
      repeat (rewrite TimeFacts.le_join_l with (lhs := sc_tgt loc); eauto).
      repeat (rewrite TimeFacts.le_join_r with (rhs := sc_tgt loc); eauto).
      repeat (rewrite TimeFacts.le_join_l with (lhs := sc_src loc); eauto).
      repeat (rewrite TimeFacts.le_join_r with (rhs := sc_src loc); eauto).
      split; try solve [eapply Time.le_lteq; eauto].
      auto_solve_time_rel.
      auto_solve_time_rel.
    }
    {
      right.
      assert (LT_CUR_RLX_SC_S: Time.lt (sc_src loc) (rlx0 loc)).
      {
        eapply MON_INJ; eauto.
      }
      repeat (rewrite TimeFacts.le_join_r with (lhs := sc_tgt loc); eauto).
      repeat (rewrite TimeFacts.le_join_r with (rhs := rlx loc); eauto).
      repeat (rewrite TimeFacts.le_join_r with (rhs := rlx0 loc); eauto).
      split; try solve [eapply Time.le_lteq; eauto].
      eapply Time.le_lteq; eauto.
      eapply Time.le_lteq; eauto.
    }
Qed.
  
Lemma TM_rely_stable
      inj inj' loc tm1 tm2 mem mem' sc' lo mem0 sc0
      (TM_H: TM inj loc tm1 tm2 mem)
      (CONCRETE_INCR: concrete_mem_incr mem mem')
      (INCR_INJ: incr_inj inj inj')
      (INV: I_dce lo inj' (Build_Rss sc0 mem0 sc' mem'))
      (NA_LOC: lo loc = Ordering.nonatomic):
  TM inj' loc tm1 tm2 mem'.
Proof.
  inv TM_H. des.
  econs; eauto.
  - ii.
    destruct (inj loc to) eqn:INJ_ORIGN.
    lets INJ_ORIGN': INJ_ORIGN. eapply INCR_INJ in INJ_ORIGN'.
    rewrite H3 in INJ_ORIGN'. inv INJ_ORIGN'. eauto.
    eapply INCR_INJ in H0.
    destruct (Time.le_lt_dec to'0 (tm2 loc)); eauto.
    assert (LT: Time.lt to' to'0).
    {
      simpl in INV. des. inv INJ_MEM; eauto.
    }
    eapply Time.le_lteq in H1. des; subst; try solve [auto_solve_time_rel].
    simpl in INV. des. inv INJ_MEM.
    exploit COMPLETE; [eapply H3 | eauto..]. ii; des.
    eapply SOUND in x; eauto. des. rewrite H3 in x. symmetry in x. inv x.
    exploit COMPLETE; [eapply H0 | eauto..]. ii; des.
    eapply SOUND in x. des. rewrite H0 in x. symmetry in x. inv x.
    exploit Memory_get_disj_proper; [eapply x3 | eapply x1 | eauto..].
    introv LE.
    exploit TS_RSV; [eapply x1 | eauto..].
    {
      clear - H4. cut (Time.le Time.bot (tm1 loc)). ii.
      auto_solve_time_rel. eapply Time.bot_spec; eauto.
    }

    ii; des.
    specialize (x4 f').
    assert (ITV: Interval.mem (to_r, f') f').
    {
      econs; eauto. ss. eapply Time.le_lteq; eauto.
    }
    eapply x4 in ITV.
    specialize (H2 f').
    eapply Time.le_lteq in LE. des; subst.
    {
      assert (ITV': Interval.mem (to', tm2 loc) f'); eauto.
      econs; ss; eauto.
      clear - x1 l. eapply memory_get_ts_le in x1.
      auto_solve_time_rel.
      eapply H2 in ITV'.
      eapply concrete_covered_concrete_mem_incr_prsv in ITV'; eauto.
      clear - ITV ITV'.
      contradiction ITV. inv ITV'. econs; eauto.
    }
    {
      exploit Memory.get_ts; [eapply x3 | eauto..]. ii; des; subst.
      auto_solve_time_rel.
      contradiction ITV; eauto. econs; eauto. econs; ss; eauto.
      eapply Time.le_lteq; eauto.
    }
  - exists to'. splits; eauto.
    introv ITV. eapply H2 in ITV.
    eapply concrete_covered_concrete_mem_incr_prsv; eauto.
Qed.

Lemma InvView_dce_rely_stable'
      inj inj'
      sc_tgt mem_tgt sc_src mem_src
      sc_tgt' mem_tgt' sc_src' mem_src'
      tview_tgt tview_src lo
      (INV: I_dce lo inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src'))
      (INV0: I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (INCR_INJ: incr_inj inj inj')
      (INV_VIEW: InvView_dce inj lo tview_tgt tview_src mem_src)
      (CONCRETE_INCR_TGT: concrete_mem_incr mem_tgt mem_tgt')
      (CONCRETE_INCR_SRC: concrete_mem_incr mem_src mem_src')
      (CLOSED_VIEWINJ: TView.closed tview_tgt mem_tgt):
  InvView_dce inj' lo tview_tgt tview_src mem_src'.
Proof.
  inv INV_VIEW.
  econs; eauto.
  - clear - INV CONCRETE_INCR_TGT CONCRETE_INCR_SRC NA_LOC_CUR_RLX INCR_INJ.
    ii. exploit NA_LOC_CUR_RLX; eauto. ii. clear NA_LOC_CUR_RLX.
    simpl in CONCRETE_INCR_TGT, CONCRETE_INCR_SRC.
    eapply TM_rely_stable; eauto.
  - clear - INV CONCRETE_INCR_TGT CONCRETE_INCR_SRC NA_LOC_CUR_RLX0 INCR_INJ.
    ii. exploit NA_LOC_CUR_RLX0; eauto. ii. clear NA_LOC_CUR_RLX0.
    simpl in CONCRETE_INCR_TGT, CONCRETE_INCR_SRC.
    eapply TM_rely_stable; eauto.
  - ii. lets ATOM_LOC: H. eapply ATM_LOC_REL in H.
    eapply incr_inj_ViewInj; eauto.
    clear - CLOSED_VIEWINJ INV0. inv CLOSED_VIEWINJ.
    specialize (REL loc).
    eapply closed_view_msginj_implies_closed_viewInj; eauto.
    ss. des; eauto.
Qed.
      
Lemma InvView_dce_rely_stable
      inj inj'
      sc_tgt mem_tgt sc_src mem_src
      sc_tgt' mem_tgt' sc_src' mem_src'
      tview_tgt prm_tgt tview_src prm_src lo
      (INV: I_dce lo inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src'))
      (INV0: I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (INCR_INJ: incr_inj inj inj')
      (INV_VIEW: InvView_dce inj lo tview_tgt tview_src mem_src)
      (ENV_STEPS: env_steps (Build_Rss sc_tgt mem_tgt sc_src mem_src)
                            (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src') prm_tgt prm_src)
      (CLOSED_VIEWINJ: TView.closed tview_tgt mem_tgt):
  InvView_dce inj' lo tview_tgt tview_src mem_src'.
Proof.
  eapply InvView_dce_rely_stable'; eauto.
  inv ENV_STEPS. eauto. inv ENV_STEPS. eauto.
Qed.

Lemma cur_acq_rely_stable
      inj view_cur_tgt view_acq_tgt view_cur_src view_acq_src
      inj' lo
      (CUR_ACQ: cur_acq lo inj view_cur_tgt view_acq_tgt view_cur_src view_acq_src)
      (INCR_INJ: incr_inj inj inj'):
      (*(MONOTONIC_INJ: monotonic_inj inj):*)
  cur_acq lo inj' view_cur_tgt view_acq_tgt view_cur_src view_acq_src.
Proof.
  unfold cur_acq in *; ss. ii.
  exploit CUR_ACQ; eauto. clear CUR_ACQ.
  ii; des.
  - left. split; eauto.
  - right. split; eauto.
Qed.

Lemma cur_acq_pln_rely_stable
      inj view_cur_tgt view_acq_tgt view_cur_src view_acq_src
      inj' lo
      (CUR_ACQ: cur_acq_pln lo inj view_cur_tgt view_acq_tgt view_cur_src view_acq_src)
      (INCR_INJ: incr_inj inj inj'):
  cur_acq_pln lo inj' view_cur_tgt view_acq_tgt view_cur_src view_acq_src.
Proof.
  unfold cur_acq_pln in *; ss. ii.
  exploit CUR_ACQ; eauto. clear CUR_ACQ.
  ii; des.
  - left. split; eauto.
  - right. split; eauto.
Qed.

Lemma rel_promises_rely_stable
      inj inj' prm_tgt prm_src index (pdset:@DelaySet index) 
      (REL_PROM: rel_promises inj pdset prm_tgt prm_src)
      (INCR_INJ: incr_inj inj inj'):
  rel_promises inj' pdset prm_tgt prm_src.
Proof.
  inv REL_PROM. econs; eauto.
  - ii. exploit SOUND1; eauto. ii; des.
    do 4 eexists. split; eauto.
  - ii. exploit SOUND2; eauto. ii; des.
    do 4 eexists. split; eauto.
  - ii. exploit COMPLETE; eauto. ii; des.
    exists t. split; eauto.
    exists t. split; eauto.
Qed.

Lemma promises_relation_rely_stable
      inj inj' lo prm_tgt prm_src
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (INCR_INJ: incr_inj inj inj'):
  promises_relation inj' lo prm_tgt prm_src.
Proof.
  inv PROM_REL.
  econs; eauto. clear H0.
  eapply rel_promises_rely_stable; eauto.
Qed. 

Lemma TM_src_view_le_unused_timestamps
      inj loc tm tm' mem' to to' from' val' R' to_r
      (TM_H: TM inj loc tm tm' mem')
      (CLOSED_TM: Memory.closed_timemap tm' mem')
      (GET: Memory.get loc to' mem' = Some (from', Message.concrete val' R'))
      (INJ: inj loc to = Some to')
      (LT: Time.lt (tm loc) to)
      (ITV: Time.lt to_r from')
      (NOCOVER: forall ts, Interval.mem (to_r, from') ts -> ~ Cover.covered loc ts mem'):
  Time.le (tm' loc) to_r.
Proof.
  inv TM_H. des.
  destruct (Time.le_lt_dec (tm' loc) to_r); eauto.
  exploit H; [eapply INJ | eapply LT | eauto..]. introv LT'.
  unfold Memory.closed_timemap in CLOSED_TM. specialize (CLOSED_TM loc). des.
  exploit Memory_get_disj_proper; [eapply CLOSED_TM | eapply GET | eapply LT' | eauto..].
  introv LE.
  specialize (NOCOVER (tm' loc)).
  exploit NOCOVER; eauto. econs; eauto.
  econs. eapply CLOSED_TM.
  eapply Memory.get_ts in CLOSED_TM. des; subst.
  clear - CLOSED_TM0 l. rewrite CLOSED_TM0 in l. auto_solve_time_rel.
  econs; eauto. ss. eapply Time.le_lteq; eauto.
  ii; ss.
Qed.

Lemma inj_src_view_le_unused_timestamps
      inj loc ts ts' f0 v0 R0 mem' to to' from' val' R' to_r
      (TM_H: inj loc ts = Some ts')
      (GET0: Memory.get loc ts' mem' = Some (f0, Message.concrete v0 R0))
      (GET: Memory.get loc to' mem' = Some (from', Message.concrete val' R'))
      (INJ: inj loc to = Some to')
      (LT: Time.lt ts to)
      (ITV: Time.lt to_r from')
      (NOCOVER: forall ts, Interval.mem (to_r, from') ts -> ~ Cover.covered loc ts mem')
      (MON_INJ: monotonic_inj inj)
      (CLOSED_MEM: Memory.closed mem'):
  Time.le ts' to_r.
Proof.
  exploit TM_src_view_le_unused_timestamps.
  {
    instantiate (5 := inj). instantiate (4 := loc).
    instantiate (3 := TimeMap.singleton loc ts). instantiate (2 := TimeMap.singleton loc ts').
    instantiate (1 := mem').
    econs; eauto. unfold TimeMap.singleton. do 2 (rewrite Loc_add_eq; eauto).
    unfold TimeMap.singleton. do 2 (rewrite Loc_add_eq; eauto).
    exists ts'. split; eauto. split. eapply Time.le_lteq; eauto.
    introv ITV'. inv ITV'; ss. auto_solve_time_rel.
  }
  {
    unfold TimeMap.singleton, Memory.closed_timemap. ii.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      rewrite Loc_add_eq; eauto.
    }
    {
      rewrite Loc_add_neq; eauto. inv CLOSED_MEM.
      unfold Memory.inhabited in INHABITED. specialize (INHABITED loc0).
      unfold LocFun.init. eauto.
    }
  }
  eapply GET. eauto.
  unfold TimeMap.singleton. rewrite Loc_add_eq. eauto.
  eauto. eauto.
  unfold TimeMap.singleton. rewrite Loc_add_eq. eauto.
Qed. 
  
Lemma TM_I_dce_non_atomic_write
      inj loc lo
      tview_tgt prm_tgt sc_tgt mem_tgt tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      tview_src prm_src sc_src mem_src
      from to val Rw ord kind
      (TM_H: TM inj loc (View.rlx (TView.cur tview_tgt)) (View.rlx (TView.cur tview_src)) mem_src)
      (INV: I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (LOC: lo loc = Ordering.nonatomic)
      (WRITE: Local.write_step (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt loc from to val None Rw ord
                               (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt' kind lo)
      (LOCAL_WF_TGT: Local.wf (Local.mk tview_tgt prm_tgt) mem_tgt)
      (CLOSED_SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_CLOSED_TGT: Memory.closed mem_tgt)
      (LOCAL_WF_SRC: Local.wf (Local.mk tview_src prm_src) mem_src)
      (MEM_CLOSED_SRC: Memory.closed mem_src)
      (PRM_REL: promises_relation inj lo prm_tgt prm_src)
      (PRM_CONS: Local.promise_consistent (Local.mk tview_src prm_src)):
  exists from' to' tview_src' prm_src' mem_src' kind' inj',
    <<LOCAL_WRITE_SRC: Local.write_step (Local.mk tview_src prm_src) sc_src mem_src loc from' to' val None None ord
                                        (Local.mk tview_src' prm_src') sc_src mem_src' kind' lo>> /\
    <<TM_H': inj' loc (View.rlx (TView.cur tview_tgt') loc) = Some (View.rlx (TView.cur tview_src') loc)>> /\ 
    <<INJ': inj' = fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to' else (inj loc1 to1)>> /\
    <<INJ_INCR: incr_inj inj inj'>> /\ <<MON_INJ: monotonic_inj inj' >> /\
    <<SPLIT_INJ: forall t val R, kind = Memory.op_kind_split t (Message.concrete val R) -> kind' = Memory.op_kind_add>> /\
    <<INV': I_dce lo inj' (Build_Rss sc_tgt' mem_tgt' sc_src mem_src')>> /\ 
    <<KIND_MATCH: (forall t val R, kind <> Memory.op_kind_split t (Message.concrete val R)) ->
                             kind_match kind kind'>>.
Proof.
  inv WRITE. simpl in LC2. inv LC2. simpl in RELEASE, WRITABLE, WRITE0.
  destruct kind.
  - (* memory add *)
    pose proof (next_concrete_ext_loc0 mem_tgt' loc to) as NXT.
    des1. 
    {
      (* next message exists *)
      do 6 des1.
      assert (NXT_TGT: Memory.get loc nxt_ts mem_tgt = Some (f0, Message.concrete val0 R0)).
      {
        inv WRITE0. inv PROMISE. erewrite Memory.add_o in NXT0; eauto.
        des_ifH NXT0; eauto. ss; des; subst. auto_solve_time_rel.
      }      
      simpl in INV. do 5 des1.
      assert (NXT_SRC: exists nxt_ts' f_s val_s R_s,
                 Memory.get loc nxt_ts' mem_src = Some (f_s, Message.concrete val_s R_s) /\
                 inj loc nxt_ts = Some nxt_ts').
      {
        clear - INJ_MEM NXT_TGT. inv INJ_MEM.
        exploit SOUND; eauto. ii; des; eauto. do 4 eexists. eauto.
      }
      do 5 des1.

      (* find unused timestamp *)
      exploit TS_RSV; [eapply NXT_SRC | eauto..].
      {
        clear - NXT NXT_SRC. pose proof (Time.bot_spec nxt_ts).
        eapply Time.le_lteq in H. des; subst; try solve [auto_solve_time_rel]. eauto.
      }
      introv Unused_Timestamps. do 2 des1.
      (* do source write *) 
      assert (ADD: exists mem_src',
                 Memory.write prm_src mem_src loc (Time.middle to_r (Time.middle to_r f_s))
                              (Time.middle to_r f_s) val None
                              prm_src mem_src' Memory.op_kind_add).
      {
        eapply write_succeed_valid; eauto.
        {
          inv LOCAL_WF_SRC; eauto.
        }
        {
          introv COVER ITV. specialize (Unused_Timestamps0 t).
          eapply Unused_Timestamps0; eauto. inv ITV. ss. econs; eauto. ss.
          pose proof (Time.middle_spec Unused_Timestamps).  des.
          eapply Time.middle_spec in H. des. clear - FROM H. auto_solve_time_rel.
          eapply Time.le_lteq. left; ss.
          eapply Time.middle_spec in Unused_Timestamps. des. auto_solve_time_rel.
        }
        {
          ss. unfold TimeMap.bot. eapply Time.bot_spec.
        }
        {
          eapply Time.middle_spec in Unused_Timestamps. des; eauto.
          eapply Time.middle_spec in Unused_Timestamps. des; eauto.
        }
        {
          introv ATTACH. eapply RSV_ITV_insert_middle_not_attach in ATTACH; eauto.
        }
        {
          econs; eauto.
        }
      }
      des1.
      assert (WRITEABLE': Time.le (View.rlx (TView.cur tview_src) loc) to_r).
      {
        eapply TM_src_view_le_unused_timestamps; eauto.
        clear - LOCAL_WF_SRC. inv LOCAL_WF_SRC; ss. inv TVIEW_CLOSED. inv CUR; eauto.
        clear - WRITABLE NXT. inv WRITABLE. auto_solve_time_rel.
      }

      (* find increasing injection *)
      assert (NEW: inj loc to = None).
      {
        clear - WRITE0 INJ_MEM. inv WRITE0. inv PROMISE.
        eapply Memory.add_get0 in MEM. des. destruct (inj loc to) eqn:INJ; eauto.
        inv INJ_MEM. exploit COMPLETE; eauto. ii; des.
        rewrite GET in x. ss.
      }
      exploit wf_inj_incr; [ | eapply NEW | eauto..].
      {
        inv INJ_MEM; eauto.
      }
      {
        inv ADD. inv PROMISE.
        instantiate (1 := Time.middle to_r f_s). introv INJ_ORIGN LT.
        {
          inv INJ_MEM. exploit COMPLETE; [eapply INJ_ORIGN | eauto..]. ii; des.
          exploit SOUND; eauto. ii; des. rewrite INJ_ORIGN in x0. symmetry in x0. inv x0.
          exploit inj_src_view_le_unused_timestamps; [eapply INJ_ORIGN | eapply x2 | eapply NXT_SRC | eauto..].
          auto_solve_time_rel.
          introv LE.
          eapply Time.middle_spec in Unused_Timestamps. des. auto_solve_time_rel.
        }
      }
      {
        introv INJ LT.
        destruct (Time.le_lt_dec nxt_ts ts).
        {
          inv INJ_MEM. 
          exploit monotonic_inj_implies_le_prsv; [eapply MONOTONIC | eapply l | eauto..].
          introv LE'. clear - LE' NXT_SRC Unused_Timestamps.
          eapply memory_get_ts_le in NXT_SRC. eapply Time.middle_spec in Unused_Timestamps. des.
          cut (Time.le f_s ts'). ii. auto_solve_time_rel.
          clear - NXT_SRC LE'. auto_solve_time_rel.
        }
        { 
          clear - INJ_MEM INJ LT l NXT1 WRITE0. inv INJ_MEM.
          exploit COMPLETE; eauto. ii; des.
          exploit SOUND; eauto. ii; des. clear SOUND COMPLETE MONOTONIC.
          rewrite INJ in x0. inv x0.
          inv WRITE0. inv PROMISE. eapply Memory.add_get1 in x; eauto.
          eapply NXT1 in x; eauto. des. auto_solve_time_rel. auto_solve_time_rel.
          ii. auto_solve_time_rel. ii; subst.
          auto_solve_time_rel.
        }
      }
      introv NEW_INJ. do 3 des1.
 
      do 2 eexists. exists (TView.write_tview tview_src sc_src loc (Time.middle to_r f_s) ord).
      do 3 eexists. exists inj'.
      splits.
      {
        econs; eauto.
        rewrite LOC in LO. simpl in LO. subst.
        simpl. econs.
        ss. econs; eauto. eapply Time.middle_spec in Unused_Timestamps. des. auto_solve_time_rel.
        rewrite LOC in LO. simpl in LO. subst.
        ii; ss.
      }
      {
        inv WRITABLE.
        exploit write_cur_view_to; [eapply TS | eauto..].
        inv LOCAL_WF_TGT; eauto. instantiate (1 := ord). instantiate (1 := sc_tgt).
        ii. des. rewrite VIEW_CUR_RLX.
        cut (Time.lt (View.rlx (TView.cur tview_src) loc) (Time.middle to_r f_s)). introv WRITEABLE_SRC.
        exploit write_cur_view_to; [eapply WRITEABLE_SRC | eauto..].
        inv LOCAL_WF_SRC; eauto. instantiate (1 := ord). instantiate (1 := sc_src).
        ii. des. rewrite VIEW_CUR_RLX0.
        des_if; eauto. ss. des; ss.
        eapply Time.middle_spec in Unused_Timestamps. des.
        auto_solve_time_rel.
      }
      eauto. eauto. eauto. ii; tryfalse.
      {
        ss. splits; eauto.

        (* TMapInj *)
        eapply incr_inj_TMapInj; eauto.
        eapply closed_tm_to_closed_TMapInj; eauto.

        (* Msginj *)
        eapply add_msgInj_stable_concrete.
        {
          eapply INJ_MEM.
        }
        {
          inv WRITE0. inv PROMISE. eauto.
        }
        {
          inv ADD. inv PROMISE. eauto.
        }
        {
          rewrite LOC in LO. simpl in LO. subst.
          unfold TView.write_released. ss.
        }
        eauto. eauto. subst. des_if; eauto. ss; des; ss.
        {
          rewrite NEW_INJ0. introv INJ_GET. des_ifH INJ_GET. ss. des; subst.
          inv WRITE0. inv PROMISE. eapply Memory.add_get0 in MEM. des; eauto.
          simpl in o.
          clear - INJ_MEM INJ_GET WRITE0. inv WRITE0. inv PROMISE.
          inv INJ_MEM. exploit COMPLETE; eauto. ii; des.
          exploit SOUND; eauto. ii; des. rewrite INJ_GET in x0. inv x0.
          eapply Memory.add_get1 in x; eauto.
        }
        eauto.

        (* Unused timestamps *)
        introv GET_SRC INJ'_GET LT' NON_ATOMIC_LOC.
        inv ADD. inv PROMISE. erewrite Memory.add_o in GET_SRC; eauto.
        des_ifH GET_SRC.
        {
          simpl in a. des; subst. inv GET_SRC.
          exists to_r. split. eapply Time.middle_spec in Unused_Timestamps. des.
          eapply Time.middle_spec in Unused_Timestamps. des; eauto.
          clear - Unused_Timestamps Unused_Timestamps0 MEM.
          introv ITV COVER. specialize (Unused_Timestamps0 ts).
          eapply Unused_Timestamps0; eauto.
          inv ITV. ss. econs; eauto. ss.
          eapply Time.middle_spec in Unused_Timestamps. des.
          eapply Time.middle_spec in Unused_Timestamps. des.
          clear - TO Unused_Timestamps2 Unused_Timestamps1.
          econs. cut (Time.lt ts  (Time.middle to_r f_s)). ii.
          auto_solve_time_rel. auto_solve_time_rel.
          eapply Cover.add_covered in COVER; eauto. des; eauto.
          clear - Unused_Timestamps ITV COVER0.
          inv ITV. ss. inv COVER0; ss.
          auto_solve_time_rel.
        }
        {
          simpl in o. des_ifH INJ'_GET; eauto.
          simpl in a. des; subst; ss. inv INJ'_GET. ss.
          destruct (Loc.eq_dec loc loc0); subst.
          {
            (* same location *)
            des1; ss. des1; ss.
            destruct (Time.eq_dec to0 nxt_ts); subst.
            {
              rewrite NXT_SRC0 in INJ'_GET. inv INJ'_GET.
              rewrite NXT_SRC in GET_SRC. inv GET_SRC.
              exists (Time.middle to_r from'). split. eapply Time.middle_spec in Unused_Timestamps.
              des; eauto.
              introv ITV COVER. specialize (Unused_Timestamps0 ts).
              eapply Unused_Timestamps0; eauto. econs; eauto. ss.
              eapply Time.middle_spec in Unused_Timestamps. des.
              inv ITV; ss. auto_solve_time_rel.
              ss. inv ITV; ss.
              eapply Cover.add_covered in COVER; eauto. des1; eauto.
              des1. clear - ITV COVER0. inv ITV; ss. inv COVER0; ss.
              auto_solve_time_rel.
            }
            {
              destruct (Time.le_lt_dec to0 nxt_ts).
              {
                eapply Time.le_lteq in l. des; subst; ss.
                exploit inj_src_view_le_unused_timestamps;
                  [eapply INJ'_GET | eapply GET_SRC | eapply NXT_SRC | eapply NXT_SRC0 | eauto..].
                inv INJ_MEM; eauto.
                introv LE. exploit TS_RSV; [eapply GET_SRC | eauto..]. ii; des.
                exists to_r0. split; eauto. introv ITV' COVER. specialize (x0 ts).
                eapply x0; eauto.
                eapply Cover.add_covered in COVER; eauto. des; eauto.
                clear - GET_SRC LE ITV' COVER0 Unused_Timestamps. inv COVER0; ss.
                eapply memory_get_ts_le in GET_SRC. clear TO. inv ITV'; ss. clear FROM0.
                eapply Time.middle_spec in Unused_Timestamps. des. clear Unused_Timestamps0.
                eapply Time.middle_spec in Unused_Timestamps. des. clear Unused_Timestamps0.
                cut (Time.lt ts (Time.middle to_r (Time.middle to_r f_s))).
                ii. auto_solve_time_rel. ii; auto_solve_time_rel.
                clear - TO GET_SRC LE Unused_Timestamps.
                cut (Time.le ts to_r). ii. auto_solve_time_rel.
                cut (Time.le ts to'). ii. auto_solve_time_rel. auto_solve_time_rel.
              }
              {
                exploit TS_RSV; [eapply GET_SRC | eauto..]. ii; des.
                exploit inj_src_view_le_unused_timestamps;
                  [eapply NXT_SRC0 | eapply NXT_SRC | eapply GET_SRC | eauto..].
                inv INJ_MEM; eauto. introv LE.
                exists to_r0. split; eauto. introv ITV' COVER. specialize (x0 ts).
                eapply x0; eauto.
                eapply Cover.add_covered in COVER; eauto. des; eauto.
                clear - NXT_SRC Unused_Timestamps LE ITV' COVER0.
                inv ITV'; ss. clear TO. inv COVER0; ss. clear FROM0.
                cut (Time.le ts to_r0). ii. auto_solve_time_rel.
                cut (Time.le ts nxt_ts'). ii. auto_solve_time_rel.
                eapply memory_get_ts_le in NXT_SRC.
                cut (Time.le ts f_s). ii. auto_solve_time_rel.
                eapply Time.middle_spec in Unused_Timestamps. des.
                econs. auto_solve_time_rel.
              }
            }
          }
          {
            (* disjoint loc *)
            exploit TS_RSV; eauto. ii. do 2 des1.
            exists to_r0. split; eauto.
            introv ITV COVER. specialize (x0 ts). eapply x0; eauto.
            eapply Cover.add_covered in COVER; eauto. des1; eauto.
            des1; subst. des1; ss.
          }
        }

        (* reservation preservation *)
        clear - ADD NO_RSVs. introv GET. inv ADD. inv PROMISE.
        erewrite Memory.add_o in GET; eauto. des_ifH GET; eauto.
        ss.

        (* Identity injection on atomic location *)
        clear - NEW_INJ0 ID_ATOMIC LOC. ii. subst.
        des_ifH H0; eauto. ss. des; subst; ss. tryfalse.

        (* closed memory *)
        inv ADD. inv PROMISE.
        eapply Memory.add_closed; eauto.
      }

      ii; ss.
    }
    {
      (* next message not exist *)
      (* find unused timestamp *)
      pose proof (Cover.gt_max_not_covered) as MAX_NO_COVER.
      (* do source write *)
      assert (ADD: exists mem_src',
                 Memory.write prm_src mem_src loc (Time.incr (Memory.max_ts loc mem_src))
                              (Time.incr (Time.incr (Memory.max_ts loc mem_src))) val None prm_src mem_src'
                              Memory.op_kind_add).
      {
        eapply write_succeed_valid; eauto.
        {
          eapply LOCAL_WF_SRC; eauto.
        }
        {
          introv COVER ITV. inv ITV. simpl in FROM, TO.
          cut (Time.lt (Memory.max_ts loc mem_src) t). introv LT.
          eapply MAX_NO_COVER in LT. tryfalse.
          clear - FROM. assert (Time.lt (Memory.max_ts loc mem_src) (Time.incr (Memory.max_ts loc mem_src))).
          auto_solve_time_rel. auto_solve_time_rel.
        }
        {
          simpl. unfold TimeMap.bot. eapply Time.bot_spec.
        }
        {
          auto_solve_time_rel.
        }
        {
          introv ATTACH. inv ATTACH. des.
          exploit memory_get_ts_le; eauto. introv LE.
          eapply Memory.max_ts_spec in GET. des.
          cut (Time.le (Time.incr (Time.incr (Memory.max_ts loc mem_src))) (Memory.max_ts loc mem_src)).
          introv LE'.
          assert (LT_contr: Time.lt (Memory.max_ts loc mem_src)
                                    (Time.incr (Time.incr (Memory.max_ts loc mem_src)))).
          {
            cut (Time.lt (Memory.max_ts loc mem_src) (Time.incr (Memory.max_ts loc mem_src))). ii.
            cut (Time.lt (Time.incr (Memory.max_ts loc mem_src))
                         (Time.incr (Time.incr (Memory.max_ts loc mem_src)))). ii.
            auto_solve_time_rel.
            auto_solve_time_rel.
            auto_solve_time_rel.
          }
          auto_solve_time_rel.
          auto_solve_time_rel.
        }
        {
          econs; eauto.
        }
      }

      des.
      (* find increasing injection *)
      inv WRITABLE. inv WRITE0. inv PROMISE.
      exploit Memory.add_get0; [eapply MEM | eauto..]. ii. des1.
      assert (NEW: inj loc to = None).
      {
        clear - GET INV. ss. des. clear - GET INJ_MEM. inv INJ_MEM.
        destruct (inj loc to) eqn:INJ_LOC; eauto.
        exploit COMPLETE; eauto. ii; des.
        rewrite GET in x. ss.
      }
      exploit wf_inj_incr; [ | eapply NEW | eauto..].
      {
        simpl in INV. des. inv INJ_MEM; eauto.
      }
      {
        instantiate (1 := Time.incr (Time.incr (Memory.max_ts loc mem_src))).
        introv INJ_GET LT. clear - INJ_GET INV. ss. des.
        clear - INJ_MEM INJ_GET. inv INJ_MEM.
        exploit COMPLETE; eauto. ii; des. exploit SOUND; eauto. ii; des.
        rewrite INJ_GET in x0. inv x0.
        exploit Memory.max_ts_spec; [eapply x2 | eauto..]. ii; des.
        cut (Time.lt (Memory.max_ts loc mem_src) (Time.incr (Time.incr (Memory.max_ts loc mem_src)))).
        ii. auto_solve_time_rel.
        cut (Time.lt (Memory.max_ts loc mem_src) (Time.incr (Memory.max_ts loc mem_src))).
        ii.
        cut (Time.lt (Time.incr (Memory.max_ts loc mem_src))
                     (Time.incr (Time.incr (Memory.max_ts loc mem_src)))). ii.
        auto_solve_time_rel.
        eapply Time.incr_spec. eapply Time.incr_spec.        
      }
      {
        introv INJ_TO LT. clear - LT INJ_TO INV NXT MEM. ss. des.
        clear - INJ_MEM INJ_TO LT NXT MEM. inv INJ_MEM.
        exploit COMPLETE; eauto. ii; des.
        exploit Memory.add_get1; eauto. ii.
        eapply NXT in x1. clear - LT x1. auto_solve_time_rel.
      }

      assert (WRITEABLE': Time.lt (View.rlx (TView.cur tview_src) loc)
                                  (Time.incr (Memory.max_ts loc mem_src))).
      {
        clear - LOCAL_WF_SRC. inv LOCAL_WF_SRC; ss. inv TVIEW_CLOSED.
        inv CUR. unfold Memory.closed_timemap in RLX.
        specialize (RLX loc). des. eapply Memory.max_ts_spec in RLX. des.
        cut (Time.lt (Memory.max_ts loc mem_src) (Time.incr (Memory.max_ts loc mem_src))).
        ii. auto_solve_time_rel. auto_solve_time_rel.
      }

      ii. do 3 des1.
      exists (Time.incr (Memory.max_ts loc mem_src)) (Time.incr (Time.incr (Memory.max_ts loc mem_src))).
      do 3 eexists. exists Memory.op_kind_add inj'.
      splits.
      {
        econs; eauto.
        ss. clear - LOC LO. rewrite LOC in LO. ss. subst.
        ss.
        ss. econs; eauto.
        clear - WRITEABLE'.
        cut (Time.lt (Time.incr (Memory.max_ts loc mem_src))
                     (Time.incr (Time.incr (Memory.max_ts loc mem_src)))).
        ii. auto_solve_time_rel. auto_solve_time_rel.
        clear - LO LOC. rewrite LOC in LO. ss. subst.
        ii; tryfalse.
      }
      {
        ss. unfold TimeMap.singleton. unfold TimeMap.join.
        do 2 (rewrite Loc_add_eq).
        unfold Time.join. des_if.
        {
          des_if; eauto. rewrite NEW_INJ.
          des_if; ss. des; ss.
          clear - l0 WRITEABLE'.
          cut (Time.le (View.rlx (TView.cur tview_src) loc)
                       (Time.incr (Time.incr (Memory.max_ts loc mem_src)))).
          ii. clear - l0 H. auto_solve_time_rel.
          cut (Time.lt (Time.incr (Memory.max_ts loc mem_src))
                       (Time.incr (Time.incr (Memory.max_ts loc mem_src)))).
          ii. eapply Time.le_lteq. left. auto_solve_time_rel.
          eapply Time.incr_spec.
        }
        {
          clear - TS l.
          cut (Time.le (View.rlx (TView.cur tview_tgt) loc) to).
          ii. auto_solve_time_rel.
          eapply Time.le_lteq. left. auto_solve_time_rel.
        }
      }

      eauto. eauto. eauto. ii; ss.
      {
        simpl in INV. des. simpl; splits; eauto.

        (* TMapInj *)
        eapply incr_inj_TMapInj; eauto.
        eapply closed_tm_to_closed_TMapInj; eauto.

        (* MsgInj *)
        eapply add_msgInj_stable_concrete.
        {
          eapply INJ_MEM.
        }
        {
          eapply MEM.
        }
        {
          inv ADD. inv PROMISE. eauto.
        }
        {
          rewrite LOC in LO. simpl in LO. subst.
          unfold TView.write_released. ss.
        }
        eauto. eauto. subst. des_if; eauto. ss; des; ss.
        {
          rewrite NEW_INJ. introv INJ_GET. des_ifH INJ_GET. ss. des; subst.
          eapply Memory.add_get0 in MEM. des; eauto.
          simpl in o.
          clear - INJ_MEM INJ_GET MEM. 
          inv INJ_MEM. exploit COMPLETE; eauto. ii; des.
          exploit SOUND; eauto. ii; des. rewrite INJ_GET in x0. inv x0.
          eapply Memory.add_get1 in x; eauto.
        }
        eauto.
        {
          introv GET_SRC' INJ'_TO LT_BOT NON_ATOM_LOC.
          inv ADD. inv PROMISE.
          erewrite Memory.add_o in GET_SRC'; eauto.
          des_ifH GET_SRC'; eauto.
          {
            simpl in a. des1; subst. inv GET_SRC'.
            exists (Memory.max_ts loc mem_src). splits.
            eapply Time.incr_spec.
            introv ITV COVER. 
            eapply Cover.add_covered in COVER; eauto.
            des1.
            {
              clear - ITV COVER. inv COVER. inv ITV0; ss.
              inv ITV; ss. exploit Memory.max_ts_spec; eauto. ii; des.
              clear - TO FROM0 MAX.
              cut (Time.lt to ts). ii. auto_solve_time_rel. auto_solve_time_rel.
            }
            {
              des1; subst.
              clear - ITV COVER0. inv ITV; ss. inv COVER0; ss.
              clear - TO FROM0. auto_solve_time_rel.
            }
          }
          {
            simpl in o.
            des_ifH INJ'_TO. simpl in a. des1; subst. des1; tryfalse.
            simpl in o0.
            exploit TS_RSV; eauto. ii. do 2 des1.
            exists to_r. split. eauto.
            introv ITV COVER'. specialize (x0 ts).
            eapply x0; eauto.
            eapply Cover.add_covered in COVER'; eauto.
            des1; eauto. des1; subst. des1; tryfalse. des1; tryfalse.
            clear - GET_SRC' ITV COVER'0.
            exploit memory_get_ts_le; eauto. introv LE.
            eapply Memory.max_ts_spec in GET_SRC'; eauto. des.
            clear - MAX ITV COVER'0 LE. inv ITV; ss. inv COVER'0; ss.
            cut (Time.le from' (Time.incr (Memory.max_ts loc mem_src))).
            ii. clear - TO H FROM0.
            cut (Time.le ts (Time.incr (Memory.max_ts loc mem_src))). ii.
            clear - H0 FROM0. auto_solve_time_rel. auto_solve_time_rel.
            cut (Time.le from' (Memory.max_ts loc mem_src)). ii.
            cut (Time.lt (Memory.max_ts loc mem_src) (Time.incr (Memory.max_ts loc mem_src))). ii.
            eapply Time.le_lteq. left. auto_solve_time_rel.
            auto_solve_time_rel.
            auto_solve_time_rel.
          }
        }
        {
          introv GET_RSV. inv ADD. inv PROMISE.
          erewrite Memory.add_o in GET_RSV; eauto.
          des_ifH GET_RSV; eauto.
          simpl in a. des1; subst. inv GET_RSV.
        }
        {
          introv LOC_ATOMIC INJ'_TO.
          rewrite NEW_INJ in INJ'_TO. des_ifH INJ'_TO; eauto.
          simpl in a. des1; subst. rewrite LOC in LOC_ATOMIC. ss.
        }

        (* closed memory *)
        inv ADD. inv PROMISE.
        eapply Memory.add_closed; eauto.
      }
      ii; eauto. ss.
    }     
  - (* memory split *) 
    inv WRITE0. inv PROMISE. do 4 des1. subst. inv RESERVE.
    exploit Memory.split_get0; [eapply MEM | eauto..]. ii. do 3 des1.
    simpl in INV. do 5 des1.
    assert (NXT_SRC: exists ts3' f_s val_s R_s,
               Memory.get loc ts3' mem_src = Some (f_s, Message.concrete val_s R_s) /\
               inj loc ts3 = Some ts3').
    {
      clear - INJ_MEM GET0.
      inv INJ_MEM. exploit SOUND; eauto. ii; des; eauto.
      do 4 eexists. eauto.
    }
    do 5 des1.
    exploit split_succeed_wf; eauto. ii; do 3 des1. clear GET3 MSG_WF.

    (* find unused timestamp *)
    exploit TS_RSV; [eapply NXT_SRC | eauto..].
    {
      clear - TS23 GET0. eapply Memory.get_ts in GET0. des; subst.
      auto_solve_time_rel. pose proof (Time.bot_spec ts3).
      eapply Time.le_lteq in H. des; eauto. subst. auto_solve_time_rel.
    }
    introv Unused_Timestamps. do 2 des1.
    (* do source write *) 
    assert (ADD: exists mem_src',
               Memory.write prm_src mem_src loc (Time.middle to_r (Time.middle to_r f_s))
                            (Time.middle to_r f_s) val'0 None
                            prm_src mem_src' Memory.op_kind_add).
    {
      eapply write_succeed_valid; eauto.
      {
        inv LOCAL_WF_SRC; eauto.
      }
      {
        introv COVER ITV. specialize (Unused_Timestamps0 t).
        eapply Unused_Timestamps0; eauto. inv ITV. ss. econs; eauto. ss.
        pose proof (Time.middle_spec Unused_Timestamps).  des.
        eapply Time.middle_spec in H. des. clear - FROM H. auto_solve_time_rel.
        eapply Time.le_lteq. left; ss.
        eapply Time.middle_spec in Unused_Timestamps. des. auto_solve_time_rel.
      }
      {
        ss. unfold TimeMap.bot. eapply Time.bot_spec.
      }
      {
        eapply Time.middle_spec in Unused_Timestamps. des; eauto.
        eapply Time.middle_spec in Unused_Timestamps. des; eauto.
      }
      {
        introv ATTACH. eapply RSV_ITV_insert_middle_not_attach in ATTACH; eauto.
      }
      {
        econs; eauto.
      }
    }
    des1.
    assert (WRITEABLE': Time.le (View.rlx (TView.cur tview_src) loc) to_r).
    {
      eapply TM_src_view_le_unused_timestamps; eauto.
      clear - LOCAL_WF_SRC. inv LOCAL_WF_SRC; ss. inv TVIEW_CLOSED. inv CUR; eauto.
      clear - WRITABLE TS23. inv WRITABLE. auto_solve_time_rel.
    }

    (* find increasing injection *)
    assert (NEW: inj loc to = None).
    {
      clear - GET INJ_MEM. destruct (inj loc to) eqn:INJ_LOC; eauto.
      inv INJ_MEM. exploit COMPLETE; eauto. ii; des.
      rewrite GET in x. ss.
    }
    exploit wf_inj_incr; [ | eapply NEW | eauto..].
    {
      inv INJ_MEM; eauto.
    }
    {
      inv ADD. inv PROMISE.
      instantiate (1 := Time.middle to_r f_s). introv INJ_ORIGN LT.
      {
        inv INJ_MEM. exploit COMPLETE; [eapply INJ_ORIGN | eauto..]. ii; des.
        exploit SOUND; eauto. ii; des. rewrite INJ_ORIGN in x0. symmetry in x0. inv x0.
        exploit inj_src_view_le_unused_timestamps; [eapply INJ_ORIGN | eapply x2 | eapply NXT_SRC | eauto..].
        auto_solve_time_rel.
        introv LE.
        eapply Time.middle_spec in Unused_Timestamps. des. auto_solve_time_rel.
      }
    } 
    {
      introv INJ LT.
      destruct (Time.le_lt_dec ts3 ts).
      {
        inv INJ_MEM. 
        exploit monotonic_inj_implies_le_prsv; [eapply MONOTONIC | eapply l | eauto..].
        introv LE'. clear - LE' NXT_SRC Unused_Timestamps.
        eapply memory_get_ts_le in NXT_SRC. eapply Time.middle_spec in Unused_Timestamps. des.
        cut (Time.le f_s ts'). ii. auto_solve_time_rel.
        clear - NXT_SRC LE'. auto_solve_time_rel.
      }
      {
        clear - LT l INJ INJ_MEM TS12 TS23 GET0. inv INJ_MEM.
        exploit COMPLETE; [eapply INJ | eauto..]. ii; des. clear SOUND COMPLETE.
        exploit Memory.get_disjoint; [eapply GET0 | eapply x | eauto..]. ii; des; subst.
        auto_solve_time_rel. unfold Interval.disjoint in x1.
        specialize (x1 ts). contradiction x1; eauto.
        econs; ss; eauto. clear - TS12 LT. auto_solve_time_rel.
        econs; eauto.
        econs; ss; eauto.
        eapply Memory.get_ts in x. des; subst. auto_solve_time_rel. eauto.
        eapply Time.le_lteq. eauto.
      }
    }
    introv NEW_INJ. do 3 des1.

    do 2 eexists. exists (TView.write_tview tview_src sc_src loc (Time.middle to_r f_s) ord).
    do 3 eexists. exists inj'.
    splits.
    {
      econs; eauto.
      rewrite LOC in LO. simpl in LO. subst.
      simpl. econs.
      ss. econs; eauto. eapply Time.middle_spec in Unused_Timestamps. des. auto_solve_time_rel.
      rewrite LOC in LO. simpl in LO. subst.
      ii; ss.
    }
    {
      inv WRITABLE. 
      exploit write_cur_view_to; [eapply TS0 | eauto..].
      inv LOCAL_WF_TGT; eauto. instantiate (1 := ord). instantiate (1 := sc_tgt).
      ii. des. rewrite VIEW_CUR_RLX.
      cut (Time.lt (View.rlx (TView.cur tview_src) loc) (Time.middle to_r f_s)). introv WRITEABLE_SRC.
      exploit write_cur_view_to; [eapply WRITEABLE_SRC | eauto..].
      inv LOCAL_WF_SRC; eauto. instantiate (1 := ord). instantiate (1 := sc_src).
      ii. des. rewrite VIEW_CUR_RLX0.
      des_if; eauto. ss. des; ss.
      eapply Time.middle_spec in Unused_Timestamps. des.
      auto_solve_time_rel.
    }
    eauto. eauto. eauto. ii; eauto.
    {
      ss. splits; eauto.

      (* TMapInj *)
      eapply incr_inj_TMapInj; eauto.
      eapply closed_tm_to_closed_TMapInj; eauto.

      (* Msginj *)
      eapply split_add_msgInj_stable_concrete; eauto.
      inv ADD. inv PROMISE; eauto.
      unfold TView.write_released. rewrite LOC in LO. simpl in LO. subst ord.
      ss.
      subst. des_if; eauto. ss. des; ss.
      ii. rewrite NEW_INJ0 in H. des_ifH H; eauto.
      simpl in a. des; subst. inv H. eauto.
      simpl in o. clear - MEM H INJ_MEM. inv INJ_MEM.
      exploit COMPLETE; eauto. ii; des.
      eapply Memory.split_get1 in x; eauto. des; eauto.

      (* Unused timestamps *)
      introv GET_SRC INJ'_GET LT' NON_ATOMIC_LOC.
      inv ADD. inv PROMISE. erewrite Memory.add_o in GET_SRC; eauto.
      des_ifH GET_SRC.
      { 
        simpl in a. des; subst. inv GET_SRC.
        exists to_r. split. eapply Time.middle_spec in Unused_Timestamps. des.
        eapply Time.middle_spec in Unused_Timestamps. des; eauto. 
        clear - Unused_Timestamps Unused_Timestamps0 MEM0.
        introv ITV COVER. specialize (Unused_Timestamps0 ts).
        eapply Unused_Timestamps0; eauto.
        inv ITV. ss. econs; eauto. ss.
        eapply Time.middle_spec in Unused_Timestamps. des.
        eapply Time.middle_spec in Unused_Timestamps. des.
        clear - TO Unused_Timestamps2 Unused_Timestamps1.
        econs. cut (Time.lt ts  (Time.middle to_r f_s)). ii.
        auto_solve_time_rel. auto_solve_time_rel.
        eapply Cover.add_covered in COVER; eauto. des; eauto.
        clear - Unused_Timestamps ITV COVER0.
        inv ITV. ss. inv COVER0; ss.
        auto_solve_time_rel.
      }
      {
        simpl in o. des_ifH INJ'_GET; eauto.
        simpl in a. des; subst; ss. inv INJ'_GET. ss.
        destruct (Loc.eq_dec loc loc0); subst.
        {
          (* same location *)
          des1; ss. des1; ss.
          destruct (Time.eq_dec to0 ts3); subst.
          {
            rewrite NXT_SRC0 in INJ'_GET. inv INJ'_GET.
            rewrite NXT_SRC in GET_SRC. inv GET_SRC.
            exists (Time.middle to_r from'). split. eapply Time.middle_spec in Unused_Timestamps.
            des; eauto.
            introv ITV COVER. specialize (Unused_Timestamps0 ts).
            eapply Unused_Timestamps0; eauto. econs; eauto. ss.
            eapply Time.middle_spec in Unused_Timestamps. des.
            inv ITV; ss. auto_solve_time_rel.
            ss. inv ITV; ss.
            eapply Cover.add_covered in COVER; eauto. des1; eauto.
            des1. clear - ITV COVER0. inv ITV; ss. inv COVER0; ss.
            auto_solve_time_rel.
          }
          {
            destruct (Time.le_lt_dec to0 ts3).
            {
              eapply Time.le_lteq in l. des; subst; ss.
              exploit inj_src_view_le_unused_timestamps;
                [eapply INJ'_GET | eapply GET_SRC | eapply NXT_SRC | eapply NXT_SRC0 | eauto..].
              inv INJ_MEM; eauto.
              introv LE. exploit TS_RSV; [eapply GET_SRC | eauto..]. ii; des.
              exists to_r0. split; eauto. introv ITV' COVER. specialize (x0 ts).
              eapply x0; eauto.
              eapply Cover.add_covered in COVER; eauto. des; eauto.
              clear - GET_SRC LE ITV' COVER0 Unused_Timestamps. inv COVER0; ss.
              eapply memory_get_ts_le in GET_SRC. clear TO. inv ITV'; ss. clear FROM0.
              eapply Time.middle_spec in Unused_Timestamps. des. clear Unused_Timestamps0.
              eapply Time.middle_spec in Unused_Timestamps. des. clear Unused_Timestamps0.
              cut (Time.lt ts (Time.middle to_r (Time.middle to_r f_s))).
              ii. auto_solve_time_rel. ii; auto_solve_time_rel.
              clear - TO GET_SRC LE Unused_Timestamps.
              cut (Time.le ts to_r). ii. auto_solve_time_rel.
              cut (Time.le ts to'). ii. auto_solve_time_rel. auto_solve_time_rel.
            }
            {
              exploit TS_RSV; [eapply GET_SRC | eauto..]. ii; des.
              exploit inj_src_view_le_unused_timestamps;
                [eapply NXT_SRC0 | eapply NXT_SRC | eapply GET_SRC | eauto..].
              inv INJ_MEM; eauto. introv LE.
              exists to_r0. split; eauto. introv ITV' COVER. specialize (x0 ts).
              eapply x0; eauto.
              eapply Cover.add_covered in COVER; eauto. des; eauto.
              clear - NXT_SRC Unused_Timestamps LE ITV' COVER0.
              inv ITV'; ss. clear TO. inv COVER0; ss. clear FROM0.
              cut (Time.le ts to_r0). ii. auto_solve_time_rel.
              cut (Time.le ts ts3'). ii. auto_solve_time_rel.
              eapply memory_get_ts_le in NXT_SRC.
              cut (Time.le ts f_s). ii. auto_solve_time_rel.
              eapply Time.middle_spec in Unused_Timestamps. des.
              econs. auto_solve_time_rel.
            }
          }
        }
        {
          (* disjoint loc *)
          exploit TS_RSV; eauto. ii. do 2 des1.
          exists to_r0. split; eauto.
          introv ITV COVER. specialize (x0 ts). eapply x0; eauto.
          eapply Cover.add_covered in COVER; eauto. des1; eauto.
          des1; subst. des1; ss.
        }
      }

      (* reservation preservation *)
      clear - ADD NO_RSVs. introv GET. inv ADD. inv PROMISE.
      erewrite Memory.add_o in GET; eauto. des_ifH GET; eauto.
      ss.

      (* Identity injection on atomic location *)
      clear - NEW_INJ0 ID_ATOMIC LOC. ii. subst.
      des_ifH H0; eauto. ss. des; subst; ss. tryfalse.

      (* closed memory *)
      inv ADD. inv PROMISE.
      eapply Memory.add_closed; eauto.
    }
 
    ii; ss. specialize (H ts3 val' released'). contradiction H; eauto.
  - (* memory lower *)
    inv WRITE0. inv PROMISE. des. subst.
    rewrite LOC in LO. simpl in LO. subst.
    exploit Memory.lower_get0; [eapply PROMISES | eauto..].
    ii. do 2 des1.
    assert (GET': exists from' to' released',
               Memory.get loc to' prm_src = Some (from', Message.concrete val0 released') /\
               inj loc to = Some to' /\
               opt_ViewInj inj released released').
    {
      clear - GET MEM LOCAL_WF_TGT LOCAL_WF_SRC INV PRM_REL.
      inv LOCAL_WF_TGT. ss. des. exploit PROMISES; eauto. ii.
      unfold promises_relation in PRM_REL. des. inv PRM_REL.
      exploit SOUND2; eauto. ii; des.
      inv INJ_MEM. exploit COMPLETE0; eauto. ii; des.
      exploit SOUND; eauto. ii; des. rewrite x0 in x3. symmetry in x3. inv x3.
      inv LOCAL_WF_SRC. ss. exploit PROMISES0; eauto. ii.
      rewrite x5 in x3. inv x3.
      rewrite x in x2. inv x2.
      do 3 eexists. splits; eauto.
    }
    destruct GET' as (from' & to' & released' & GET' & INJ_TO & OPT_VIEWINJ).
    assert (GET_MEM': Memory.get loc to' mem_src = Some (from', Message.concrete val0 released')).
    {
      clear - LOCAL_WF_SRC GET'. inv LOCAL_WF_SRC; ss. eauto.
    }
    assert (LT_ITV: Time.lt from' to').
    {
      clear - GET' PRM_CONS.
      unfold Local.promise_consistent in *. ss.
      exploit PRM_CONS; eauto. ii.
      eapply Memory.get_ts in GET'; eauto. des; subst; ss.
      auto_solve_time_rel.
    }

    exploit Memory.lower_exists; [eapply GET' | eauto..].
    econs; eauto.
    introv LOWER_PRM'. destruct LOWER_PRM' as (prm_src' & LOWER_PRM').
    exploit Memory.lower_exists; [eapply GET_MEM' | eauto..].
    econs; eauto.
    introv LOWER_MEM'. destruct LOWER_MEM' as (mem_src' & LOWER_MEM').

    assert (REMOVE_PRM': exists prm_src'', Memory.remove prm_src' loc from' to' (Message.concrete val0 None) prm_src'').
    {
      eapply Memory.remove_exists; eauto.
      eapply Memory.lower_get0 in LOWER_PRM'. des; eauto.
    }
    destruct REMOVE_PRM' as (prm_src'' & REMOVE_PRM').

    assert (WRITEABLE': Time.lt (View.rlx (TView.cur tview_src) loc) to').
    {
      clear - TM_H INJ_TO WRITABLE. 
      inv TM_H. inv WRITABLE. eauto.
    }

    inv MSG_LE.
    exists from' to'. eexists. exists prm_src'' mem_src' (Memory.op_kind_lower (Message.concrete val0 released')) inj.
    splits.
    {
      econs; ss; eauto.
      rewrite LOC. ss.
      econs; eauto. econs; eauto.
      econs; eauto. ss. unfold TimeMap.bot. eapply Time.bot_spec; eauto.      
    }
    {
      unfold TView.write_tview; ss. destruct tview_tgt, tview_src; ss.
      unfold TimeMap.singleton; ss. unfold TimeMap.join.
      do 2 (rewrite Loc_add_eq); eauto. unfold Time.join.
      des_if; ss. des_if; eauto. clear - WRITEABLE' l0.
      assert (LE: Time.le to' (View.rlx cur0 loc)). econs; eauto.
      auto_solve_time_rel.
      clear - l WRITABLE. inv WRITABLE.
      assert (LE: Time.le to (View.rlx cur loc)). econs; eauto.
      auto_solve_time_rel.
    }
    {
      eapply functional_extensionality; eauto. ii.
      eapply functional_extensionality; eauto. ii.
      des_if; ss; eauto. des; subst. eauto.
    }
    unfold incr_inj; ii; eauto. simpl in INV; ss. des. inv INJ_MEM; eauto.
    ii; ss.
    {
      simpl in INV. des.
      ss. splits; eauto.
      eapply lower_msgInj_stable_concrete with (inj' := inj); eauto.
      unfold TView.write_released; ss.
      unfold incr_inj; ss; eauto.
      inv INJ_MEM; des; eauto.
      inv INJ_MEM; eauto. introv INJ. exploit COMPLETE; eauto. introv GET''. des.
      eapply Memory.lower_get1 in GET''; eauto. des; eauto. destruct m'; ss; eauto.
      inv MSG_LE.

      introv MSG_SRC_GET INJ LT NON_ATOMIC.
      erewrite Memory.lower_o in MSG_SRC_GET; eauto.
      des_ifH MSG_SRC_GET; eauto. simpl in a. des; subst.
      inv MSG_SRC_GET. inv INJ_MEM.
      exploit COMPLETE; eauto. ii; des. exploit SOUND; eauto. ii; des.
      rewrite INJ in x0. symmetry in x0. inv x0.
      exploit TS_RSV; eauto. ii; des.
      exists to_r. rewrite GET_MEM' in x2. inv x2. split; eauto.
      introv ITV COVER'. specialize (x3 ts). eapply x3; eauto.
      eapply Cover.lower_covered with (mem2 := mem_src'); eauto.
      exploit TS_RSV; eauto. ii. do 2 des1.
      exists to_r. split; eauto.
      introv ITV COVER'. specialize (x0 ts). eapply x0; eauto.
      eapply Cover.lower_covered with (mem2 := mem_src'); eauto.

      introv GET_RSV. erewrite Memory.lower_o in GET_RSV; eauto.
      des_ifH GET_RSV; ss. eauto.

      eapply Memory.lower_closed; eauto.
      econs; eauto. ss. unfold TimeMap.bot. eapply Time.bot_spec; eauto.
    }
    ii; ss.
  - (* memory remove: contradiction *)
    inv WRITE0. inv PROMISE; ss.
Qed.

Lemma InvView_dce_write
      tview_tgt sc_tgt loc to
      tview_src sc_src to' ow mem_src mem_src' inj inj' lo
      (INV_VIEW: InvView_dce inj lo tview_tgt tview_src mem_src)
      (WRITEABLE_TGT: Time.lt (View.rlx (TView.cur tview_tgt) loc) to)
      (WRITEABLE_SRC: Time.lt (View.rlx (TView.cur tview_src) loc) to')
      (MON_INJ: monotonic_inj inj')
      (INCR_INJ: incr_inj inj inj')
      (INJ_TO: inj' loc to = Some to')
      (DIS_INJ: forall loc0 to0, (loc <> loc0 \/ to <> to0) -> inj loc0 to0 = inj' loc0 to0)
      (MEM_EQ: forall loc0, loc <> loc0 -> (mem_src loc0) = (mem_src' loc0))
      (CUR_ACQ: cur_acq lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                        (TView.cur tview_src) (TView.acq tview_src))
      (CLOSED_TVIEW_TGT: closed_tviewInj inj tview_tgt)
      (VIEW_INJ_CUR: Ordering.le Ordering.acqrel ow ->  ViewInj inj (TView.cur tview_tgt) (TView.cur tview_src)):
  InvView_dce inj' lo
              (TView.write_tview tview_tgt sc_tgt loc to ow)
              (TView.write_tview tview_src sc_src loc to' ow) mem_src'.
Proof.
  inv INV_VIEW.
  unfold TView.write_tview; ss.
  econs; eauto; simpl; (unfold TimeMap.join, TimeMap.singleton; simpls).
  - introv AT_LOC.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      repeat (rewrite Loc_add_eq; eauto).
      exploit ATM_LOC_ACQ_PLN; eauto. ii. eapply INCR_INJ in x.
      eapply inj_join_comp; eauto.
    }
    {
      repeat (rewrite Loc_add_neq; eauto).
      unfold LocFun.init; ss. repeat (rewrite Time_join_bot). eauto.
    }
  - introv AT_LOC.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      repeat (rewrite Loc_add_eq; eauto).
      exploit ATM_LOC_ACQ_RLX; eauto. ii. eapply INCR_INJ in x.
      eapply inj_join_comp; eauto.
    }
    {
      repeat (rewrite Loc_add_neq; eauto).
      unfold LocFun.init; ss. repeat (rewrite Time_join_bot). eauto.
    }
  - introv NA_LOC. exploit NA_LOC_CUR_RLX; eauto. ii.
    inv x.
    econs; eauto.
    {
      ii.
      destruct (Loc.eq_dec loc loc0); subst.
      {
        repeat (rewrite Loc_add_eq in *; ss).
        rewrite TimeFacts.le_join_r in H2.
        rewrite TimeFacts.le_join_r; eauto.
        econs; eauto. econs; eauto.
      }
      {
        unfold TimeMap.join, TimeMap.singleton in *; ss.
        repeat (rewrite Loc_add_neq in *; eauto; ss).
        repeat (rewrite Time_join_bot in *; ss).
        exploit DIS_INJ; eauto. instantiate (1 := to0). ii.
        rewrite H1 in x. eauto.
      }
    }
    {
      des.
      destruct (Loc.eq_dec loc loc0); subst.
      {
        repeat (rewrite Loc_add_eq; eauto). exists to'.
        repeat (rewrite TimeFacts.le_join_r in *). splits; eauto.
        eapply Time.le_lteq; eauto.
        ii. inv H3; ss. auto_solve_time_rel.
        econs; eauto. econs; eauto.
      }
      {
        repeat (rewrite Loc_add_neq; eauto).
        unfold LocFun.init; ss.
        repeat (rewrite Time_join_bot in *); eauto.
        exists to'0.
        splits; eauto.
        ii. eapply H2 in H3. inv H3.
        econs; eauto.
        unfold Memory.get in *. rewrite <- MEM_EQ; eauto.
      }
    }
  - introv AT_LOC.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      repeat (rewrite Loc_add_eq; eauto).
      exploit ATM_LOC_ACQ_PLN; eauto. ii. eapply INCR_INJ in x.
      eapply inj_join_comp; eauto.
    }
    {
      repeat (rewrite Loc_add_neq; eauto).
      unfold LocFun.init; ss. repeat (rewrite Time_join_bot). eauto.
    }
  - introv AT_LOC.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      repeat (rewrite Loc_add_eq; eauto).
      exploit ATM_LOC_ACQ_PLN; eauto. ii. eapply INCR_INJ in x.
      eapply inj_join_comp; eauto.
    }
    {
      repeat (rewrite Loc_add_neq; eauto).
      unfold LocFun.init; ss. repeat (rewrite Time_join_bot). eauto.
    }
  - introv NA_LOC. econs; eauto.
    {
      destruct (Loc.eq_dec loc loc0); subst.
      {
        repeat (rewrite Loc_add_eq; eauto).
        ii. unfold cur_acq in CUR_ACQ. exploit CUR_ACQ; eauto. ii; des.
        {
          eapply Time_lt_join in H0. des.
          eapply lt_lt_join; eauto.
        }
        {
          rewrite <- EQ0. rewrite <- EQ in H0. clear EQ EQ0.
          exploit NA_LOC_CUR_RLX; eauto. ii. inv x. des.
          eapply Time_lt_join in H0. des.
          eapply lt_lt_join; eauto.
          eapply H1 in H0; eauto. rewrite DIS_INJ; eauto. right; ii; subst. auto_solve_time_rel.
        }
      }
      {
        repeat (rewrite Loc_add_neq; eauto).
        unfold LocFun.init; ss. repeat (rewrite Time_join_bot; eauto).
        ii. exploit NA_LOC_CUR_RLX0; eauto. ii.
        inv x. des. eapply H1; eauto. rewrite DIS_INJ; eauto.
      }
    }
    {
      destruct (Loc.eq_dec loc loc0); subst.
      {
        repeat (rewrite Loc_add_eq; eauto).
        unfold cur_acq in CUR_ACQ. exploit CUR_ACQ; eauto. ii; des.
        exists (Time.join (View.rlx (TView.acq tview_src) loc0) to').
        splits; eauto. eapply inj_join_comp; eauto.
        eapply Time.le_lteq. eauto. introv ITV. inv ITV; ss. auto_solve_time_rel.
        rewrite <- EQ, <- EQ0. exists to'.
        repeat (rewrite TimeFacts.le_join_r; eauto).
        splits; eauto. eapply Time.le_lteq; eauto.
        introv ITV. inv ITV; ss. auto_solve_time_rel.
        econs; eauto. econs; eauto.
      }
      {
        repeat (rewrite Loc_add_neq; eauto).
        unfold LocFun.init. repeat (rewrite Time_join_bot; eauto).
        exploit NA_LOC_CUR_RLX0; eauto. ii. inv x. des.
        exists to'0. splits; eauto. ii. eapply H2 in H3. inv H3. econs; eauto.
        unfold Memory.get in *; ss. rewrite <- MEM_EQ; eauto.
      }
    }
  - introv AT_LOC. exploit ATM_LOC_REL; eauto. ii. 
    des_if.
    {
      destruct (Loc.eq_dec loc loc0); subst.
      {
        unfold closed_tviewInj in *. des. eauto.
        repeat (rewrite Loc_add_eq).
        eapply Monotonic_viewInj_join_singleton; eauto.
        eapply incr_inj_closedViewInj; eauto.
        exploit VIEW_INJ_CUR; eauto. ii.
        eapply incr_inj_ViewInj; eauto.
      }
      {
        unfold closed_tviewInj in *. des. eauto.
        repeat (rewrite Loc_add_neq; eauto).
        eapply incr_inj_ViewInj; eauto.
      }
    }
    {
      destruct (Loc.eq_dec loc loc0); subst.
      {
        unfold closed_tviewInj in *. des. eauto.
        repeat (rewrite Loc_add_eq).
        eapply Monotonic_viewInj_join_singleton; eauto.
        eapply incr_inj_closedViewInj; eauto.
        eapply incr_inj_ViewInj; eauto.
      }
      {
        unfold closed_tviewInj in *. des. eauto.
        repeat (rewrite Loc_add_neq; eauto).
        eapply incr_inj_ViewInj; eauto.
      }
    }
Qed.

Lemma cur_acq_write_prsv
      lo inj inj' tview_tgt sc_tgt tview_src sc_src loc to to' ow
      (CUR_ACQ: cur_acq lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                        (TView.cur tview_src) (TView.acq tview_src))
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj')
      (WRITEABLE_TGT: Time.lt (View.rlx (TView.cur tview_tgt) loc) to)
      (WRITEABLE_SRC: Time.lt (View.rlx (TView.cur tview_src) loc) to')
      (INJ_TO: inj' loc to = Some to'):
  cur_acq lo inj' (TView.cur (TView.write_tview tview_tgt sc_tgt loc to ow))
          (TView.acq (TView.write_tview tview_tgt sc_tgt loc to ow))
          (TView.cur (TView.write_tview tview_src sc_src loc to' ow))
          (TView.acq (TView.write_tview tview_src sc_src loc to' ow)).                
Proof.
  unfold TView.write_tview; ss.
  unfold cur_acq in *; ss. ii. exploit CUR_ACQ; eauto. ii; des.
  - unfold TimeMap.join, TimeMap.singleton; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      repeat (rewrite Loc_add_eq; eauto).
      destruct (Time.le_lt_dec (View.rlx (TView.acq tview_tgt) loc0) to).
      {
        right. repeat (rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto).
        eapply monotonic_inj_implies_le_prsv in l; eauto.
        econs; eauto.
        econs; eauto.        
      }
      {
        left.
        rewrite DenseOrder.DenseOrderFacts.le_join_r.
        rewrite DenseOrder.DenseOrderFacts.le_join_l.
        splits; eauto.
        rewrite DenseOrder.DenseOrderFacts.le_join_l. eauto.
        econs; eauto.
        econs; eauto. econs; eauto.
      }
    }
    {
      repeat (rewrite Loc_add_neq; eauto).
      unfold LocFun.init; ss. repeat (rewrite Time_join_bot; eauto).
    }
  - unfold TimeMap.join, TimeMap.singleton; ss.
    rewrite <- EQ, <- EQ0.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      repeat (rewrite Loc_add_eq; eauto).
    }
    {
      repeat (rewrite Loc_add_neq; eauto).
    }
Qed.

Lemma cur_acq_pln_write_prsv
      lo inj inj' tview_tgt sc_tgt tview_src sc_src loc to to' ow
      (CUR_ACQ: cur_acq_pln lo inj (TView.cur tview_tgt) (TView.acq tview_tgt)
                            (TView.cur tview_src) (TView.acq tview_src))
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj')
      (WRITEABLE_TGT: Time.lt (View.rlx (TView.cur tview_tgt) loc) to)
      (WRITEABLE_SRC: Time.lt (View.rlx (TView.cur tview_src) loc) to')
      (INJ_TO: inj' loc to = Some to'):
  cur_acq_pln lo inj' (TView.cur (TView.write_tview tview_tgt sc_tgt loc to ow))
              (TView.acq (TView.write_tview tview_tgt sc_tgt loc to ow))
              (TView.cur (TView.write_tview tview_src sc_src loc to' ow))
              (TView.acq (TView.write_tview tview_src sc_src loc to' ow)).                
Proof.
  unfold TView.write_tview; ss.
  unfold cur_acq_pln in *; ss. ii. exploit CUR_ACQ; eauto. ii; des.
  - unfold TimeMap.join, TimeMap.singleton; ss.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      repeat (rewrite Loc_add_eq; eauto). 
      destruct (Time.le_lt_dec to (View.pln (TView.acq tview_tgt) loc0)).
      {
        eapply Time.le_lteq in l. des; subst.
        {
          left.
          rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto.
          rewrite DenseOrder.DenseOrderFacts.le_join_l; eauto.
          splits; eauto.
          rewrite DenseOrder.DenseOrderFacts.le_join_l; eauto.
          econs; eauto. econs; eauto. econs; eauto.
        }
        {
          right. split; eauto. 
          rewrite DenseOrder.DenseOrderFacts.le_join_r with
              (lhs := (View.rlx (TView.cur tview_tgt) loc0)); eauto.
          eapply Time.join_spec; eauto.
          eapply Time.le_lteq; eauto. eapply Time.le_lteq; eauto.
          eapply Time.le_lteq; eauto.
          eapply INCR_INJ in LT0. rewrite INJ_TO in LT0. inv LT0.
          eapply Time.join_spec; eauto.
          rewrite Time.join_comm. eapply le_join; eauto.
          eapply Time.le_lteq; eauto.
          rewrite Time.join_comm. eapply le_join; eauto.
          eapply Time.le_lteq; eauto.
        }
      }
      {
        right.
        repeat (rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto).
        split. eapply Time.le_lteq; eauto. eapply Time.le_lteq; eauto.
        econs; eauto. econs; eauto. econs; eauto. econs; eauto.
      }
    }
    {
      repeat (rewrite Loc_add_neq; eauto).
      unfold LocFun.init; ss. repeat (rewrite Time_join_bot; eauto).
    }
  - unfold TimeMap.join, TimeMap.singleton; ss.
    right.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      repeat (rewrite Loc_add_eq; eauto).
      repeat (rewrite DenseOrder.DenseOrderFacts.le_join_r; eauto; try solve [econs; eauto]).
      splits; (eapply Time.le_lteq; eauto).
      econs; eauto. auto_solve_time_rel.
      econs; eauto. auto_solve_time_rel.
    }
    {
      repeat (rewrite Loc_add_neq; eauto).
      unfold LocFun.init. repeat (rewrite Time_join_bot; eauto).
    }
Qed.

Lemma InvView_dce_at_loc
      inj lo tview_tgt tview_src mem_src loc
      (INV_VIEW: InvView_dce inj lo tview_tgt tview_src mem_src)
      (AT_LOC: lo loc = Ordering.atomic):
  <<CUR_PLN_INJ: inj loc (View.pln (TView.cur tview_tgt) loc) = Some (View.pln (TView.cur tview_src) loc)>> /\
  <<CUR_RLX_INJ: inj loc (View.rlx (TView.cur tview_tgt) loc) = Some (View.rlx (TView.cur tview_src) loc)>> /\
  <<ACQ_PLN_INJ: inj loc (View.pln (TView.acq tview_tgt) loc) = Some (View.pln (TView.acq tview_src) loc)>> /\
  <<ACQ_RLX_INJ: inj loc (View.rlx (TView.acq tview_tgt) loc) = Some (View.rlx (TView.acq tview_src) loc)>>.
Proof.
  inv INV_VIEW.
  exploit ATM_LOC_CUR_PLN; eauto. ii.
  exploit ATM_LOC_CUR_RLX; eauto. ii.
  exploit ATM_LOC_ACQ_PLN; eauto. ii.
  exploit ATM_LOC_ACQ_RLX; eauto.
Qed.

(** * promises relation lemmas *)
Lemma mem_split_rsv
      prm loc ts1 ts2 ts3 val R val' R' prm'
      (SPLIT: Memory.split prm loc ts1 ts2 ts3 (Message.concrete val R) (Message.concrete val' R') prm'):
  (forall t f loc, Memory.get loc t prm = Some (f, Message.reserve) <->
              Memory.get loc t prm' = Some (f, Message.reserve)).
Proof.
  ii. split; ii.
  - erewrite Memory.split_o; eauto.
    des_if; ss. des1; subst.
    exploit Memory.split_get0; eauto. ii; des.
    rewrite H in GET. ss.
    des_if; ss. des1; subst. des1; ss.
    exploit Memory.split_get0; eauto. ii; des.
    rewrite H in GET0. ss.
  - erewrite Memory.split_o in H; eauto.
    des_ifH H; ss.
    des_ifH H; ss.
Qed.

Lemma mem_lower_rsv
      prm loc from to val R msg prm'
      (SPLIT: Memory.lower prm loc from to (Message.concrete val R) msg prm'):
  (forall t f loc, Memory.get loc t prm = Some (f, Message.reserve) <->
              Memory.get loc t prm' = Some (f, Message.reserve)).
Proof.
  ii. split; ii.
  - erewrite Memory.lower_o; eauto.
    des_if; ss. des1; subst.
    exploit Memory.lower_get0; eauto. ii; des.
    rewrite H in GET. ss.
  - erewrite Memory.lower_o in H; eauto.
    des_ifH H; ss. des1; subst.
    exploit Memory.lower_get0; eauto. ii; des. inv MSG_LE. ss.
Qed.

Lemma mem_remove_concrete_rsv
      prm loc from to val R prm'
      (SPLIT: Memory.remove prm loc from to (Message.concrete val R) prm'):
  (forall t f loc, Memory.get loc t prm = Some (f, Message.reserve) <->
              Memory.get loc t prm' = Some (f, Message.reserve)).
Proof.
  ii. split; ii.
  - erewrite Memory.remove_o; eauto.
    des_if; ss. des1; subst.
    exploit Memory.remove_get0; eauto. ii; des.
    rewrite H in GET. ss.
  - erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss. 
Qed.

Lemma write_split_prm_prop
      prm mem loc from to val R prm' mem' ts val' R'
      (WRITE: Memory.write prm mem loc from to val R prm' mem'
                           (Memory.op_kind_split ts (Message.concrete val' R'))):
  (forall val0 R0 t f loc, Memory.get loc t prm = Some (f, Message.concrete val0 R0) ->
                      exists f', Memory.get loc t prm' = Some (f', Message.concrete val0 R0)) /\
  (forall val0 R0 t f' loc, Memory.get loc t prm' = Some (f', Message.concrete val0 R0) ->
                       exists f, Memory.get loc t prm = Some (f, Message.concrete val0 R0)).
Proof.
  split; ii.
  - inv WRITE. inv PROMISE; ss. des; subst. inv RESERVE. inv RESERVEORIGINAL.
    lets GET: H.
    eapply Memory.split_get1 in H; eauto. des.
    eapply Memory.remove_get1 in GET2; eauto. des; subst; eauto.
    clear MEM. exploit Memory.split_get0; eauto. ii; des.
    rewrite GET in GET0. ss.
  - inv WRITE. inv PROMISE; ss. des; subst. inv RESERVE. inv RESERVEORIGINAL.
    lets GET: H.
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; des; subst; ss; eauto.
    erewrite Memory.split_o in H; eauto.
    des_ifH H; des; subst; ss; eauto.
    des_ifH H; des; subst; ss; eauto.
    des_ifH H; des; subst; ss; eauto.
    erewrite Memory.split_o in H; eauto.
    des_ifH H; des; subst; ss; eauto.
    des_ifH H; des; subst; ss; eauto.
    des_ifH H; des; subst; ss; eauto.
    subst. inv H.
    exploit Memory.split_get0; eauto.
    ii; des; eauto.
Qed.

Lemma write_split_rsv_prop
      prm mem loc from to val R prm' mem' ts val' R'
      (WRITE: Memory.write prm mem loc from to val R prm' mem'
                           (Memory.op_kind_split ts (Message.concrete val' R'))):
  (forall t f loc, Memory.get loc t prm = Some (f, Message.reserve) <->
              Memory.get loc t prm' = Some (f, Message.reserve)).
Proof.
  inv WRITE. inv PROMISE; ss. des; subst. inv RESERVE. inv RESERVEORIGINAL. ii. split; ii.
  - erewrite Memory.remove_o; eauto.
    des_if; eauto. ss. des; subst.
    clear MEM. exploit Memory.split_get0; eauto. ii; des.
    rewrite H in GET. ss.
    ss. eapply mem_split_rsv in PROMISES. eapply PROMISES. eauto.
  - erewrite Memory.remove_o in H; eauto.
    des_ifH H; des; ss; eauto.
    eapply mem_split_rsv in PROMISES. eapply PROMISES in H. eauto.
    eapply mem_split_rsv in H; eauto.
Qed.

Lemma promises_relation_lower
      prm_tgt loc from to val R msg prm_tgt'
      prm_src from' to' val' R' msg' prm_src'
      inj lo
      (LOWER1: Memory.lower prm_tgt loc from to (Message.concrete val R) msg prm_tgt')
      (LOWER2: Memory.lower prm_src loc from' to' (Message.concrete val' R') msg' prm_src')
      (PROM_REL: promises_relation inj lo prm_tgt prm_src):
  promises_relation inj lo prm_tgt' prm_src'.
Proof.
  inv PROM_REL. econs; eauto.
  - inv H. econs; eauto; ii.
    {
      rewrite dset_gempty in H. ss.
    }
    {
      erewrite Memory.lower_o in H; eauto. des_ifH H; ss; eauto.
      des; subst. inv H.
      exploit Memory.lower_get0; [eapply LOWER1 | eauto..]. ii; des.
      exploit SOUND2; [eapply GET | eauto..]. ii; des.
      eapply Memory.lower_get1 in x0; eauto. des. inv MSG_LE0.
      exists t' f' val'0 released. splits; eauto.
      exploit SOUND2; eauto. ii; do 5 des1.
      exploit Memory.lower_get1; eauto. ii; do 2 des1. inv MSG_LE.
      exists t' f' val'0 released. splits; eauto. 
    }
    {
      erewrite Memory.lower_o in H; eauto. des_ifH H; ss; eauto.
      des1; subst. inv H.
      exploit Memory.lower_get0; eauto. ii; des.
      exploit COMPLETE; eauto. ii; des. rewrite dset_gempty in x0. ss.
      exploit Memory.lower_get1; [eapply LOWER1 | eauto..]. ii; des. inv MSG_LE0.
      exists t. splits; eauto.
      exploit COMPLETE; eauto. ii; do 3 des1.
      des1. rewrite dset_gempty in x0. ss.
      do 3 des1. exploit Memory.lower_get1; [eapply LOWER1 | eauto..]. ii; do 2 des1. inv MSG_LE.
      exists t. splits; eauto.
    }
  - ii; split; ii.
    eapply mem_lower_rsv in LOWER1.
    eapply LOWER1 in H2. clear LOWER1.
    eapply mem_lower_rsv in LOWER2.
    eapply LOWER2; eauto. eapply H0; eauto.
    eapply mem_lower_rsv in LOWER2.
    eapply LOWER2 in H2. clear LOWER2.
    eapply mem_lower_rsv in LOWER1.
    eapply LOWER1; eauto.
    eapply H0; eauto.
Qed.

Lemma promises_relation_remove_concrete
      prm_tgt loc from to val R prm_tgt'
      prm_src from' to' val' R' prm_src'
      inj lo inj'
      (REMOVE1: Memory.remove prm_tgt loc from to (Message.concrete val R) prm_tgt')
      (REMOVE2: Memory.remove prm_src loc from' to' (Message.concrete val' R') prm_src')
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (INJ_TO: inj' loc to = Some to')
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj'):
  promises_relation inj lo prm_tgt' prm_src'.
Proof.
  inv PROM_REL. econs; eauto.
  - inv H. econs; eauto.
    {
      ii. rewrite dset_gempty in H. ss.
    }
    {
      ii. erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss.
      exploit SOUND2; eauto. ii;  do 5 des1.
      exists t' f' val'0 R'0. splits; eauto.
      erewrite Memory.remove_o; eauto. des_if; eauto.
      simpl in a. des1; subst. des1; ss.
      eapply INCR_INJ in x.
      exploit monotonic_inj_implies_injective; [eapply MON_INJ | eapply INJ_TO | eapply x | eauto..].
      ii; subst. ss.
    }
    {
      ii. erewrite Memory.remove_o in H; eauto. des_ifH H; eauto; ss.
      exploit COMPLETE; eauto. ii; do 2 des1. des1.
      des1. rewrite dset_gempty in x0. ss.
      do 3 des1. exists t. splits; eauto. right.
      exists f val0 R0. erewrite Memory.remove_o; eauto.
      des_if; eauto. simpl in a. des1; subst. des1; ss.
      eapply INCR_INJ in x.
      rewrite INJ_TO in x. inv x. ss.
    }
  - ii. splits; ii.
    eapply mem_remove_concrete_rsv in REMOVE1.
    eapply REMOVE1 in H2. clear REMOVE1.
    eapply mem_remove_concrete_rsv in REMOVE2.
    eapply REMOVE2; eauto. eapply H0; eauto.
    eapply mem_remove_concrete_rsv in REMOVE1.
    eapply REMOVE1. clear REMOVE1.
    eapply mem_remove_concrete_rsv in REMOVE2.
    eapply REMOVE2 in H2; eauto.
    eapply H0; eauto.
Qed.

Lemma promises_relation_add_concrete
      prm_tgt loc from to val R prm_tgt'
      prm_src from' to' val' R' prm_src'
      inj lo inj'
      (ADD1: Memory.add prm_tgt loc from to (Message.concrete val R) prm_tgt')
      (ADD2: Memory.add prm_src loc from' to' (Message.concrete val' R') prm_src')
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (INJ_TO: inj' loc to = Some to')
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj'):
  promises_relation inj' lo prm_tgt' prm_src'.
Proof.
  inv PROM_REL. econs; eauto.
  - inv H. clear H0. econs; eauto.
    {
      ii. rewrite dset_gempty in H. ss.
    }
    {
      ii.
      erewrite Memory.add_o in H; eauto.
      des_ifH H; ss; eauto.
      simpl in a. des1; subst. inv H.
      exists to' from' val' R'. split; eauto.
      exploit Memory.add_get0; eauto. ii; des; eauto.
      exploit SOUND2; eauto. ii. do 5 des1.
      exists t' f' val'0 R'0. split; eauto.
      erewrite Memory.add_o; eauto. des_if; eauto.
      simpl in a. des1; subst. des1; ss.
      eapply INCR_INJ in x.
      exploit monotonic_inj_implies_injective;
        [eapply MON_INJ | eapply INJ_TO | eapply x | eauto..]. ii; subst. ss.
    }
    {
      ii.
      erewrite Memory.add_o in H; eauto.
      des_ifH H; ss; eauto. des1; subst. inv H.
      exploit Memory.add_get0; [eapply ADD1 | eauto..]. i. des1.
      exists to. split; eauto.
      exploit COMPLETE; eauto. ii. do 2 des1. des1.
      des1. rewrite dset_gempty in x0. ss.
      do 3 des1. exists t. split; eauto.
      right. erewrite Memory.add_o; eauto.
      des_if; eauto.
    }
  - ii. split; ii.
    {
      erewrite Memory.add_o in H2; eauto.
      des_ifH H2; ss.
      erewrite Memory.add_o; eauto. des_if; eauto.
      simpl in a. des1; subst. des; ss.
      eapply H0 in H2; eauto. exploit Memory.add_get0; eauto.
      ii; des. rewrite H2 in GET. ss.
      simpl in o0.
      eapply H0; eauto.
    }
    {
      erewrite Memory.add_o in H2; eauto.
      des_ifH H2; ss.
      erewrite Memory.add_o; eauto.
      des_if; eauto.
      simpl in a. des1; subst. des1; subst; ss.
      eapply H0 in H2; eauto.
      exploit Memory.add_get0; [eapply ADD1 | eauto..]. ii; des.
      rewrite H2 in GET. ss.
      eapply H0; eauto.
    }
Qed.

Lemma promises_relation_add_rsv
      prm_tgt loc from to prm_tgt'
      prm_src prm_src'
      inj lo
      (ADD1: Memory.add prm_tgt loc from to (Message.reserve) prm_tgt')
      (ADD2: Memory.add prm_src loc from to (Message.reserve) prm_src')
      (PROM_REL: promises_relation inj lo prm_tgt prm_src):
  promises_relation inj lo prm_tgt' prm_src'.
Proof.
  inv PROM_REL. econs; eauto.
  - inv H. econs; eauto; ii.
    {
      rewrite dset_gempty in H; ss.
    }
    {
      erewrite Memory.add_o in H; eauto.
      des_ifH H; ss.
      exploit SOUND2; eauto. ii. do 5 des1.
      exists t' f' val' R'.
      splits; eauto.
      erewrite Memory.add_o; eauto.
      des_if; eauto. simpl in a. des1; subst.
      des; ss.
      exploit Memory.add_get0; eauto. ii; des.
      rewrite x0 in GET. ss.
    }
    {
      erewrite Memory.add_o in H; eauto.
      des_ifH H; ss.
      exploit COMPLETE; eauto. ii. do 2 des1.
      des1. des1. rewrite dset_gempty in x0; ss.
      do 3 des1.
      exists t. splits; eauto.
      right. exists f val R.
      erewrite Memory.add_o; eauto. 
      des_if; eauto. simpl in a. des1; subst.
      exploit Memory.add_get0; [eapply ADD1 | eauto..].
      i. des1. rewrite x0 in GET. ss.
    }
  - ii. split; ii.
    {
      erewrite Memory.add_o in H2; eauto. des_ifH H2; eauto.
      simpl in a. des1; subst. inv H2.
      exploit Memory.add_get0; [eapply ADD2 | eauto..]. ii; des; eauto.
      simpl in o.
      erewrite Memory.add_o; eauto.
      des_if; eauto. simpl in a. des1; subst. des1; ss.
      eapply H0; eauto.
    }
    {
      erewrite Memory.add_o in H2; eauto. des_ifH H2; eauto.
      simpl in a. des1; subst. inv H2.
      exploit Memory.add_get0; eauto. ii; des; eauto.
      simpl in o.
      erewrite Memory.add_o; eauto. des_if; eauto.
      simpl in a. des1; subst; ss. des1; ss.
      eapply H0; eauto.
    }
Qed.

Lemma promises_relation_add_rsv'
      prm_tgt loc from to prm_tgt'
      prm_src
      inj lo
      (ADD1: Memory.add prm_tgt loc from to (Message.reserve) prm_tgt')
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (NA_LOC: lo loc = Ordering.nonatomic):
  promises_relation inj lo prm_tgt' prm_src.
Proof.
  inv PROM_REL. econs; eauto.
  - inv H. econs; eauto; ii.
    {
      erewrite Memory.add_o in H; eauto.
      des_ifH H; ss.
      exploit SOUND2; eauto. 
    }
    {
      exploit COMPLETE; eauto. ii. do 2 des1.
      des1. des1. rewrite dset_gempty in x0; ss.
      do 3 des1.
      exists t. splits; eauto.
      right. exists f val R.
      erewrite Memory.add_o; eauto. 
      des_if; eauto. simpl in a. des1; subst.
      exploit Memory.add_get0; [eapply ADD1 | eauto..].
      i. des1. rewrite x0 in GET. ss.
    }
  - ii. split; ii.
    {
      erewrite Memory.add_o in H2; eauto. des_ifH H2; eauto.
      simpl in a. des1; subst. inv H2.
      rewrite NA_LOC in H1. ss.
      simpl in o.
      eapply H0; eauto.
    }
    {
      erewrite Memory.add_o; eauto. des_if; eauto.
      simpl in a. des1; subst; ss. rewrite NA_LOC in H1. ss.
      eapply H0; eauto.
    }
Qed.

Lemma promises_relation_split
      prm_tgt loc from to ts val R val1 R1 prm_tgt'
      prm_src from' to' ts' val' R' val1' R1' prm_src'
      inj lo inj'
      (SPLIT1: Memory.split prm_tgt loc from to ts
                            (Message.concrete val R) (Message.concrete val1 R1) prm_tgt')
      (SPLIT2: Memory.split prm_src loc from' to' ts'
                            (Message.concrete val' R') (Message.concrete val1' R1') prm_src')
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (INJ_TO: inj' loc to = Some to')
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj'):
  promises_relation inj' lo prm_tgt' prm_src'.
Proof.
  inv PROM_REL. econs; eauto.
  - inv H. econs; eauto; ii.
    {
      erewrite dset_gempty in H; ss.
    }
    {
      erewrite Memory.split_o in H; eauto.
      des_ifH H; ss. des1; subst. inv H.
      exploit Memory.split_get0; eauto. i. do 3 des1.
      exists to' from' val' R'. split; eauto.
      des_ifH H; ss. des1; subst. inv H.
      exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. i. do 3 des1.
      exploit SOUND2; [eapply GET0 | eauto..]. i. do 5 des1.
      eapply Memory.split_get1 in x0; eauto. do 2 des1.
      exists t' f'0 val'0 R'0. split; eauto.
      exploit SOUND2; [eapply H | eauto..]. i. do 5 des1.
      eapply Memory.split_get1 in x0; eauto. do 2 des1.
      exists t' f'0 val'0 R'0. split; eauto.
    }
    {
      erewrite Memory.split_o in H; eauto.
      des_ifH H; ss. des1; subst. inv H.
      exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. i. do 3 des1.
      exists to. split; eauto.
      des_ifH H; ss. des1; subst. inv H.
      exploit Memory.split_get0; eauto. i. do 3 des1.
      exploit COMPLETE; eauto. i. do 2 des1.
      des1. des1. rewrite dset_gempty in x0. ss.
      do 3 des1. exists t. split; eauto. right.
      eapply Memory.split_get1 in x0; eauto. do 2 des1.
      eauto.
      exploit COMPLETE; eauto. i.
      do 2 des1. des1. des1. rewrite dset_gempty in x0. ss.
      do 3 des1. exists t. split; eauto. right.
      eapply Memory.split_get1 in x0; eauto. do 2 des1.
      exists f'0 val0 R0. eauto.
    }
  - ii. split; ii.
    {
      erewrite Memory.split_o in H2; eauto. des_ifH H2; ss.
      des_ifH H2; ss.
      erewrite Memory.split_o; eauto.
      des_if; eauto. simpl in a. des1; subst.
      eapply H0 in H2; eauto.
      exploit Memory.split_get0; eauto. i. do 3 des1.
      rewrite H2 in GET. ss.
      des_if; eauto. simpl in a. des1; subst. ss.
      exploit Memory.split_get0; [eapply SPLIT2 | eauto..].
      i. do 3 des1. eapply H0 in H2; eauto.
      rewrite H2 in GET0. ss.
      eapply H0; eauto.
    }
    {
      erewrite Memory.split_o in H2; eauto. des_ifH H2; ss.
      des_ifH H2; ss.
      erewrite Memory.split_o; eauto. des_if; ss; eauto.
      des1; subst. eapply H0 in H2; eauto.
      exploit Memory.split_get0; [eapply SPLIT1 | eauto..].
      i. do 3 des1. rewrite H2 in GET; ss.
      des_if; eauto. simpl in a. des1; subst.
      eapply H0 in H2; eauto.
      exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. i. do 3 des1.
      rewrite H2 in GET0. ss.
      eapply H0; eauto.
    }
Qed.

Lemma promises_relation_split_add
      prm_tgt loc from to ts val R val1 R1 prm_tgt'
      prm_src from' to' val' R' prm_src'
      inj lo inj'
      (SPLIT: Memory.split prm_tgt loc from to ts
                            (Message.concrete val R) (Message.concrete val1 R1) prm_tgt')
      (ADD: Memory.add prm_src loc from' to'
                            (Message.concrete val' R') prm_src')
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (INJ_TO: inj' loc to = Some to')
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj'):
  promises_relation inj' lo prm_tgt' prm_src'.
Proof.
  inv PROM_REL. econs; eauto.
  - inv H. econs; eauto; ii.
    {
      erewrite dset_gempty in H; ss.
    } 
    {
      erewrite Memory.split_o in H; eauto.
      des_ifH H; ss. des1; subst. inv H.
      exploit Memory.add_get0; eauto. i. des1.
      exists to' from' val' R'. split; eauto.
      des_ifH H; ss. des1; subst. inv H.
      exploit Memory.split_get0; [eapply SPLIT | eauto..]. i. do 3 des1.
      exploit SOUND2; [eapply GET0 | eauto..]. i. do 5 des1.
      eapply Memory.add_get1 in x0; eauto.
      exists t' f' val'0 R'0. split; eauto.
      exploit SOUND2; [eapply H | eauto..]. i. do 5 des1.
      eapply Memory.add_get1 in x0; eauto.
      exists t' f' val'0 R'0. split; eauto.
    }
    {
      erewrite Memory.add_o in H; eauto.
      des_ifH H; ss. des1; subst. inv H.
      exploit Memory.split_get0; [eapply SPLIT | eauto..]. i. do 3 des1.
      exists to. split; eauto.
      exploit COMPLETE; eauto. i. do 2 des1.
      des1. des1. rewrite dset_gempty in x0. ss.
      do 3 des1. exists t. split; eauto. right.
      eapply Memory.split_get1 in x0; eauto. do 2 des1.
      eauto.
    }
  - ii. split; ii.
    {
      erewrite Memory.split_o in H2; eauto. des_ifH H2; ss.
      des_ifH H2; ss.
      erewrite Memory.add_o; eauto.
      des_if; eauto. simpl in a. des1; subst.
      eapply H0 in H2; eauto.
      exploit Memory.add_get0; eauto. i. des1.
      rewrite H2 in GET. ss.
      eapply H0; eauto.
    }
    {
      erewrite Memory.add_o in H2; eauto. des_ifH H2; ss.
      erewrite Memory.split_o; eauto. des_if; ss; eauto.
      des1; subst. eapply H0 in H2; eauto.
      exploit Memory.split_get0; [eapply SPLIT | eauto..].
      i. do 3 des1. rewrite H2 in GET; ss.
      des_if; eauto. simpl in a. des1; subst.
      eapply H0 in H2; eauto.
      exploit Memory.split_get0; [eapply SPLIT | eauto..]. i. do 3 des1.
      rewrite H2 in GET0. ss.
      eapply H0; eauto.
    }
Qed.

Lemma promises_relation_cancel_at
      inj lo prm_tgt prm_tgt' prm_src prm_src' loc from to
      (PRM_REL: promises_relation inj lo prm_tgt prm_src)
      (CCL1: Memory.remove prm_tgt loc from to Message.reserve prm_tgt')
      (CCL2: Memory.remove prm_src loc from to Message.reserve prm_src')
      (AT_LOC: lo loc = Ordering.atomic):
  promises_relation inj lo prm_tgt' prm_src'.
Proof.
  inv PRM_REL. econs; eauto.
  - inv H. econs; eauto; ii.
    {
      rewrite dset_gempty in H; ss.
    }
    {
      erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss.
      exploit SOUND2; eauto. ii. do 5 des1.
      exists t' f' val' R'. split; eauto.
      erewrite Memory.remove_o; eauto.
      des_if; eauto.
      ss. des1; subst.
      exploit Memory.remove_get0; eauto. ii. des1.
      rewrite x0 in GET. ss.
    }
    {
      erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss.
      exploit COMPLETE; eauto. i. do 2 des1.
      des1. des1. rewrite dset_gempty in x0. ss.
      do 3 des1.
      exists t. split; eauto. right.
      erewrite Memory.remove_o; eauto.
      des_if; eauto.
      simpl in a. des1; subst.
      exploit Memory.remove_get0; [eapply CCL1 | eauto..].
      i. des1. rewrite x0 in GET. ss.
    }
  - ii. split; ii.
    {
      erewrite Memory.remove_o in H2; eauto.
      des_ifH H2; ss.
      erewrite Memory.remove_o; eauto.
      des_if; eauto.
      simpl in a. des1; subst. des1; ss.
      eapply H0; eauto.
    }
    {
      erewrite Memory.remove_o in H2; eauto.
      des_ifH H2; eauto; ss.
      erewrite Memory.remove_o; eauto.
      des_if; eauto. simpl in a. des1; subst. des; ss.
      eapply H0; eauto.
    }
Qed.

Lemma promises_relation_cancel_na
      inj lo prm_tgt prm_tgt' prm_src loc from to
      (PRM_REL: promises_relation inj lo prm_tgt prm_src)
      (CCL1: Memory.remove prm_tgt loc from to Message.reserve prm_tgt')
      (AT_LOC: lo loc = Ordering.nonatomic):
  promises_relation inj lo prm_tgt' prm_src.
Proof.
  inv PRM_REL. econs; eauto.
  - inv H. econs; eauto; ii.
    {
      erewrite Memory.remove_o in H; eauto.
      des_ifH H; ss.
      exploit SOUND2; eauto.
    }
    {
      exploit COMPLETE; eauto. i. do 2 des1.
      des1. des1. rewrite dset_gempty in x0. ss.
      do 3 des1.
      exists t. split; eauto.
      right. erewrite Memory.remove_o; eauto.
      des_if; eauto. simpl in a. des1; subst.
      exploit Memory.remove_get0; eauto.
      i. des1. rewrite x0 in GET. ss.
    }
  - ii. split; ii.
    erewrite Memory.remove_o in H2; eauto.
    des_ifH H2; ss. eapply H0; eauto.
    erewrite Memory.remove_o; eauto.
    des_if; eauto. 
    simpl in a. des1; subst.
    rewrite AT_LOC in H1; ss.
    eapply H0; eauto.
 Qed.
    
Lemma promises_relation_inj_na_write_prsv
      tview_tgt prm_tgt sc_tgt mem_tgt loc from to val tview_tgt' prm_tgt' sc_tgt' mem_tgt' Rr Rw kind1
      tview_src prm_src sc_src mem_src from' to' val' tview_src' prm_src' sc_src' mem_src' Rr' Rw' kind2
      ow lo inj inj'
      (WRITE1: Local.write_step (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt loc from to val Rr Rw ow
                                (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt' kind1 lo)
      (WRITE2: Local.write_step (Local.mk tview_src prm_src) sc_src mem_src loc from' to' val' Rr' Rw' ow
                                (Local.mk tview_src' prm_src') sc_src' mem_src' kind2 lo)
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (SPLIT_INJ: forall (t : Time.t) (val : Const.t) (R : option View.t),
          kind1 = Memory.op_kind_split t (Message.concrete val R) -> kind2 = Memory.op_kind_add)
      (KIND_MATCH: (forall (t : Time.t) (val : Const.t) (R : option View.t),
                       kind1 <> Memory.op_kind_split t (Message.concrete val R)) -> kind_match kind1 kind2)
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj')
      (INJ_TO: inj' loc to = Some to'):
  promises_relation inj lo prm_tgt' prm_src'.
Proof.
  destruct kind1; ss.
  - exploit KIND_MATCH; eauto. ii; ss. ii.
    destruct kind2; ss.
    inv WRITE1. inv LC2; ss. inv WRITE2. inv LC2; ss.
    eapply MemoryFacts.MemoryFacts.write_add_promises in WRITE.
    eapply MemoryFacts.MemoryFacts.write_add_promises in WRITE0. subst. eauto.
  - clear KIND_MATCH.
    inv WRITE1. inv LC2. ss. inv WRITE2. inv LC2; ss.
    assert (exists val3 R3, msg3 = Message.concrete val3 R3).
    {
      clear - WRITE. inv WRITE. inv PROMISE; eauto.
    }
    des; subst.
    exploit SPLIT_INJ; eauto. ii; subst.
    exploit write_split_prm_prop; eauto. ii; des.
    eapply MemoryFacts.MemoryFacts.write_add_promises in WRITE0. subst.
    inv PROM_REL. econs; eauto.
    {
      inv H. econs; eauto; ii.
      exploit x1; eauto. ii; des. eauto.
      eapply COMPLETE in H; eauto. des.
      rewrite dset_gempty in H1. ss. exists t. splits; eauto. right.
      eapply x0 in H1. des. eauto.
    }
    {
      ii. split; ii.
      eapply write_split_rsv_prop in WRITE. eapply WRITE in H2. eapply H0; eauto.
      eapply write_split_rsv_prop in WRITE. eapply WRITE. eapply H0; eauto.
    }
  - exploit KIND_MATCH; eauto. ii; ss.
    ii. destruct msg1; ss. destruct kind2; ss. destruct msg1; ss. subst.
    clear KIND_MATCH SPLIT_INJ.
    inv WRITE1; ss. inv LC2. inv WRITE2; ss. inv LC2.
    inv WRITE; ss. inv PROMISE; ss. des; subst; ss. inv RESERVE.
    inv WRITE0; ss. inv PROMISE; ss. des; subst; ss. inv RESERVE.
    eapply promises_relation_lower with (prm_tgt' := promises1) (prm_src' := promises3) in PROM_REL; eauto.
    eapply promises_relation_remove_concrete; eauto.
  - inv WRITE1. ss. inv WRITE; ss. inv PROMISE; ss.
Qed.

Lemma promises_relation_inj_write_kind_match_prsv
      tview_tgt prm_tgt sc_tgt mem_tgt loc from to val tview_tgt' prm_tgt' sc_tgt' mem_tgt' Rr Rw kind1
      tview_src prm_src sc_src mem_src from' to' val' tview_src' prm_src' sc_src' mem_src' Rr' Rw' kind2
      ow lo inj inj'
      (WRITE1: Local.write_step (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt loc from to val Rr Rw ow
                                (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt' kind1 lo)
      (WRITE2: Local.write_step (Local.mk tview_src prm_src) sc_src mem_src loc from' to' val' Rr' Rw' ow
                                (Local.mk tview_src' prm_src') sc_src' mem_src' kind2 lo)
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (KIND_MATCH: kind_match kind1 kind2)
      (INCR_INJ: incr_inj inj inj')
      (MON_INJ: monotonic_inj inj')
      (INJ_TO: inj' loc to = Some to'):
  promises_relation inj lo prm_tgt' prm_src'.
Proof.
  destruct kind1; ss.
  - destruct kind2; ss.
    inv WRITE1. inv LC2; ss. inv WRITE2. inv LC2; ss.
    eapply MemoryFacts.MemoryFacts.write_add_promises in WRITE.
    eapply MemoryFacts.MemoryFacts.write_add_promises in WRITE0. subst. eauto.
  - destruct msg3; ss. destruct kind2; ss. destruct msg3; ss.
    inv WRITE1. inv LC2. ss. inv WRITE2. inv LC2; ss.
    exploit write_split_prm_prop; [eapply WRITE | eauto..]. ii; des.
    exploit write_split_prm_prop; [eapply WRITE0 | eauto..]. ii; des.
    inv PROM_REL. econs; eauto.
    {
      inv H. econs; eauto; ii. rewrite dset_gempty in H; ss.
      eapply x1 in H. des. exploit SOUND2; eauto. ii; des.
      eapply x2 in x4. des.
      do 4 eexists. split; eauto.
      eapply x3 in H. des. eapply COMPLETE in H; eauto.
      des. rewrite dset_gempty in H1. ss. exists t. splits; eauto. right.
      eapply x0 in H1. des. eauto.
    }
    {
      ii. split; ii. 
      eapply write_split_rsv_prop in WRITE. eapply WRITE in H2.
      eapply write_split_rsv_prop in WRITE0. eapply WRITE0; eauto. eapply H0; eauto.
      eapply write_split_rsv_prop in WRITE0. eapply WRITE0 in H2.
      eapply write_split_rsv_prop in WRITE. eapply WRITE; eauto. eapply H0; eauto.
    }
  - destruct msg1; ss. destruct kind2; ss. destruct msg1; ss. subst.
    inv WRITE1; ss. inv LC2. inv WRITE2; ss. inv LC2.
    inv WRITE; ss. inv PROMISE; ss. des; subst; ss. inv RESERVE.
    inv WRITE0; ss. inv PROMISE; ss. des; subst; ss. inv RESERVE.
    eapply promises_relation_lower with (prm_tgt' := promises1) (prm_src' := promises3) in PROM_REL; eauto.
    eapply promises_relation_remove_concrete; eauto.
  - inv WRITE1. ss. inv WRITE; ss. inv PROMISE; ss.
Qed.

Lemma rel_promises_inj_loc_nonsynch
      prm_tgt prm_src inj inj' mem_tgt mem_src index loc
      (REL_PROMISES: rel_promises inj (@dset_init index) prm_tgt prm_src)
      (INCR_INJ: incr_inj inj inj')
      (MEM_NONSYCH: Memory.nonsynch_loc loc prm_tgt)
      (MEM_INJ: MsgInj inj' mem_tgt mem_src)
      (PRM_LESS_TGT: Memory.le prm_tgt mem_tgt)
      (PRM_LESS_SRC: Memory.le prm_src mem_src):
  Memory.nonsynch_loc loc prm_src.
Proof.
  unfold Memory.nonsynch_loc in *. ii.
  inv REL_PROMISES.
  destruct msg; ss.
  exploit COMPLETE; eauto. ii; des.
  rewrite dset_gempty in x0. ss.
  exploit PRM_LESS_TGT; eauto. ii.
  exploit PRM_LESS_SRC; eauto. ii.
  inv MEM_INJ.
  exploit SOUND; eauto. ii; des.
  eapply INCR_INJ in x. rewrite x in x3. inv x3.
  rewrite x2 in x5. inv x5.
  exploit MEM_NONSYCH; eauto. ii.
  ss; subst. destruct R'; ss.
Qed.

Lemma rel_promises_inj_nonsynch
      prm_tgt prm_src inj inj' mem_tgt mem_src index
      (REL_PROMISES: rel_promises inj (@dset_init index) prm_tgt prm_src)
      (INCR_INJ: incr_inj inj inj')
      (MEM_NONSYCH: Memory.nonsynch prm_tgt)
      (MEM_INJ: MsgInj inj' mem_tgt mem_src)
      (PRM_LESS_TGT: Memory.le prm_tgt mem_tgt)
      (PRM_LESS_SRC: Memory.le prm_src mem_src):
  Memory.nonsynch prm_src.
Proof.
  unfold Memory.nonsynch in *. i.
  specialize (MEM_NONSYCH loc).
  eapply rel_promises_inj_loc_nonsynch; eauto.
Qed.

Lemma promises_relation_bot
      prm_src inj lo
      (PRM_REL: promises_relation inj lo Memory.bot prm_src)
      (NO_NA_RSV: forall loc to from,
          Memory.get loc to prm_src = Some (from, Message.reserve) -> lo loc = Ordering.atomic):
  prm_src = Memory.bot.
Proof.
  inv PRM_REL.
  destruct (classic (exists loc to from msg, Memory.get loc to prm_src = Some (from, msg))).
  {
    des.
    destruct msg. inv H.
    eapply COMPLETE in H1; eauto; des.
    rewrite dset_gempty in H2. ss.
    rewrite Memory.bot_get in H2; ss.
    exploit NO_NA_RSV; eauto. ii.
    eapply H0 in H1; eauto.
    rewrite Memory.bot_get in H1; ss.
  }
  {
    eapply Memory.ext; ii.
    rewrite Memory.bot_get.
    destruct (Memory.get loc ts prm_src) eqn:Heqe; eauto.
    destruct p.
    contradiction H1; eauto.
  }
Qed.

(** *promise step lemmas *)
Require Import ConsistentStableEnv.

Lemma promise_add_concrete_I_dce_prsv
      prm_tgt sc_tgt mem_tgt loc from to val R prm_tgt' mem_tgt' inj lo
      prm_src sc_src mem_src
      (PROM_ADD: Memory.promise prm_tgt mem_tgt loc from to (Message.concrete val R)
                                prm_tgt' mem_tgt' Memory.op_kind_add)
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (INV: I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (PRM_LESS_TGT: Memory.le prm_tgt mem_tgt)
      (PRM_LESS_SRC: Memory.le prm_src mem_src)
      (CLOSED_MSG: Memory.closed_message (Message.concrete val R) mem_tgt')
      (MON_INJ: monotonic_inj inj)
      (MEM_AT_EQ: Mem_at_eq lo mem_tgt mem_src)
      (CLOSED_MEM: Memory.closed mem_tgt)
      (CLOSED_SC: Memory.closed_timemap sc_tgt mem_tgt):
  exists prm_src' mem_src' kind from' to' R' inj',
    <<PRM_ADD': Memory.promise prm_src mem_src loc from' to' (Message.concrete val R')
                               prm_src' mem_src' kind>> /\
    <<CLOSED_MSG: Memory.closed_message (Message.concrete val R') mem_src'>> /\
    <<MEM_AT_EQ': Mem_at_eq lo mem_tgt' mem_src'>> /\                          
    <<INCR_INJ': incr_inj inj inj'>> /\ 
    <<MON_INJ': monotonic_inj inj'>> /\
    <<INV': I_dce lo inj' (Build_Rss sc_tgt mem_tgt' sc_src mem_src')>> /\
    <<PROM_REL': promises_relation inj' lo prm_tgt' prm_src'>> /\                    
    <<CONCRETE_INCR_TGT: concrete_mem_incr mem_tgt mem_tgt'>> /\ 
    <<CONCTETE_INCR_SRC: concrete_mem_incr mem_src mem_src'>>.
Proof.
  inv PROM_ADD.
  destruct (lo loc) eqn: LOC_TYPE.
  - (* atomic write *)
    renames LOC_TYPE to AT_LOC.
    assert (NOT_COVER: forall t : Time.t, Cover.covered loc t mem_src -> ~ Interval.mem (from, to) t).
    {
      ii. eapply memory_add_cover_disjoint; eauto.
      clear - H H0 MEM_AT_EQ AT_LOC. inv H; ss.
      unfold Mem_at_eq in MEM_AT_EQ. exploit MEM_AT_EQ; eauto.
      ii. unfold Mem_approxEq_loc in x. des.
      lets GET0: GET.
      destruct msg.
      specialize (x from0 to0 val).
      des. exploit x1; eauto. ii; des.
      econs; eauto.
      eapply x0 in GET0. econs; eauto.
    }
    assert (INJ_NONE: inj loc to = None).
    {
      clear - INV MEM. destruct (inj loc to) eqn:INJ; eauto.
      simpl in INV. des. inv INJ_MEM.
      exploit COMPLETE; eauto. ii; des.
      exploit Memory.add_get0; eauto. ii; des. rewrite x in GET. ss.
    }
    pose proof (identity_inj_incr) as NEW_INJ.
    specialize (NEW_INJ inj loc to). exploit NEW_INJ; eauto.
    clear - INV AT_LOC. ss. des.  eauto.
    clear NEW_INJ. intro NEW_INJ. des.
    assert (INCR_INJ: incr_inj inj inj').
    {
      clear - NEW_INJ0 INJ_NONE.
      subst. unfold incr_inj. ii. des_if; eauto.
      ss. des; subst. rewrite INJ_NONE in H; ss.
    }
    assert (SOUND_INJ': forall loc t f val_t R_t, Memory.get loc t mem_tgt' = Some (f, Message.concrete val_t R_t) ->
                                             exists t', inj' loc t = Some t').
    {
      simpl in INV. des. clear - INJ_MEM INJ_NONE NEW_INJ0 MEM. ii. subst.
      des_if; eauto. ss.
      erewrite Memory.add_o in H; eauto. des_ifH H; ss.
      des1; subst. des1; tryfalse. inv INJ_MEM.
      eapply SOUND in H. des; eauto.
    }
    assert (COMPLETE_INJ: forall t t' loc, inj' loc t = Some t' ->
                                      exists f val_t R_t, Memory.get loc t mem_tgt' = Some (f, Message.concrete val_t R_t)).
    {
      ii; subst. des_ifH H; eauto. simpl in a. des1. subst. inv H.
      clear - MEM. exploit Memory.add_get0; eauto. ii; des; eauto.
      simpl in o.
      erewrite Memory.add_o; eauto.
      des_if; eauto. simpl in o0.
      clear - INV H. ss. des. inv INJ_MEM.
      eapply COMPLETE in H. des; eauto.
    }
    assert (CLOSED_MSG_VIEW: forall released, R = Some released -> closed_viewInj inj' released).
    {
      ii; subst.
      eapply closed_viewInj_general; eauto.
      clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED; ss.
    }
    assert (CLOSED_MSG_VIEW_S: forall released, R = Some released ->
                                           exists released', ViewInj inj' released released').
    {
      clear - CLOSED_MSG_VIEW. ii. subst.
      exploit CLOSED_MSG_VIEW; eauto. ii.
      eapply closed_viewInj_implies_view; eauto.
    }

    assert (MSG_VIEW_S: exists R', opt_ViewInj inj' R R').
    {
      clear - CLOSED_MSG_VIEW_S. destruct R.
      exploit CLOSED_MSG_VIEW_S; eauto. ii; des.
      exists (Some released'). unfold opt_ViewInj. eauto.
      exists (@None View.t). econs; eauto.
    }
    destruct MSG_VIEW_S as (R' & MSG_VIEW_S).
    assert (ADD_MEM: exists mem_src', Memory.add mem_src loc from to (Message.concrete val R') mem_src').
    {
      exploit add_succeed_wf; eauto. ii; des.
      eapply Memory.add_exists; eauto.
      clear - NOT_COVER. ii. eapply NOT_COVER; eauto.
      econs; eauto.
      inv MSG_WF. econs.
      eapply View_opt_wf_inj_prsv; eauto.
      destruct R. ss. eapply closed_viewInj_general; eauto.
      clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED. eauto.
      econs; eauto.
    }
    destruct ADD_MEM as (mem_src' & ADD_MEM_SRC).
    exploit Memory.add_exists_le; [eapply PRM_LESS_SRC | eapply ADD_MEM_SRC | eauto..].
    introv ADD_PRM_SRC. destruct ADD_PRM_SRC as (prm_src' & ADD_PRM_SRC).
    assert (MEM_INJ': MsgInj inj' mem_tgt' mem_src').
    {
      eapply add_msgInj_stable_concrete; eauto.
      clear - INV. ss. des. eauto.
      subst inj'. des_if; eauto. simpl in o. des1; tryfalse.
    }
    assert (CLOSED_MSG_S: Memory.closed_message (Message.concrete val R') mem_src').
    {
      econs; eauto. destruct R'; eauto.
      destruct R; simpl in MSG_VIEW_S; tryfalse.
      inv CLOSED_MSG. inv CLOSED. econs.
      eapply closed_view_inj_prsv; eauto.
      clear - MEM_INJ'. ii. inv MEM_INJ'. exploit SOUND; eauto. ii; des.
      do 4 eexists. split; eauto.
    }
    assert (MSG_TO_S: Memory.message_to (Message.concrete val R') loc to).
    { 
      inv TS. econs.
      eapply Message_wf_inj; eauto. destruct R; try solve [econs; eauto].
      simpl. eapply closed_viewInj_general; eauto.
      clear - CLOSED_MSG. inv CLOSED_MSG; eauto. inv CLOSED; ss.
      simpl. des_if; eauto. simpl in o. des1; ss.
    }

    exists prm_src' mem_src' Memory.op_kind_add from to R'. exists inj'.
    splits; eauto.
    { 
      econs; eauto.
      ii. inv MSG. clear - MEM_AT_EQ GET ATTACH AT_LOC.
      unfold Mem_at_eq in MEM_AT_EQ. exploit MEM_AT_EQ; eauto. ii.
      clear MEM_AT_EQ. unfold Mem_approxEq_loc in x. des.
      destruct msg'. specialize (x to to' val). des.
      exploit x1; eauto. ii; des. eauto.
      eapply x0 in GET. eauto.
    }
    {
      eapply Mem_at_eq_add_concrete_prsv; eauto.
    }
    {
      simpl in INV. des.
      simpl. splits; eauto.
      eapply incr_inj_TMapInj; eauto. eapply closed_tm_to_closed_TMapInj; eauto.
      lets ADD_MEM_SRC': ADD_MEM_SRC. 
      ii. eapply memory_add_disj_loc_same with (loc0 := loc0) in ADD_MEM_SRC; eauto.
      unfold Memory.get in *.
      rewrite <- ADD_MEM_SRC in H.
      exploit TS_RSV; eauto.
      rewrite NEW_INJ0 in H0. des_ifH H0; eauto.
      simpl in a. des1; subst. inv H0. clear - H ADD_MEM_SRC'.
      exploit Memory.add_get0; eauto. ii. des1. unfold Memory.get in GET.
      rewrite H in GET. ss.
      ii. do 2 des1. exists to_r. split; eauto.
      introv ITV COVER'. eapply x0; eauto. inv COVER'.
      econs. 2: { eapply ITV0. }
      unfold Memory.get in *. rewrite <- ADD_MEM_SRC in GET. eauto.
      ii. subst. rewrite AT_LOC in H2. ss.
      ii. erewrite Memory.add_o in H; eauto.
      des_ifH H; eauto. tryfalse.
      ii. rewrite NEW_INJ0 in H0. des_ifH H0; eauto.
      simpl in a. des1; subst. inv H0. eauto.
      eapply Memory.add_closed; eauto.
    }
    {
      eapply promises_relation_add_concrete; eauto.
      subst. des_if; eauto. simpl in o. des1; tryfalse.
    }
    split; eapply memory_add_concrete_mem_incr; eauto.
  - (* non-atomic write *)
    pose proof (next_concrete_ext_loc0 mem_tgt' loc to) as NXT.
    des1.
    {
      (* next message exists *)
      do 6 des1.
      assert (NXT_TGT: Memory.get loc nxt_ts mem_tgt = Some (f0, Message.concrete val0 R0)).
      {
        erewrite Memory.add_o in NXT0; eauto.
        des_ifH NXT0; eauto. ss; des; subst. auto_solve_time_rel.
      }      
      simpl in INV. do 5 des1.
      assert (NXT_SRC: exists nxt_ts' f_s val_s R_s,
                 Memory.get loc nxt_ts' mem_src = Some (f_s, Message.concrete val_s R_s) /\
                 inj loc nxt_ts = Some nxt_ts').
      {
        clear - INJ_MEM NXT_TGT. inv INJ_MEM.
        exploit SOUND; eauto. ii; des; eauto. do 4 eexists. eauto.
      }
      do 5 des1.

      (* find unused timestamp *)
      exploit TS_RSV; [eapply NXT_SRC | eauto..].
      {
        clear - NXT NXT_SRC. pose proof (Time.bot_spec nxt_ts).
        eapply Time.le_lteq in H. des; subst; try solve [auto_solve_time_rel]. eauto.
      }
      introv Unused_Timestamps. do 2 des1.

      (* find increasing injection *)
      assert (INJ_NONE: inj loc to = None).
      {
        clear - MEM INJ_MEM.
        eapply Memory.add_get0 in MEM. des. destruct (inj loc to) eqn:INJ; eauto.
        inv INJ_MEM. exploit COMPLETE; eauto. ii; des.
        rewrite GET in x. ss.
      }
      exploit wf_inj_incr; [ | eapply INJ_NONE | eauto..].
      {
        inv INJ_MEM; eauto.
      }
      {
        instantiate (1 := Time.middle to_r f_s). introv INJ_ORIGN LT.
        inv INJ_MEM. exploit COMPLETE; [eapply INJ_ORIGN | eauto..]. ii; des.
        exploit SOUND; eauto. ii; des. rewrite INJ_ORIGN in x0. symmetry in x0. inv x0.
        exploit inj_src_view_le_unused_timestamps; [eapply INJ_ORIGN | eapply x2 | eapply NXT_SRC | eauto..].
        auto_solve_time_rel.
        introv LE.
        eapply Time.middle_spec in Unused_Timestamps. des. auto_solve_time_rel.
      }
      {
        introv INJ LT.
        destruct (Time.le_lt_dec nxt_ts ts).
        {
          inv INJ_MEM. 
          exploit monotonic_inj_implies_le_prsv; [eapply MONOTONIC | eapply l | eauto..].
          introv LE'. clear - LE' NXT_SRC Unused_Timestamps.
          eapply memory_get_ts_le in NXT_SRC. eapply Time.middle_spec in Unused_Timestamps. des.
          cut (Time.le f_s ts'). ii. auto_solve_time_rel.
          clear - NXT_SRC LE'. auto_solve_time_rel.
        }
        { 
          clear - INJ_MEM INJ LT l NXT1 MEM. inv INJ_MEM.
          exploit COMPLETE; eauto. ii; des.
          exploit SOUND; eauto. ii; des. clear SOUND COMPLETE MONOTONIC.
          rewrite INJ in x0. inv x0.
          eapply Memory.add_get1 in x; eauto.
          eapply NXT1 in x; eauto. des. auto_solve_time_rel. auto_solve_time_rel.
          ii. auto_solve_time_rel. ii; subst.
          auto_solve_time_rel.
        }
      }
      introv NEW_INJ. do 3 des1.

      assert (SOUND_INJ': forall loc t f val_t R_t, Memory.get loc t mem_tgt' = Some (f, Message.concrete val_t R_t) ->
                                               exists t', inj' loc t = Some t').
      {
        clear - INJ_MEM INJ_NONE NEW_INJ0 MEM. ii. subst.
        des_if; eauto. ss.
        erewrite Memory.add_o in H; eauto. des_ifH H; ss.
        des1; subst. des1; tryfalse. inv INJ_MEM.
        eapply SOUND in H. des; eauto.
      }
      assert (COMPLETE_INJ: forall t t' loc, inj' loc t = Some t' ->
                                        exists f val_t R_t, Memory.get loc t mem_tgt' = Some (f, Message.concrete val_t R_t)).
      {
        ii; subst. des_ifH H; eauto. simpl in a. des1. subst. inv H.
        clear - MEM. exploit Memory.add_get0; eauto. ii; des; eauto.
        simpl in o.
        erewrite Memory.add_o; eauto.
        des_if; eauto. simpl in o0.
        clear - INJ_MEM H. ss. des. inv INJ_MEM.
        eapply COMPLETE in H. des; eauto.
      }
      assert (CLOSED_MSG_VIEW: forall released, R = Some released -> closed_viewInj inj' released).
      {
        ii; subst.
        eapply closed_viewInj_general; eauto.
        clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED; ss.
      }
      assert (CLOSED_MSG_VIEW_S: forall released, R = Some released ->
                                             exists released', ViewInj inj' released released').
      {
        clear - CLOSED_MSG_VIEW. ii. subst.
        exploit CLOSED_MSG_VIEW; eauto. ii.
        eapply closed_viewInj_implies_view; eauto.
      }

      assert (MSG_VIEW_S: exists R', opt_ViewInj inj' R R').
      {
        clear - CLOSED_MSG_VIEW_S. destruct R.
        exploit CLOSED_MSG_VIEW_S; eauto. ii; des.
        exists (Some released'). unfold opt_ViewInj. eauto.
        exists (@None View.t). econs; eauto.
      }
      destruct MSG_VIEW_S as (R' & MSG_VIEW_S).
      assert (ADD_MEM: exists mem_src', Memory.add mem_src loc (Time.middle to_r (Time.middle to_r f_s))
                                              (Time.middle to_r f_s) (Message.concrete val R') mem_src').
      { 
        exploit add_succeed_wf; eauto. ii; des.
        eapply Memory.add_exists; eauto.
        {
          clear - Unused_Timestamps0 Unused_Timestamps. ii.
          eapply Time.middle_spec in Unused_Timestamps. des.
          eapply Time.middle_spec in Unused_Timestamps. des. 
          eapply Unused_Timestamps0; eauto.
          instantiate (1 := x). econs; eauto; ss. inv LHS; ss.
          auto_solve_time_rel.
          inv LHS; ss. eapply Time.le_lteq. left. auto_solve_time_rel.
          econs. 2: { eapply RHS; eauto. } eauto.
        }
        {
          clear - Unused_Timestamps. eapply Time.middle_spec in Unused_Timestamps. des.
          eapply Time.middle_spec in Unused_Timestamps; des. eauto.
        }
        {
          inv MSG_WF. econs.
          eapply View_opt_wf_inj_prsv; eauto.
          destruct R. ss. eapply closed_viewInj_general; eauto.
          clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED. eauto.
          econs; eauto.
        } 
      }
      destruct ADD_MEM as (mem_src' & ADD_MEM_SRC).
      exploit Memory.add_exists_le; [eapply PRM_LESS_SRC | eapply ADD_MEM_SRC | eauto..].
      introv ADD_PRM_SRC. destruct ADD_PRM_SRC as (prm_src' & ADD_PRM_SRC).
      assert (MEM_INJ': MsgInj inj' mem_tgt' mem_src').
      {
        eapply add_msgInj_stable_concrete; eauto.
        subst inj'. des_if; eauto. simpl in o. des1; tryfalse.
      }
      assert (CLOSED_MSG_S: Memory.closed_message (Message.concrete val R') mem_src').
      {
        econs; eauto. destruct R'; eauto.
        destruct R; simpl in MSG_VIEW_S; tryfalse.
        inv CLOSED_MSG. inv CLOSED. econs.
        eapply closed_view_inj_prsv; eauto.
        clear - MEM_INJ'. ii. inv MEM_INJ'. exploit SOUND; eauto. ii; des.
        do 4 eexists. split; eauto.
      }
      assert (MSG_TO_S: Memory.message_to (Message.concrete val R') loc (Time.middle to_r f_s)).
      { 
        inv TS. econs.
        eapply Message_wf_inj; eauto. destruct R; try solve [econs; eauto].
        simpl. eapply closed_viewInj_general; eauto.
        clear - CLOSED_MSG. inv CLOSED_MSG; eauto. inv CLOSED; ss.
        simpl. des_if; eauto. simpl in o. des1; ss.
      }

      exists prm_src' mem_src' Memory.op_kind_add.
      exists (Time.middle to_r (Time.middle to_r f_s)) (Time.middle to_r f_s) R'. exists inj'.
      splits; eauto.
      { 
        econs; eauto.
        ii. inv MSG.
        clear - GET Unused_Timestamps Unused_Timestamps0.
        eapply Time.middle_spec in Unused_Timestamps. des.
        exploit Memory.get_ts; eauto. ii; des; subst.
        rewrite x0 in Unused_Timestamps. auto_solve_time_rel.
        eapply not_cover_attach_contr; eauto.
        eapply Time.le_lteq; eauto.
      }
      {
        eapply Mem_at_eq_add_na_stable; eauto.
        eapply Mem_at_eq_reflexive; eauto.
        eapply Mem_at_eq_add_na_stable; eauto.
        eapply Mem_at_eq_reflexive; eauto.
      }
      {
        simpl. splits; eauto.
        (* sc mapping *)
        eapply incr_inj_TMapInj; eauto. eapply closed_tm_to_closed_TMapInj; eauto.

        (* TS rsv *)
        introv GET_SRC INJ'_GET LT' NON_ATOMIC_LOC.
        erewrite Memory.add_o in GET_SRC; eauto.
        des_ifH GET_SRC.
        {
          simpl in a. des; subst. inv GET_SRC.
          exists to_r. split. eapply Time.middle_spec in Unused_Timestamps. des.
          eapply Time.middle_spec in Unused_Timestamps. des; eauto.
          clear - Unused_Timestamps Unused_Timestamps0 ADD_MEM_SRC.
          introv ITV COVER. specialize (Unused_Timestamps0 ts).
          eapply Unused_Timestamps0; eauto.
          inv ITV. ss. econs; eauto. ss.
          eapply Time.middle_spec in Unused_Timestamps. des.
          eapply Time.middle_spec in Unused_Timestamps. des.
          clear - TO Unused_Timestamps2 Unused_Timestamps1.
          econs. cut (Time.lt ts (Time.middle to_r f_s)). ii.
          auto_solve_time_rel. auto_solve_time_rel.
          eapply Cover.add_covered in COVER; eauto. des; eauto.
          clear - Unused_Timestamps ITV COVER0.
          inv ITV. ss. inv COVER0; ss.
          auto_solve_time_rel.
        }
        {
          simpl in o. subst inj'. des_ifH INJ'_GET; eauto.
          simpl in a. des; subst; ss. inv INJ'_GET. ss.
          destruct (Loc.eq_dec loc loc0); subst.
          {
            (* same location *)
            des1; ss. des1; ss.
            destruct (Time.eq_dec to0 nxt_ts); subst.
            {
              rewrite NXT_SRC0 in INJ'_GET. inv INJ'_GET.
              rewrite NXT_SRC in GET_SRC. inv GET_SRC.
              exists (Time.middle to_r from'). split. eapply Time.middle_spec in Unused_Timestamps.
              des; eauto.
              introv ITV COVER. specialize (Unused_Timestamps0 ts).
              eapply Unused_Timestamps0; eauto. econs; eauto. ss.
              eapply Time.middle_spec in Unused_Timestamps. des.
              inv ITV; ss. auto_solve_time_rel.
              ss. inv ITV; ss.
              eapply Cover.add_covered in COVER; eauto. des1; eauto.
              des1. clear - ITV COVER0. inv ITV; ss. inv COVER0; ss.
              auto_solve_time_rel.
            }
            {
              destruct (Time.le_lt_dec to0 nxt_ts).
              {
                eapply Time.le_lteq in l. des; subst; ss.
                exploit inj_src_view_le_unused_timestamps;
                  [eapply INJ'_GET | eapply GET_SRC | eapply NXT_SRC | eapply NXT_SRC0 | eauto..].
                inv INJ_MEM; eauto.
                introv LE. exploit TS_RSV; [eapply GET_SRC | eauto..]. ii; des.
                exists to_r0. split; eauto. introv ITV' COVER. specialize (x0 ts).
                eapply x0; eauto.
                eapply Cover.add_covered in COVER; eauto. des; eauto.
                clear - GET_SRC LE ITV' COVER0 Unused_Timestamps. inv COVER0; ss.
                eapply memory_get_ts_le in GET_SRC. clear TO. inv ITV'; ss. clear FROM0.
                eapply Time.middle_spec in Unused_Timestamps. des. clear Unused_Timestamps0.
                eapply Time.middle_spec in Unused_Timestamps. des. clear Unused_Timestamps0.
                cut (Time.lt ts (Time.middle to_r (Time.middle to_r f_s))).
                ii. auto_solve_time_rel. ii; auto_solve_time_rel.
                clear - TO GET_SRC LE Unused_Timestamps.
                cut (Time.le ts to_r). ii. auto_solve_time_rel.
                cut (Time.le ts to'). ii. auto_solve_time_rel. auto_solve_time_rel.
              }
              {
                exploit TS_RSV; [eapply GET_SRC | eauto..]. ii; des.
                exploit inj_src_view_le_unused_timestamps;
                  [eapply NXT_SRC0 | eapply NXT_SRC | eapply GET_SRC | eauto..].
                inv INJ_MEM; eauto. introv LE.
                exists to_r0. split; eauto. introv ITV' COVER. specialize (x0 ts).
                eapply x0; eauto.
                eapply Cover.add_covered in COVER; eauto. des; eauto.
                clear - NXT_SRC Unused_Timestamps LE ITV' COVER0.
                inv ITV'; ss. clear TO. inv COVER0; ss. clear FROM0.
                cut (Time.le ts to_r0). ii. auto_solve_time_rel.
                cut (Time.le ts nxt_ts'). ii. auto_solve_time_rel.
                eapply memory_get_ts_le in NXT_SRC.
                cut (Time.le ts f_s). ii. auto_solve_time_rel.
                eapply Time.middle_spec in Unused_Timestamps. des.
                econs. auto_solve_time_rel.
              }
            }
          }
          {
            (* disjoint loc *)
            exploit TS_RSV; eauto. ii. do 2 des1.
            exists to_r0. split; eauto.
            introv ITV COVER. specialize (x0 ts). eapply x0; eauto.
            eapply Cover.add_covered in COVER; eauto. des1; eauto.
            des1; subst. des1; ss.
          }
        }

        (* reservation preservation *)
        clear - ADD_MEM_SRC NO_RSVs. introv GET. 
        erewrite Memory.add_o in GET; eauto. des_ifH GET; eauto.
        ss.

        (* Identity injection on atomic location *)
        clear - NEW_INJ0 ID_ATOMIC LOC_TYPE. ii. subst.
        des_ifH H0; eauto. ss. des; subst; ss. tryfalse.

        (* closed memory *)
        eapply Memory.add_closed; eauto.
      }
      {
        eapply promises_relation_add_concrete; eauto.
        subst. des_if; eauto. simpl in o. des1; tryfalse.
      }
      split; eapply memory_add_concrete_mem_incr; eauto.
    }
    {
      (* next message not exist *)
      (* find unused timestamp *)
      pose proof (Cover.gt_max_not_covered) as MAX_NO_COVER.

      (* find increasing injection *)
      exploit Memory.add_get0; [eapply MEM | eauto..]. ii. des1.
      assert (INJ_NONE: inj loc to = None).
      {
        clear - GET INV. ss. des. clear - GET INJ_MEM. inv INJ_MEM.
        destruct (inj loc to) eqn:INJ_LOC; eauto.
        exploit COMPLETE; eauto. ii; des.
        rewrite GET in x. ss.
      }
      exploit wf_inj_incr; [ | eapply INJ_NONE | eauto..].
      {
        simpl in INV. des. inv INJ_MEM; eauto.
      }
      {
        instantiate (1 := Time.incr (Time.incr (Memory.max_ts loc mem_src))).
        introv INJ_GET LT. clear - INJ_GET INV. ss. des.
        clear - INJ_MEM INJ_GET. inv INJ_MEM.
        exploit COMPLETE; eauto. ii; des. exploit SOUND; eauto. ii; des.
        rewrite INJ_GET in x0. inv x0.
        exploit Memory.max_ts_spec; [eapply x2 | eauto..]. ii; des.
        cut (Time.lt (Memory.max_ts loc mem_src) (Time.incr (Time.incr (Memory.max_ts loc mem_src)))).
        ii. auto_solve_time_rel.
        cut (Time.lt (Memory.max_ts loc mem_src) (Time.incr (Memory.max_ts loc mem_src))).
        ii.
        cut (Time.lt (Time.incr (Memory.max_ts loc mem_src))
                     (Time.incr (Time.incr (Memory.max_ts loc mem_src)))). ii.
        auto_solve_time_rel.
        eapply Time.incr_spec. eapply Time.incr_spec.        
      }
      {
        introv INJ_TO LT. clear - LT INJ_TO INV NXT MEM. ss. des.
        clear - INJ_MEM INJ_TO LT NXT MEM. inv INJ_MEM.
        exploit COMPLETE; eauto. ii; des.
        exploit Memory.add_get1; eauto. ii.
        eapply NXT in x1. clear - LT x1. auto_solve_time_rel.
      }
      ii. do 3 des1.
      simpl in INV. des.

      assert (SOUND_INJ': forall loc t f val_t R_t,
                 Memory.get loc t mem_tgt' =
                   Some (f, Message.concrete val_t R_t) ->
                 exists t', inj' loc t = Some t').
      {
        clear - INJ_MEM INJ_NONE NEW_INJ MEM. ii. subst.
        des_if; eauto. ss.
        erewrite Memory.add_o in H; eauto. des_ifH H; ss.
        des1; subst. des1; tryfalse. inv INJ_MEM.
        eapply SOUND in H. des; eauto.
      }
      assert (COMPLETE_INJ: forall t t' loc, inj' loc t = Some t' ->
                                        exists f val_t R_t, Memory.get loc t mem_tgt' = Some (f, Message.concrete val_t R_t)).
      {
        ii; subst. des_ifH H; eauto. simpl in a. des1. subst. inv H.
        clear - MEM. exploit Memory.add_get0; eauto. ii; des; eauto.
        simpl in o.
        erewrite Memory.add_o; eauto.
        des_if; eauto. simpl in o0.
        clear - INJ_MEM H. ss. des. inv INJ_MEM.
        eapply COMPLETE in H. des; eauto.
      }
      assert (CLOSED_MSG_VIEW: forall released, R = Some released -> closed_viewInj inj' released).
      {
        ii; subst.
        eapply closed_viewInj_general; eauto.
        clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED; ss.
      }
      assert (CLOSED_MSG_VIEW_S: forall released, R = Some released ->
                                             exists released', ViewInj inj' released released').
      {
        clear - CLOSED_MSG_VIEW. ii. subst.
        exploit CLOSED_MSG_VIEW; eauto. ii.
        eapply closed_viewInj_implies_view; eauto.
      }

      assert (MSG_VIEW_S: exists R', opt_ViewInj inj' R R').
      {
        clear - CLOSED_MSG_VIEW_S. destruct R.
        exploit CLOSED_MSG_VIEW_S; eauto. ii; des.
        exists (Some released'). unfold opt_ViewInj. eauto.
        exists (@None View.t). econs; eauto.
      }
      destruct MSG_VIEW_S as (R' & MSG_VIEW_S).
      assert (ADD_MEM: exists mem_src',
                 Memory.add mem_src loc (Time.incr (Memory.max_ts loc mem_src)) (Time.incr (Time.incr (Memory.max_ts loc mem_src))) (Message.concrete val R') mem_src').
      { 
        exploit add_succeed_wf; eauto. ii; des.
        eapply Memory.add_exists; eauto.
        {
          introv GET'. ii. inv LHS; ss.
          exploit Memory.max_ts_spec; eauto. ii. des.
          clear - GET' RHS FROM MAX. inv RHS; ss.
          cut (Time.le x (Memory.max_ts loc mem_src)). i.
          clear - FROM H.
          cut (Time.lt x (Time.incr (Memory.max_ts loc mem_src))).
          i. auto_solve_time_rel. ii. auto_solve_time_rel.
          cut (Time.lt (Memory.max_ts loc mem_src) (Time.incr (Memory.max_ts loc mem_src))).
          i. auto_solve_time_rel.
          auto_solve_time_rel. auto_solve_time_rel.
        }
        {
          auto_solve_time_rel.
        }
        {
          inv MSG_WF. econs.
          eapply View_opt_wf_inj_prsv; eauto.
          destruct R. ss. eapply closed_viewInj_general; eauto.
          clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED. eauto.
          econs; eauto.
        } 
      }
      destruct ADD_MEM as (mem_src' & ADD_MEM_SRC).
      exploit Memory.add_exists_le; [eapply PRM_LESS_SRC | eapply ADD_MEM_SRC | eauto..].
      introv ADD_PRM_SRC. destruct ADD_PRM_SRC as (prm_src' & ADD_PRM_SRC).
      assert (MEM_INJ': MsgInj inj' mem_tgt' mem_src').
      {
        eapply add_msgInj_stable_concrete; eauto.
        subst inj'. des_if; eauto. simpl in o. des1; tryfalse.
      }
      assert (CLOSED_MSG_S: Memory.closed_message (Message.concrete val R') mem_src').
      {
        econs; eauto. destruct R'; eauto.
        destruct R; simpl in MSG_VIEW_S; tryfalse.
        inv CLOSED_MSG. inv CLOSED. econs.
        eapply closed_view_inj_prsv; eauto.
        clear - MEM_INJ'. ii. inv MEM_INJ'. exploit SOUND; eauto. ii; des.
        do 4 eexists. split; eauto.
      }
      assert (MSG_TO_S: Memory.message_to (Message.concrete val R') loc (Time.incr (Time.incr (Memory.max_ts loc mem_src)))).
      { 
        inv TS. econs.
        eapply Message_wf_inj; eauto. destruct R; try solve [econs; eauto].
        simpl. eapply closed_viewInj_general; eauto.
        clear - CLOSED_MSG. inv CLOSED_MSG; eauto. inv CLOSED; ss.
        simpl. des_if; eauto. simpl in o. des1; ss.
      }

      exists prm_src' mem_src' Memory.op_kind_add.
      exists (Time.incr (Memory.max_ts loc mem_src)).
      exists (Time.incr (Time.incr (Memory.max_ts loc mem_src))).
      exists R' inj'.
      splits; eauto.
      {
        econs; eauto. clear. ii. inv MSG.
        exploit Memory.max_ts_spec; eauto. ii; des.
        exploit Memory.get_ts; [eapply GET | eauto..]. ii; des; subst.
        cut (Time.lt (Time.incr (Memory.max_ts loc mem_src))
                     (Time.incr (Time.incr (Memory.max_ts loc mem_src)))).
        i. rewrite x0 in H. auto_solve_time_rel.
        auto_solve_time_rel.
        cut (Time.lt to' to'). i. auto_solve_time_rel.
        cut (Time.lt to' (Time.incr (Time.incr (Memory.max_ts loc mem_src)))).
        i. clear - x0 H. auto_solve_time_rel. ii. auto_solve_time_rel.
        clear x0.
        cut (Time.lt (Memory.max_ts loc mem_src) (Time.incr (Time.incr (Memory.max_ts loc mem_src)))).
        i. auto_solve_time_rel.
        cut (Time.lt (Memory.max_ts loc mem_src)
                     (Time.incr (Memory.max_ts loc mem_src))). i.
        cut (Time.lt (Time.incr (Memory.max_ts loc mem_src))
                     (Time.incr (Time.incr (Memory.max_ts loc mem_src)))). i.
        auto_solve_time_rel. auto_solve_time_rel.
        auto_solve_time_rel.
      }
      {
        eapply Mem_at_eq_add_na_stable; eauto.
        eapply Mem_at_eq_reflexive; eauto.
        eapply Mem_at_eq_add_na_stable; eauto.
        eapply Mem_at_eq_reflexive; eauto.
      }
      {
        simpl; splits; eauto.

        (* TMapInj *)
        eapply incr_inj_TMapInj; eauto.
        eapply closed_tm_to_closed_TMapInj; eauto.

        (* TS rsv *)
        introv GET_SRC' INJ'_TO LT_BOT NON_ATOM_LOC.
        erewrite Memory.add_o in GET_SRC'; eauto.
        des_ifH GET_SRC'; eauto.
        {
          simpl in a. des1; subst. inv GET_SRC'.
          exists (Memory.max_ts loc mem_src). splits.
          eapply Time.incr_spec.
          introv ITV COVER. 
          eapply Cover.add_covered in COVER; eauto.
          des1.
          {
            clear - ITV COVER. inv COVER. inv ITV0; ss.
            inv ITV; ss. exploit Memory.max_ts_spec; eauto. ii; des.
            clear - TO FROM0 MAX.
            cut (Time.lt to ts). ii. auto_solve_time_rel. auto_solve_time_rel.
          }
          {
            des1; subst.
            clear - ITV COVER0. inv ITV; ss. inv COVER0; ss.
            clear - TO FROM0. auto_solve_time_rel.
          }
        }
        {
          simpl in o. subst inj'.
          des_ifH INJ'_TO. simpl in a. des1; subst. des1; tryfalse.
          simpl in o0.
          exploit TS_RSV; eauto. ii. do 2 des1.
          exists to_r. split. eauto.
          introv ITV COVER'. specialize (x0 ts).
          eapply x0; eauto.
          eapply Cover.add_covered in COVER'; eauto.
          des1; eauto. des1; subst. des1; tryfalse. des1; tryfalse.
          clear - GET_SRC' ITV COVER'0.
          exploit memory_get_ts_le; eauto. introv LE.
          eapply Memory.max_ts_spec in GET_SRC'; eauto. des.
          clear - MAX ITV COVER'0 LE. inv ITV; ss. inv COVER'0; ss.
          cut (Time.le from' (Time.incr (Memory.max_ts loc mem_src))).
          ii. clear - TO H FROM0.
          cut (Time.le ts (Time.incr (Memory.max_ts loc mem_src))). ii.
          clear - H0 FROM0. auto_solve_time_rel. auto_solve_time_rel.
          cut (Time.le from' (Memory.max_ts loc mem_src)). ii.
          cut (Time.lt (Memory.max_ts loc mem_src) (Time.incr (Memory.max_ts loc mem_src))). ii.
          eapply Time.le_lteq. left. auto_solve_time_rel.
          auto_solve_time_rel.
          auto_solve_time_rel.
        }

        (* reservation *)
        introv GET_RSV.
        erewrite Memory.add_o in GET_RSV; eauto.
        des_ifH GET_RSV; eauto.
        simpl in a. des1; subst. inv GET_RSV.

        (* ATOMIC ID *)
        introv LOC_ATOMIC INJ'_TO.
        rewrite NEW_INJ in INJ'_TO. des_ifH INJ'_TO; eauto.
        simpl in a. des1; subst. rewrite LOC_TYPE in LOC_ATOMIC. ss.

        (* closed memory *)
        eapply Memory.add_closed; eauto.
      }
      {
        eapply promises_relation_add_concrete; eauto.
        subst. des_if; eauto. simpl in o. des1; tryfalse.
      }
      split; eapply memory_add_concrete_mem_incr; eauto.
    }
Qed.

Lemma promise_add_reserve_I_dce_prsv
      prm_tgt sc_tgt mem_tgt loc from to prm_tgt' mem_tgt' inj lo
      prm_src sc_src mem_src
      (PROM_ADD: Memory.promise prm_tgt mem_tgt loc from to (Message.reserve)
                                prm_tgt' mem_tgt' Memory.op_kind_add)
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (INV: I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (PRM_LESS_TGT: Memory.le prm_tgt mem_tgt)
      (PRM_LESS_SRC: Memory.le prm_src mem_src)
      (MON_INJ: monotonic_inj inj)
      (MEM_AT_EQ: Mem_at_eq lo mem_tgt mem_src):
  exists prm_src' mem_src',
    <<PRM_ADD': Memory.promise prm_src mem_src loc from to (Message.reserve)
                               prm_src' mem_src' Memory.op_kind_add \/
                (prm_src = prm_src' /\ mem_src = mem_src')>> /\
    <<MEM_AT_EQ': Mem_at_eq lo mem_tgt' mem_src'>> /\
    <<INV': I_dce lo inj (Build_Rss sc_tgt mem_tgt' sc_src mem_src')>> /\
    <<PROM_REL': promises_relation inj lo prm_tgt' prm_src'>> /\ 
    <<CONCRETE_INCR_TGT: concrete_mem_incr mem_tgt mem_tgt'>> /\ 
    <<CONCTETE_INCR_SRC: concrete_mem_incr mem_src mem_src'>>.
Proof.
  inv PROM_ADD.
  destruct (lo loc) eqn: LOC_TYPE.
  - (* reservation on atomic location *)
    renames LOC_TYPE to AT_LOC.
    assert (NOT_COVER: forall t : Time.t, Cover.covered loc t mem_src -> ~ Interval.mem (from, to) t).
    {
      ii. eapply memory_add_cover_disjoint; eauto.
      clear - H H0 MEM_AT_EQ AT_LOC. inv H; ss.
      unfold Mem_at_eq in MEM_AT_EQ. exploit MEM_AT_EQ; eauto.
      ii. unfold Mem_approxEq_loc in x. des.
      lets GET0: GET.
      destruct msg.
      specialize (x from0 to0 val).
      des. exploit x1; eauto. ii; des.
      econs; eauto.
      eapply x0 in GET0. econs; eauto.
    }
    assert (ADD_MEM: exists mem_src', Memory.add mem_src loc from to (Message.reserve) mem_src').
    {
      exploit add_succeed_wf; eauto. ii; des.
      eapply Memory.add_exists; eauto.
      clear - NOT_COVER. ii. eapply NOT_COVER; eauto.
      econs; eauto.
    }
    destruct ADD_MEM as (mem_src' & ADD_MEM_SRC).
    exploit Memory.add_exists_le; [eapply PRM_LESS_SRC | eapply ADD_MEM_SRC | eauto..].
    introv ADD_PRM_SRC. destruct ADD_PRM_SRC as (prm_src' & ADD_PRM_SRC).

    exists prm_src' mem_src'. 
    splits.
    {
      econs; eauto. econs; eauto. ii; ss.
    }
    {
      eapply Mem_at_eq_add_reserve_prsv; eauto.
    }
    {
      ss. des. splits; eauto.
      eapply add_rsv_MsgInj_stable; eauto.

      introv GET INJ GT_BOT NA_LOC.
      erewrite Memory.add_o in GET; eauto. des_ifH GET.
      simpl in a. des1; ss.
      simpl in o.
      exploit TS_RSV; eauto. i. do 2 des1.
      exists to_r. split; eauto. 
      introv ITV COVER. eapply x0; eauto.
      inv COVER. econs.
      2: { eapply ITV0. }
      instantiate (1 := msg).
      eapply memory_add_disj_loc_stable with (loc0 := loc0) in ADD_MEM_SRC.
      clear - GET0 ADD_MEM_SRC.
      unfold Memory.get in *. rewrite <- ADD_MEM_SRC in GET0. eauto.
      ii. subst. rewrite AT_LOC in NA_LOC. ss.

      introv GET_RSV.
      erewrite Memory.add_o in GET_RSV; eauto.
      des_ifH GET_RSV; eauto. simpl in a. des1; subst. eauto.

      eapply Memory.add_closed; eauto.
    }
    {
      eapply promises_relation_add_rsv; eauto.
    }
    eapply memory_add_concrete_mem_incr; eauto.
    eapply memory_add_concrete_mem_incr; eauto.
  - (* reservation on non-atomic location *)
    exists prm_src mem_src. splits.
    right; eauto.
    {
      eapply Mem_at_eq_add_na_stable; eauto.
    }
    {
      ss. des. splits; eauto.
      eapply add_rsv_MsgInj_stable'; eauto.
    }
    {
      eapply promises_relation_add_rsv'; eauto.
    }
    eapply memory_add_concrete_mem_incr; eauto.
    ii. exists f R. splits; eauto.
    eapply View.View.opt_le_PreOrder_obligation_1; eauto.
    eapply Time.le_lteq; eauto.
    introv ITV. inv ITV; ss. auto_solve_time_rel.
Qed.

Lemma promise_split_I_dce_prsv
      prm_tgt sc_tgt mem_tgt loc from to val R ts val2 R2 prm_tgt' mem_tgt' inj lo
      prm_src sc_src mem_src
      (PROM_SPLIT: Memory.promise prm_tgt mem_tgt loc from to (Message.concrete val R)
                                prm_tgt' mem_tgt' (Memory.op_kind_split ts (Message.concrete val2 R2)))
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (INV: I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (PRM_LESS_TGT: Memory.le prm_tgt mem_tgt)
      (PRM_LESS_SRC: Memory.le prm_src mem_src)
      (CLOSED_MSG: Memory.closed_message (Message.concrete val R) mem_tgt')
      (MON_INJ: monotonic_inj inj)
      (MEM_AT_EQ: Mem_at_eq lo mem_tgt mem_src)
      (CLOSED_MEM: Memory.closed mem_tgt)
      (CLOSED_SC: Memory.closed_timemap sc_tgt mem_tgt):
  exists prm_src' mem_src' kind from' to' R' inj',
    <<PRM_ADD': Memory.promise prm_src mem_src loc from' to' (Message.concrete val R')
                               prm_src' mem_src' kind>> /\
    <<CLOSED_MSG: Memory.closed_message (Message.concrete val R') mem_src'>> /\
    <<MEM_AT_EQ': Mem_at_eq lo mem_tgt' mem_src'>> /\                          
    <<INCR_INJ': incr_inj inj inj'>> /\ 
    <<MON_INJ': monotonic_inj inj'>> /\
    <<INV': I_dce lo inj' (Build_Rss sc_tgt mem_tgt' sc_src mem_src')>> /\
    <<PROM_REL': promises_relation inj' lo prm_tgt' prm_src'>> /\                    
    <<CONCRETE_INCR_TGT: concrete_mem_incr mem_tgt mem_tgt'>> /\ 
    <<CONCTETE_INCR_SRC: concrete_mem_incr mem_src mem_src'>>.
Proof.
  inv PROM_SPLIT. des.
  symmetry in RESERVE. inv RESERVE. symmetry in RESERVEORIGINAL. inv RESERVEORIGINAL.
  destruct (lo loc) eqn: LOC_TYPE.
  - (* split promise on atomic location *)
    renames LOC_TYPE to AT_LOC. simpl in INV. des.
    assert (SRC_SPLIT_MSG: exists R2',
               Memory.get loc ts prm_src = Some (from, Message.concrete val2 R2')).
    {
      exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
      inv PROM_REL. inv H. exploit SOUND2; eauto. i. des.
      exploit ID_ATOMIC; eauto. ii; subst t'. 
      clear - GET0 x0 PRM_LESS_TGT PRM_LESS_SRC MEM_AT_EQ AT_LOC.
      eapply PRM_LESS_TGT in GET0.
      unfold Mem_at_eq in MEM_AT_EQ. exploit MEM_AT_EQ; eauto. ii. clear MEM_AT_EQ.
      unfold Mem_approxEq_loc in x. des.
      specialize (x from ts val2). des. exploit x; eauto.
      ii; des. exploit PRM_LESS_SRC; eauto. ii. rewrite x3 in x4. inv x4.
      eauto.
    }
    des1.
    assert (SRC_SPLIT_MEM: Memory.get loc ts mem_src = Some (from, Message.concrete val2 R2')).
    {
      clear - PRM_LESS_SRC SRC_SPLIT_MSG. eauto.
    }

    exploit split_succeed_wf; [eapply PROMISES | eauto..].
    ii; do 3 des1. inv MSG_WF.

    assert (INJ_NONE: inj loc to = None).
    {
      clear - INJ_MEM MEM. destruct (inj loc to) eqn:INJ; eauto.
      inv INJ_MEM. 
      exploit COMPLETE; eauto. ii; des.
      exploit Memory.split_get0; eauto. ii; des. rewrite x in GET. ss.
    }
    pose proof (identity_inj_incr) as NEW_INJ.
    specialize (NEW_INJ inj loc to). exploit NEW_INJ; eauto.
    clear NEW_INJ. intro NEW_INJ. des.
    assert (INCR_INJ: incr_inj inj inj').
    {
      clear - NEW_INJ0 INJ_NONE.
      subst. unfold incr_inj. ii. des_if; eauto.
      ss. des; subst. rewrite INJ_NONE in H; ss.
    }

    assert (SOUND_INJ': forall loc t f val_t R_t, Memory.get loc t mem_tgt' = Some (f, Message.concrete val_t R_t) ->
                                             exists t', inj' loc t = Some t').
    {
      clear - INJ_MEM INJ_NONE NEW_INJ0 MEM. ii. subst.
      des_if; eauto. ss.
      erewrite Memory.split_o in H; eauto. des_ifH H; ss.
      des1; subst. des1; tryfalse. des_ifH H. simpl in a.
      des1; subst.
      exploit Memory.split_get0; eauto. i. do 3 des1.
      inv INJ_MEM. exploit SOUND; eauto. ii; des; eauto.
      inv INJ_MEM.
      eapply SOUND in H. des; eauto.
    }
    assert (COMPLETE_INJ: forall t t' loc, inj' loc t = Some t' ->
                                      exists f val_t R_t, Memory.get loc t mem_tgt' = Some (f, Message.concrete val_t R_t)).
    {
      ii; subst. des_ifH H; eauto. simpl in a. des1. subst. inv H.
      clear - MEM. exploit Memory.split_get0; eauto. ii; des; eauto.
      simpl in o.
      erewrite Memory.split_o; eauto.
      des_if; eauto. simpl in o0.
      des_if; eauto.
      clear - INJ_MEM H. inv INJ_MEM.
      eapply COMPLETE in H. des; eauto.
    }
    assert (CLOSED_MSG_VIEW: forall released, R = Some released -> closed_viewInj inj' released).
    {
      ii; subst.
      eapply closed_viewInj_general; eauto.
      clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED; ss.
    }
    assert (CLOSED_MSG_VIEW_S: forall released, R = Some released ->
                                           exists released', ViewInj inj' released released').
    {
      clear - CLOSED_MSG_VIEW. ii. subst.
      exploit CLOSED_MSG_VIEW; eauto. ii.
      eapply closed_viewInj_implies_view; eauto.
    }

    assert (MSG_VIEW_S: exists R', opt_ViewInj inj' R R').
    {
      clear - CLOSED_MSG_VIEW_S. destruct R.
      exploit CLOSED_MSG_VIEW_S; eauto. ii; des.
      exists (Some released'). unfold opt_ViewInj. eauto.
      exists (@None View.t). econs; eauto.
    }
    destruct MSG_VIEW_S as (R' & MSG_VIEW_S).
    assert (MSG_TO_S: Memory.message_to (Message.concrete val R') loc to).
    { 
      inv TS. econs.
      eapply Message_wf_inj; eauto. destruct R; try solve [econs; eauto].
      simpl. eapply closed_viewInj_general; eauto.
      clear - CLOSED_MSG. inv CLOSED_MSG; eauto. inv CLOSED; ss.
      simpl. des_if; eauto. simpl in o. des1; ss.
    }

    assert (SPLIT_SRC: exists prm_src',
               Memory.split prm_src loc from to ts
                            (Message.concrete val R') (Message.concrete val2 R2') prm_src').
    {
      eapply Memory.split_exists; eauto.
      econs; eauto.
      eapply View_opt_wf_inj_prsv; eauto.
      destruct R. ss. eapply closed_viewInj_general; eauto.
      clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED. eauto.
      econs; eauto.
    }
    destruct SPLIT_SRC as (prm_src' & SPLIT_SRC).
    exploit Memory.split_exists_le; [eapply PRM_LESS_SRC | eapply SPLIT_SRC | eauto..].
    introv SPLIT_MEM_SRC. destruct SPLIT_MEM_SRC as (mem_src' & SPLIT_MEM_SRC).
    assert (MEM_INJ': MsgInj inj' mem_tgt' mem_src').
    {
      eapply split_msgInj_stable_concrete; eauto.
      subst inj'. des_if; eauto. simpl in o. des1; tryfalse.
    }
    assert (CLOSED_MSG_S: Memory.closed_message (Message.concrete val R') mem_src').
    {
      econs; eauto. destruct R'; eauto.
      destruct R; simpl in MSG_VIEW_S; tryfalse.
      inv CLOSED_MSG. inv CLOSED. econs.
      eapply closed_view_inj_prsv; eauto.
      clear - MEM_INJ'. ii. inv MEM_INJ'. exploit SOUND; eauto. ii; des.
      do 4 eexists. split; eauto.
    }

    exists prm_src' mem_src' (Memory.op_kind_split ts (Message.concrete val2 R2')).
    exists from to R' inj'.
    splits; eauto.
    {
      econs; eauto.
    }
    {
      eapply Mem_at_eq_split_concrete_prsv; eauto.
    }
    {
      ss. splits; eauto.
      eapply incr_inj_TMapInj; eauto. eapply closed_tm_to_closed_TMapInj; eauto.
      lets SPLIT_MEM_SRC': SPLIT_MEM_SRC. 
      ii. eapply memory_split_disj_loc_same with (loc0 := loc0) in SPLIT_MEM_SRC; eauto.
      unfold Memory.get in *.
      rewrite <- SPLIT_MEM_SRC in H.
      exploit TS_RSV; eauto.
      rewrite NEW_INJ0 in H0. des_ifH H0; eauto.
      simpl in a. des1; subst. inv H0. clear - H SPLIT_MEM_SRC'.
      exploit Memory.split_get0; eauto. ii. des1. unfold Memory.get in GET.
      rewrite H in GET. ss.
      ii. do 2 des1. exists to_r. split; eauto.
      introv ITV COVER'. eapply x0; eauto. inv COVER'.
      econs. 2: { eapply ITV0. }
      unfold Memory.get in *. rewrite <- SPLIT_MEM_SRC in GET. eauto.
      ii. subst. rewrite AT_LOC in H2. ss.
      ii. erewrite Memory.split_o in H; eauto.
      des_ifH H; eauto. tryfalse.
      des_ifH H; eauto. simpl in a. des1; subst. ss.
      ii. rewrite NEW_INJ0 in H0. des_ifH H0; eauto.
      simpl in a. des1; subst. inv H0. eauto.
      eapply Memory.split_closed; eauto.
    } 
    {
      eapply promises_relation_split; eauto.
      subst. des_if; eauto. simpl in o; ss. des1; ss.
    }
    split; eapply memory_split_concrete_mem_incr; eauto.
  - (* split promise on non-atomic location *)
    exploit Memory.split_get0; [eapply MEM | eauto..]. ii. do 3 des1.
    simpl in INV. do 5 des1.
    assert (NXT_SRC: exists ts' f_s val_s R_s,
               Memory.get loc ts' mem_src = Some (f_s, Message.concrete val_s R_s) /\
               inj loc ts = Some ts').
    {
      clear - INJ_MEM GET0.
      inv INJ_MEM. exploit SOUND; eauto. ii; des; eauto.
      do 4 eexists. eauto.
    }
    do 5 des1.
    exploit split_succeed_wf; eauto. ii; do 3 des1. clear GET3.

    (* find unused timestamp *)
    exploit TS_RSV; [eapply NXT_SRC | eauto..].
    {
      clear - TS23 GET0. eapply Memory.get_ts in GET0. des; subst.
      auto_solve_time_rel. pose proof (Time.bot_spec ts).
      eapply Time.le_lteq in H. des; eauto. subst. auto_solve_time_rel.
    }
    introv Unused_Timestamps. do 2 des1.

    (* find increasing injection *)
    assert (INJ_NONE: inj loc to = None).
    {
      clear - GET INJ_MEM. destruct (inj loc to) eqn:INJ_LOC; eauto.
      inv INJ_MEM. exploit COMPLETE; eauto. ii; des.
      rewrite GET in x. ss.
    }
    exploit wf_inj_incr; [ | eapply INJ_NONE | eauto..].
    {
      inv INJ_MEM; eauto.
    }
    {
      instantiate (1 := Time.middle to_r f_s). introv INJ_ORIGN LT.
      inv INJ_MEM. exploit COMPLETE; [eapply INJ_ORIGN | eauto..]. ii; des.
      exploit SOUND; eauto. ii; des. rewrite INJ_ORIGN in x0. symmetry in x0. inv x0.
      exploit inj_src_view_le_unused_timestamps; [eapply INJ_ORIGN | eapply x2 | eapply NXT_SRC | eauto..].
      auto_solve_time_rel.
      introv LE.
      eapply Time.middle_spec in Unused_Timestamps. des. auto_solve_time_rel.
    } 
    {
      introv INJ LT.
      destruct (Time.le_lt_dec ts ts0).
      {
        inv INJ_MEM. 
        exploit monotonic_inj_implies_le_prsv; [eapply MONOTONIC | eapply l | eauto..].
        introv LE'. clear - LE' NXT_SRC Unused_Timestamps.
        eapply memory_get_ts_le in NXT_SRC. eapply Time.middle_spec in Unused_Timestamps. des.
        cut (Time.le f_s ts'0). ii. auto_solve_time_rel.
        clear - NXT_SRC LE'. auto_solve_time_rel.
      }
      {
        clear - LT l INJ INJ_MEM TS12 TS23 GET0. inv INJ_MEM.
        exploit COMPLETE; [eapply INJ | eauto..]. ii; des. clear SOUND COMPLETE.
        exploit Memory.get_disjoint; [eapply GET0 | eapply x | eauto..]. ii; des; subst.
        auto_solve_time_rel. unfold Interval.disjoint in x1.
        specialize (x1 ts0). contradiction x1; eauto.
        econs; ss; eauto. clear - TS12 LT. auto_solve_time_rel.
        econs; eauto.
        econs; ss; eauto.
        eapply Memory.get_ts in x. des; subst. auto_solve_time_rel. eauto.
        eapply Time.le_lteq. eauto.
      }
    }
    introv NEW_INJ. do 3 des1.

    assert (SOUND_INJ': forall loc t f val_t R_t, Memory.get loc t mem_tgt' = Some (f, Message.concrete val_t R_t) ->
                                             exists t', inj' loc t = Some t').
    {
      clear - INJ_MEM INJ_NONE NEW_INJ0 MEM. ii. subst.
      des_if; eauto. ss.
      erewrite Memory.split_o in H; eauto. des_ifH H; ss.
      des1; subst. des1; tryfalse. des_ifH H. simpl in a.
      des1; subst.
      exploit Memory.split_get0; eauto. i. do 3 des1.
      inv INJ_MEM. exploit SOUND; eauto. ii; des; eauto.
      inv INJ_MEM.
      eapply SOUND in H. des; eauto.
    }
    assert (COMPLETE_INJ: forall t t' loc, inj' loc t = Some t' ->
                                      exists f val_t R_t, Memory.get loc t mem_tgt' = Some (f, Message.concrete val_t R_t)).
    {
      ii; subst. des_ifH H; eauto. simpl in a. des1. subst. inv H.
      clear - MEM. exploit Memory.split_get0; eauto. ii; des; eauto.
      simpl in o.
      erewrite Memory.split_o; eauto.
      des_if; eauto. simpl in o0.
      des_if; eauto.
      clear - INJ_MEM H. inv INJ_MEM.
      eapply COMPLETE in H. des; eauto.
    }
    assert (CLOSED_MSG_VIEW: forall released, R = Some released -> closed_viewInj inj' released).
    {
      ii; subst.
      eapply closed_viewInj_general; eauto.
      clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED; ss.
    }
    assert (CLOSED_MSG_VIEW_S: forall released, R = Some released ->
                                           exists released', ViewInj inj' released released').
    {
      clear - CLOSED_MSG_VIEW. ii. subst.
      exploit CLOSED_MSG_VIEW; eauto. ii.
      eapply closed_viewInj_implies_view; eauto.
    }

    assert (MSG_VIEW_S: exists R', opt_ViewInj inj' R R').
    {
      clear - CLOSED_MSG_VIEW_S. destruct R.
      exploit CLOSED_MSG_VIEW_S; eauto. ii; des.
      exists (Some released'). unfold opt_ViewInj. eauto.
      exists (@None View.t). econs; eauto.
    }
    destruct MSG_VIEW_S as (R' & MSG_VIEW_S). 
    assert (MSG_TO_S: Memory.message_to (Message.concrete val R') loc (Time.middle to_r f_s)).
    { 
      inv TS. econs.
      eapply Message_wf_inj; eauto. destruct R; try solve [econs; eauto].
      simpl. eapply closed_viewInj_general; eauto.
      clear - CLOSED_MSG. inv CLOSED_MSG; eauto. inv CLOSED; ss.
      simpl. des_if; eauto. simpl in o. des1; ss.
    }

    assert (ADD_MEM: exists mem_src', Memory.add mem_src loc (Time.middle to_r (Time.middle to_r f_s))
                                            (Time.middle to_r f_s) (Message.concrete val R') mem_src').
    {
      eapply Memory.add_exists; eauto.
      {
        clear - Unused_Timestamps0 Unused_Timestamps. ii.
        eapply Time.middle_spec in Unused_Timestamps. des.
        eapply Time.middle_spec in Unused_Timestamps. des. 
        eapply Unused_Timestamps0; eauto.
        instantiate (1 := x). econs; eauto; ss. inv LHS; ss.
        auto_solve_time_rel.
        inv LHS; ss. eapply Time.le_lteq. left. auto_solve_time_rel.
        econs. 2: { eapply RHS; eauto. } eauto.
      }
      {
        clear - Unused_Timestamps. eapply Time.middle_spec in Unused_Timestamps. des.
        eapply Time.middle_spec in Unused_Timestamps; des. eauto.
      }
      {
        inv MSG_WF. econs.
        eapply View_opt_wf_inj_prsv; eauto.
        destruct R. ss. eapply closed_viewInj_general; eauto.
        clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED. eauto.
        econs; eauto.
      } 
    }
    destruct ADD_MEM as (mem_src' & ADD_MEM_SRC).
    exploit Memory.add_exists_le; [eapply PRM_LESS_SRC | eapply ADD_MEM_SRC | eauto..].
    introv ADD_PRM_SRC. destruct ADD_PRM_SRC as (prm_src' & ADD_PRM_SRC).
    assert (MEM_INJ': MsgInj inj' mem_tgt' mem_src').
    {
      eapply split_add_msgInj_stable_concrete; eauto.
      subst inj'. des_if; eauto. simpl in o. des1; tryfalse.
    }
    assert (CLOSED_MSG_S: Memory.closed_message (Message.concrete val R') mem_src').
    {
      econs; eauto. destruct R'; eauto.
      destruct R; simpl in MSG_VIEW_S; tryfalse.
      inv CLOSED_MSG. inv CLOSED. econs.
      eapply closed_view_inj_prsv; eauto.
      clear - MEM_INJ'. ii. inv MEM_INJ'. exploit SOUND; eauto. ii; des.
      do 4 eexists. split; eauto.
    }

    exists prm_src' mem_src' Memory.op_kind_add.
    exists (Time.middle to_r (Time.middle to_r f_s)) (Time.middle to_r f_s).
    exists R' inj'.
    splits; eauto.
    {
      econs; eauto. ii. inv MSG.
      clear - GET3 Unused_Timestamps Unused_Timestamps0.
      eapply Time.middle_spec in Unused_Timestamps. des.
      exploit Memory.get_ts; eauto. ii; des; subst.
      rewrite x0 in Unused_Timestamps. auto_solve_time_rel.
      eapply not_cover_attach_contr; eauto.
      eapply Time.le_lteq; eauto.
    }
    {
      eapply Mem_at_eq_split_na_stable; eauto.
      eapply Mem_at_eq_reflexive; eauto.
      eapply Mem_at_eq_add_na_stable; eauto.
      eapply Mem_at_eq_reflexive; eauto.
    }
    {
      splits; eauto.
      (* sc mapping *)
      eapply incr_inj_TMapInj; eauto. eapply closed_tm_to_closed_TMapInj; eauto.

      (* Unused timestamps *)
      introv GET_SRC INJ'_GET LT' NON_ATOMIC_LOC.
      erewrite Memory.add_o in GET_SRC; eauto.
      des_ifH GET_SRC.
      { 
        simpl in a. des; subst. inv GET_SRC.
        exists to_r. split. eapply Time.middle_spec in Unused_Timestamps. des.
        eapply Time.middle_spec in Unused_Timestamps. des; eauto. 
        clear - Unused_Timestamps Unused_Timestamps0 ADD_MEM_SRC.
        introv ITV COVER. specialize (Unused_Timestamps0 ts).
        eapply Unused_Timestamps0; eauto.
        inv ITV. ss. econs; eauto. ss.
        eapply Time.middle_spec in Unused_Timestamps. des.
        eapply Time.middle_spec in Unused_Timestamps. des.
        clear - TO Unused_Timestamps2 Unused_Timestamps1.
        econs. cut (Time.lt ts  (Time.middle to_r f_s)). ii.
        auto_solve_time_rel. auto_solve_time_rel.
        eapply Cover.add_covered in COVER; eauto. des; eauto.
        clear - Unused_Timestamps ITV COVER0.
        inv ITV. ss. inv COVER0; ss.
        auto_solve_time_rel.
      }
      {
        simpl in o. subst inj'. des_ifH INJ'_GET; eauto.
        simpl in a. des; subst; ss. inv INJ'_GET. ss.
        destruct (Loc.eq_dec loc loc0); subst.
        {
          (* same location *)
          des1; ss. des1; ss. 
          destruct (Time.eq_dec to0 ts); subst.
          {
            rewrite NXT_SRC0 in INJ'_GET. inv INJ'_GET.
            rewrite NXT_SRC in GET_SRC. inv GET_SRC.
            exists (Time.middle to_r from'). split. eapply Time.middle_spec in Unused_Timestamps.
            des; eauto.
            introv ITV COVER. specialize (Unused_Timestamps0 ts0).
            eapply Unused_Timestamps0; eauto. econs; eauto. ss.
            eapply Time.middle_spec in Unused_Timestamps. des.
            inv ITV; ss. auto_solve_time_rel.
            ss. inv ITV; ss.
            eapply Cover.add_covered in COVER; eauto. des1; eauto.
            des1. clear - ITV COVER0. inv ITV; ss. inv COVER0; ss.
            auto_solve_time_rel.
          }
          {
            destruct (Time.le_lt_dec to0 ts).
            {
              eapply Time.le_lteq in l. des; subst; ss.
              exploit inj_src_view_le_unused_timestamps;
                [eapply INJ'_GET | eapply GET_SRC | eapply NXT_SRC | eapply NXT_SRC0 | eauto..].
              inv INJ_MEM; eauto.
              introv LE. exploit TS_RSV; [eapply GET_SRC | eauto..]. ii; des.
              exists to_r0. split; eauto. introv ITV' COVER. specialize (x0 ts0).
              eapply x0; eauto.
              eapply Cover.add_covered in COVER; eauto. des; eauto.
              clear - GET_SRC LE ITV' COVER0 Unused_Timestamps. inv COVER0; ss.
              eapply memory_get_ts_le in GET_SRC. clear TO. inv ITV'; ss. clear FROM0.
              eapply Time.middle_spec in Unused_Timestamps. des. clear Unused_Timestamps0.
              eapply Time.middle_spec in Unused_Timestamps. des. clear Unused_Timestamps0.
              cut (Time.lt ts0 (Time.middle to_r (Time.middle to_r f_s))).
              ii. auto_solve_time_rel. ii; auto_solve_time_rel.
              clear - TO GET_SRC LE Unused_Timestamps.
              cut (Time.le ts0 to_r). ii. auto_solve_time_rel.
              cut (Time.le ts0 to'). ii. auto_solve_time_rel. auto_solve_time_rel.
            }
            {
              exploit TS_RSV; [eapply GET_SRC | eauto..]. ii; des.
              exploit inj_src_view_le_unused_timestamps;
                [eapply NXT_SRC0 | eapply NXT_SRC | eapply GET_SRC | eauto..].
              inv INJ_MEM; eauto. introv LE.
              exists to_r0. split; eauto. introv ITV' COVER. specialize (x0 ts0).
              eapply x0; eauto.
              eapply Cover.add_covered in COVER; eauto. des; eauto.
              clear - NXT_SRC Unused_Timestamps LE ITV' COVER0.
              inv ITV'; ss. clear TO. inv COVER0; ss. clear FROM0.
              cut (Time.le ts0 to_r0). ii. auto_solve_time_rel.
              cut (Time.le ts0 ts'). ii. auto_solve_time_rel.
              eapply memory_get_ts_le in NXT_SRC.
              cut (Time.le ts0 f_s). ii. auto_solve_time_rel.
              eapply Time.middle_spec in Unused_Timestamps. des.
              econs. auto_solve_time_rel.
            }
          }
        }
        {
          (* disjoint loc *)
          exploit TS_RSV; eauto. ii. do 2 des1.
          exists to_r0. split; eauto.
          introv ITV COVER. specialize (x0 ts0). eapply x0; eauto.
          eapply Cover.add_covered in COVER; eauto. des1; eauto.
          des1; subst. des1; ss.
        }
      }

      (* reservation preservation *)
      clear - ADD_MEM_SRC NO_RSVs. introv GET.
      erewrite Memory.add_o in GET; eauto. des_ifH GET; eauto.
      ss.

      (* Identity injection on atomic location *)
      clear - NEW_INJ0 ID_ATOMIC LOC_TYPE. ii. subst.
      des_ifH H0; eauto. ss. des; subst; ss. tryfalse.

      (* closed memory *)
      eapply Memory.add_closed; eauto.
    }
    {
      eapply promises_relation_split_add; eauto.
      subst. des_if; eauto. simpl in o. des; ss.
    }
    split.
    eapply memory_split_concrete_mem_incr; eauto.
    eapply memory_add_concrete_mem_incr; eauto.
Qed.

Lemma promise_lower_I_dce_prsv
      prm_tgt sc_tgt mem_tgt loc from to val R val2 R2 prm_tgt' mem_tgt' inj lo
      prm_src sc_src mem_src inj0
      (PROM_SPLIT: Memory.promise prm_tgt mem_tgt loc from to (Message.concrete val R)
                                prm_tgt' mem_tgt' (Memory.op_kind_lower (Message.concrete val2 R2)))
      (PROM_REL: promises_relation inj0 lo prm_tgt prm_src)
      (INCR_INJ: incr_inj inj0 inj)
      (INV: I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (PRM_LESS_TGT: Memory.le prm_tgt mem_tgt)
      (PRM_LESS_SRC: Memory.le prm_src mem_src)
      (CLOSED_MSG: Memory.closed_message (Message.concrete val R) mem_tgt')
      (MON_INJ: monotonic_inj inj)
      (MEM_AT_EQ: Mem_at_eq lo mem_tgt mem_src)
      (CLOSED_MEM: Memory.closed mem_tgt)
      (CLOSED_SC: Memory.closed_timemap sc_tgt mem_tgt)
      (PRM_CONS: forall loc ts f val released,
          Memory.get loc ts prm_src = Some (f, Message.concrete val released) ->
          Time.lt f ts):
  exists prm_src' mem_src' from' to' R' msg',
    <<PRM_ADD': Memory.promise prm_src mem_src loc from' to' (Message.concrete val R')
                               prm_src' mem_src' (Memory.op_kind_lower msg')>> /\
    <<VIEW_INJ_REL: opt_ViewInj inj R R'>> /\
    <<CLOSED_MSG: Memory.closed_message (Message.concrete val R') mem_src'>> /\
    <<MEM_AT_EQ': Mem_at_eq lo mem_tgt' mem_src'>> /\                          
    <<INV': I_dce lo inj (Build_Rss sc_tgt mem_tgt' sc_src mem_src')>> /\
    <<PROM_REL': promises_relation inj0 lo prm_tgt' prm_src'>> /\                    
    <<CONCRETE_INCR_TGT: concrete_mem_incr mem_tgt mem_tgt'>> /\ 
    <<CONCTETE_INCR_SRC: concrete_mem_incr mem_src mem_src'>>.
Proof.
  inv PROM_SPLIT. do 2 des1. symmetry in RESERVE. inv RESERVE.
  exploit Memory.lower_get0; [eapply PROMISES | eauto..].
  ii. do 2 des1.
  assert (GET': exists from' to' R2',
             Memory.get loc to' prm_src = Some (from', Message.concrete val2 R2') /\
             inj loc to = Some to' /\ opt_ViewInj inj R2 R2').
  {
    clear - GET MEM PRM_LESS_TGT PRM_LESS_SRC INV PROM_REL INCR_INJ.
    exploit PRM_LESS_TGT; eauto. ii.
    unfold promises_relation in PROM_REL. des. inv PROM_REL.
    exploit SOUND2; eauto. ii; des.
    ss. des. eapply INCR_INJ in x0.
    inv INJ_MEM. exploit COMPLETE0; eauto. ii; des.
    exploit SOUND; eauto. ii; des. rewrite x0 in x3. symmetry in x3. inv x3.
    exploit PRM_LESS_SRC; eauto. ii.
    rewrite x5 in x3. inv x3.
    rewrite x in x2. inv x2.
    do 3 eexists. splits; eauto.
  }
  destruct GET' as (from' & to' & R2' & GET' & INJ_TO & OPT_VIEWINJ).
  assert (GET_MEM': Memory.get loc to' mem_src = Some (from', Message.concrete val2 R2')). eauto.
  assert (LT_ITV: Time.lt from' to').
  {
    clear - GET' PRM_CONS.
    exploit PRM_CONS; eauto.
  }

  simpl in INV. des.
  assert (SOUND_INJ': forall loc t f val_t R_t, Memory.get loc t mem_tgt' = Some (f, Message.concrete val_t R_t) ->
                                           exists t', inj loc t = Some t').
  {
    clear - INJ_MEM MEM. introv GET.
    inv INJ_MEM. erewrite Memory.lower_o in GET; eauto.
    des_ifH GET; ss. des1; subst. inv GET.
    exploit Memory.lower_get0; eauto. i. do 2 des1.
    exploit SOUND; eauto. ii; des; eauto.
    exploit SOUND; eauto. ii; des; eauto.
  }
  assert (COMPLETE_INJ: forall t t' loc, inj loc t = Some t' ->
                                    exists f val_t R_t, Memory.get loc t mem_tgt' = Some (f, Message.concrete val_t R_t)).
  {
    clear - INJ_MEM MEM. introv GET.
    inv INJ_MEM. erewrite Memory.lower_o; eauto.
    des_if; ss. des1; subst.
    exploit Memory.lower_get0; eauto. 
    exploit COMPLETE; eauto. ii; des; eauto.
  }
  assert (CLOSED_MSG_VIEW: forall released, R = Some released -> closed_viewInj inj released).
  {
    ii; subst.
    eapply closed_viewInj_general; eauto.
    clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED; ss.
  }
  assert (CLOSED_MSG_VIEW_S: forall released, R = Some released ->
                                         exists released', ViewInj inj released released').
  {
    clear - CLOSED_MSG_VIEW. ii. subst.
    exploit CLOSED_MSG_VIEW; eauto. ii.
    eapply closed_viewInj_implies_view; eauto.
  }

  assert (MSG_VIEW_S: exists R', opt_ViewInj inj R R').
  {
    clear - CLOSED_MSG_VIEW_S. destruct R.
    exploit CLOSED_MSG_VIEW_S; eauto. ii; des.
    exists (Some released'). unfold opt_ViewInj. eauto.
    exists (@None View.t). econs; eauto.
  }
  destruct MSG_VIEW_S as (R' & MSG_VIEW_S). 
  assert (MSG_TO_S: Memory.message_to (Message.concrete val R') loc to').
  { 
    inv TS. econs.
    eapply Message_wf_inj; eauto. destruct R; try solve [econs; eauto].
    simpl. eapply closed_viewInj_general; eauto.
    clear - CLOSED_MSG. inv CLOSED_MSG; eauto. inv CLOSED; ss.
  }

  assert (AT_LOC_LOWER: lo loc = Ordering.atomic -> (to = to' /\ from = from')).
  {
    clear - ID_ATOMIC MEM_AT_EQ GET PRM_LESS_TGT GET_MEM' INJ_TO.
    ii. exploit ID_ATOMIC; eauto. ii; subst. split; eauto.
    unfold Mem_at_eq in *. exploit MEM_AT_EQ; eauto. ii.
    unfold Mem_approxEq_loc in *. des.
    specialize (x from to' val2). des.
    eapply PRM_LESS_TGT in GET. exploit x; eauto. ii; des.
    rewrite GET_MEM' in x3. inv x3. eauto.
  }

  exploit lower_succeed_wf; eauto. i. do 3 des1. clear GET1 MSG_LE0.
  assert (LOWER_SRC_PROM: exists prm_src',
             Memory.lower prm_src loc from' to'
                          (Message.concrete val2 R2') (Message.concrete val R') prm_src').
  {
    inv MSG_WF.
    eapply Memory.lower_exists; eauto.
    econs; eauto. 
    eapply View_opt_wf_inj_prsv; eauto.
    destruct R; ss.
    eapply closed_viewInj_general; eauto.
    clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED. eauto.
    inv MSG_LE. econs; eauto.
    eapply view_opt_le_inj; eauto.
    destruct R; ss.
    eapply closed_viewInj_general; eauto.
    clear - CLOSED_MSG. inv CLOSED_MSG. inv CLOSED. eauto.
    eapply PRM_LESS_TGT in GET.
    eapply closed_optview_msginj_implies_closed_viewInj; eauto.
    eapply closed_mem_implies_closed_msg; eauto.
  }
  destruct LOWER_SRC_PROM as (prm_src' & LOWER_SRC_PROM).
  exploit Memory.lower_exists_le; [eapply PRM_LESS_SRC | eapply LOWER_SRC_PROM | eauto..].
  introv LOWER_MEM_SRC. destruct LOWER_MEM_SRC as (mem_src' & LOWER_MEM_SRC).
  assert (MEM_INJ': MsgInj inj mem_tgt' mem_src').
  {
    eapply lower_msgInj_stable_concrete; eauto.
    unfold incr_inj; ii; eauto.
  }
  assert (CLOSED_MSG_S: Memory.closed_message (Message.concrete val R') mem_src').
  {
    econs; eauto. destruct R'; eauto.
    destruct R; simpl in MSG_VIEW_S; tryfalse.
    inv CLOSED_MSG. inv CLOSED. econs.
    eapply closed_view_inj_prsv; eauto.
    clear - MEM_INJ'. ii. inv MEM_INJ'. exploit SOUND; eauto. ii; des.
    do 4 eexists. split; eauto.
  }

  exists prm_src' mem_src' from' to' R' (Message.concrete val2 R2').
  splits; eauto. 
  {
    destruct (lo loc) eqn:LOC_TYPE.
    exploit AT_LOC_LOWER; eauto. ii; des1; subst.
    exploit Mem_at_eq_lower_concrete_prsv;
      [eapply MEM_AT_EQ | eapply MEM | eapply LOWER_MEM_SRC | eauto..].
    eapply Mem_at_eq_lower_na_stable; eauto.
    eapply Mem_at_eq_reflexive; eauto.
    eapply Mem_at_eq_lower_na_stable; eauto.
    eapply Mem_at_eq_reflexive; eauto.
  }
  {
    destruct (lo loc) eqn:LOC_TYPE.
    {
      (* atomic location *)
      simpl. splits; eauto.
      lets LOWER_MEM_SRC': LOWER_MEM_SRC. 
      ii. eapply memory_lower_disj_loc_stable with (loc0 := loc0) in LOWER_MEM_SRC; eauto.
      unfold Memory.get in *.
      rewrite <- LOWER_MEM_SRC in H.
      exploit TS_RSV; eauto.
      ii. do 2 des1. exists to_r. split; eauto.
      introv ITV COVER'. eapply x0; eauto.
      eapply Cover.lower_covered in LOWER_MEM_SRC'; eauto.
      eapply LOWER_MEM_SRC'; eauto.
      ii. subst. rewrite LOC_TYPE in H2; ss.
      ii. erewrite Memory.lower_o in H; eauto.
      des_ifH H; eauto. tryfalse.
      eapply Memory.lower_closed; eauto.
    }
    {
      (* non-atomic location *)
      ss. splits; eauto.
      
      introv MSG_SRC_GET INJ LT NON_ATOMIC.
      erewrite Memory.lower_o in MSG_SRC_GET; eauto.
      des_ifH MSG_SRC_GET; eauto. simpl in a. des; subst.
      inv MSG_SRC_GET. inv INJ_MEM.
      exploit COMPLETE; eauto. ii; des. exploit SOUND; eauto. ii; des.
      rewrite INJ in x0. symmetry in x0. inv x0.
      exploit TS_RSV; eauto. ii; des.
      exists to_r. rewrite GET_MEM' in x2. inv x2. split; eauto.
      introv ITV COVER'. specialize (x3 ts). eapply x3; eauto.
      eapply Cover.lower_covered with (mem2 := mem_src'); eauto.
      exploit TS_RSV; eauto. ii. do 2 des1.
      exists to_r. split; eauto.
      introv ITV COVER'. specialize (x0 ts). eapply x0; eauto.
      eapply Cover.lower_covered with (mem2 := mem_src'); eauto.

      introv GET_RSV. erewrite Memory.lower_o in GET_RSV; eauto.
      des_ifH GET_RSV; ss. eauto.

      eapply Memory.lower_closed; eauto.
    }
  }
  {
    eapply promises_relation_lower; eauto.
  }
  eapply memory_lower_concrete_mem_incr; eauto.
  eapply memory_lower_concrete_mem_incr; eauto.
Qed.

Lemma promise_cancel_I_dce_prsv
      prm_tgt sc_tgt mem_tgt loc from to msg prm_tgt' mem_tgt' inj lo
      prm_src sc_src mem_src inj0
      (PROM_CANCEL: Memory.promise prm_tgt mem_tgt loc from to msg prm_tgt' mem_tgt' Memory.op_kind_cancel)
      (PROM_REL: promises_relation inj0 lo prm_tgt prm_src)
      (INCR_INJ: incr_inj inj0 inj)
      (INV: I_dce lo inj (Build_Rss sc_tgt mem_tgt sc_src mem_src))
      (PRM_LESS_TGT: Memory.le prm_tgt mem_tgt)
      (PRM_LESS_SRC: Memory.le prm_src mem_src)
      (MON_INJ: monotonic_inj inj)
      (MEM_AT_EQ: Mem_at_eq lo mem_tgt mem_src):
  exists prm_src' mem_src' from' to',
    <<PRM_CCL': (Memory.promise prm_src mem_src loc from' to' Message.reserve
                                prm_src' mem_src' Memory.op_kind_cancel) \/
                (prm_src = prm_src' /\ mem_src = mem_src')>> /\
    <<MEM_AT_EQ': Mem_at_eq lo mem_tgt' mem_src'>> /\                          
    <<INV': I_dce lo inj (Build_Rss sc_tgt mem_tgt' sc_src mem_src')>> /\
    <<PROM_REL': promises_relation inj0 lo prm_tgt' prm_src'>> /\                    
    <<CONCRETE_INCR_TGT: concrete_mem_incr mem_tgt mem_tgt'>> /\ 
    <<CONCTETE_INCR_SRC: concrete_mem_incr mem_src mem_src'>>.
Proof.
  destruct (lo loc) eqn:LOC_TYPE.
  - (* atomic location *)
    inv PROM_CANCEL; eauto.
    exploit Memory.remove_get0; [eapply PROMISES | eauto..].
    i. des1.
    assert (GET_SRC: Memory.get loc to prm_src = Some (from, Message.reserve)).
    { 
      clear - GET PROM_REL LOC_TYPE.
      inv PROM_REL. eapply H0; eauto.
    }
    exploit PRM_LESS_SRC; eauto. introv GET_SRC_MEM.
    exploit Memory.remove_exists; [eapply GET_SRC | eauto..].
    introv CANCEL_SRC_PRM. destruct CANCEL_SRC_PRM as (prm_src' & CANCEL_SRC_PRM).
    exploit Memory.remove_exists_le; eauto.
    introv CANCEL_SRC_MEM. destruct CANCEL_SRC_MEM as (mem_src' & CANCEL_SRC_MEM).
    exists prm_src' mem_src' from to.
    splits; eauto.
    {
      eapply Mem_at_eq_cancel_prsv; eauto.
    }
    {
      ss. des. splits; eauto.
      eapply cancel_msg_stable; eauto.

      introv GET' INJ_TO GT_BOT NA_LOC.
      erewrite Memory.remove_o in GET'; eauto.
      des_ifH GET'; ss.
      exploit TS_RSV; eauto. i. do 2 des1.
      exists to_r. split; eauto.
      introv ITV COVER'.
      eapply x0; eauto.
      inv COVER'. econs. 2: { eapply ITV0. }
      eapply memory_remove_disj_loc_same with (loc0 := loc0) in CANCEL_SRC_MEM; eauto.
      unfold Memory.get in *. rewrite CANCEL_SRC_MEM; eauto.
      ii; subst. rewrite LOC_TYPE in NA_LOC. ss.

      introv GET'. erewrite Memory.remove_o in GET'; eauto.
      des_ifH GET'; ss. eauto.

      eapply Memory.cancel_closed; eauto.
    }
    {
      eapply promises_relation_cancel_at; eauto.
    }
    eapply memory_cancel_concrete_mem_incr; eauto.
    eapply memory_cancel_concrete_mem_incr; eauto.
  - (* non-atomic location *)
    inv PROM_CANCEL.
    exists prm_src mem_src from to.
    splits; eauto.
    {
      eapply Mem_at_eq_remove_na_stable; eauto.
    }
    {
      ss. des. splits; eauto.
      eapply cancel_msg_stable'; eauto.
    }
    {
      eapply promises_relation_cancel_na; eauto.
    }
    eapply memory_cancel_concrete_mem_incr; eauto.
    ii. exists f R. splits.
    eapply View.View.opt_le_PreOrder_obligation_1; eauto.
    auto_solve_time_rel.
    eauto.
    introv ITV. inv ITV; ss. auto_solve_time_rel.
Qed.
