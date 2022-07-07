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
Require Import CorrectOpt.
Require Import ValAnalysis.
Require Import ConstProp.

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
Require Import ConstPropProofMState.
Require Import MemoryProps.
Require Import MemoryMerge.

Require Import Lib_Ordering.
Require Import Lib_MsgMapping.
Require Import Lib_View.
Require Import Lib_Memory.
Require Import Lib_Step.
Require Import promiseCertifiedAux.
Require Import ConsistentLemmas.
Require Import ConfigStepConvertion.

(* const prop specific lemmas *)
Lemma eval_expr_ae_bot:
  forall e aregs
    (EQ: eval_expr_ae e aregs = LVal.bot),
  exists r, VALSET.get r aregs = LVal.bot.
Proof.
  induction e; ii; ss.
  - destruct aregs; ss; eauto. exists xH. eauto.
  - destruct aregs; ss; eauto.
  - destruct aregs; ss. exists xH. eauto.
    destruct (eval_expr_ae e1 (VALSET.Top_except t)) eqn:EVAL_E1; ss.
    destruct (eval_expr_ae e2 (VALSET.Top_except t)) eqn:EVAL_E2; ss.
Qed.

Lemma val_interp_read
      R tview mem r loc or ae lo v ts released
      (VAL_INTERP: val_interp R tview mem ae lo)
      (AVAL: forall v', eval_loc_ae loc (snd ae) = LVal.VAL v' -> v = v')
      (TS: forall v', or = Ordering.plain -> eval_loc_ae loc (snd ae) = LVal.VAL v' ->
                 ts = View.pln (TView.cur tview) loc)
      (LOC_TYPE: or <> Ordering.plain -> lo loc = Ordering.atomic):
  val_interp (RegFun.add r v R) (TView.read_tview tview loc ts released or) mem
             (transf_instr (Inst.load r loc or) ae) lo.
Proof.
  unfold transf_instr. destruct ae as (aregs & amem).
  pose proof (nonatomic_or_atomic or) as ORD.
  des.
  {
    assert (ORD': Ordering.le Ordering.acqrel or = false). subst; eauto.
    rewrite ORD'. clear ORD'.
    subst.
    unfold val_interp in *. des; ss.
    split.
    {
      unfold sem_val_reg in *. ii. specialize (VAL_INTERP r0).
      destruct (Reg.eq_dec r r0); subst.

      rewrite VALSET.gsspec; eauto.
      2: { ii; subst. rewrite VALSET.get_bot in VAL_INTERP. ss. }
      2: { ii. unfold sem_val_loc in *. specialize (VAL_INTERP0 loc).
           unfold eval_loc_ae in H. rewrite H in VAL_INTERP0. ss. }
      des_if; ss.
      destruct (eval_loc_ae loc amem) eqn:EVAL_ALOC; ss.
      exploit AVAL; eauto. ii; subst.
      rewrite RegFun.add_spec_eq; eauto.
      clear - VAL_INTERP0 EVAL_ALOC. unfold sem_val_loc, eval_loc_ae in *.
      specialize (VAL_INTERP0 loc). rewrite EVAL_ALOC in VAL_INTERP0. ss.

      rewrite VALSET.gsspec; eauto.
      2: { ii; subst. rewrite VALSET.get_bot in VAL_INTERP. ss. }
      2: { ii. unfold sem_val_loc in *. specialize (VAL_INTERP0 loc).
           unfold eval_loc_ae in H. rewrite H in VAL_INTERP0. ss. }
      des_if; subst; tryfalse.
      rewrite RegFun.add_spec_neq; eauto.
    }
    {
      unfold sem_val_loc in *. ii.
      specialize (VAL_INTERP0 loc0).
      destruct (VALSET.get loc0 amem) eqn:GET_AMEM; simpl in VAL_INTERP0; tryfalse.
      eauto.
      do 3 des1.
      destruct (Loc.eq_dec loc loc0); subst.

      unfold eval_loc_ae in TS. exploit TS; eauto. i; subst. clear TS.
      simpl.
      assert (ORD1: Ordering.le Ordering.acqrel Ordering.plain = false). eauto.
      rewrite ORD1. ss.
      unfold View.singleton_ur_if; ss.
      assert (ORD2: Ordering.le Ordering.relaxed Ordering.plain = false). eauto.
      rewrite ORD2. ss.
      unfold TimeMap.bot, TimeMap.join; ss.
      repeat (rewrite Time_join_bot; ss). eauto.
      exploit le_strongrlx_tview_read_disj_loc_cur; eauto.
      {
        instantiate (1 := Ordering.plain). eauto.
      }
      instantiate (1 := tview). instantiate (2 := ts). instantiate (1 := released).
      i. des1. rewrite CUR_PLN. eauto.
    }
  }
  destruct (Ordering.le Ordering.acqrel or) eqn:ORD_ACQREL.
  {
    unfold val_interp in *. des.
    split; ss.
    {
      unfold sem_val_reg in *. ii. specialize (VAL_INTERP r0).
      rewrite VALSET.gsspec; eauto.
      2: { ii; subst. rewrite VALSET.get_bot in VAL_INTERP. ss. }
      2: { ii. inv H. }
      des_if; ss. rewrite RegFun.add_spec_neq; eauto.
    }
    {
      unfold sem_val_loc in *. ii.
      specialize (VAL_INTERP0 loc0).
      destruct amem.
      rewrite VALSET.get_bot in VAL_INTERP0. simpl in VAL_INTERP0. ss.
      simpl mem_to_top. rewrite VALSET.get_top. simpl. eauto.
    }
  }
  {
    unfold val_interp in *. des.
    split; ss.
    {
      unfold sem_val_reg in *. ii. 
      specialize (VAL_INTERP r0).
      rewrite VALSET.gsspec; eauto.
      2: { ii; subst. rewrite VALSET.get_bot in VAL_INTERP. ss. }
      2: { ii. unfold sem_val_loc in *. specialize (VAL_INTERP0 loc).
           unfold eval_loc_ae in H. rewrite H in VAL_INTERP0. ss. }
      des_if; subst.
      destruct (eval_loc_ae loc amem) eqn:GET_AMEM; ss.
      exploit AVAL; eauto. ii; subst.
      rewrite RegFun.add_spec_eq; eauto.
      clear - VAL_INTERP0 GET_AMEM. unfold sem_val_loc in *.
      specialize (VAL_INTERP0 loc).
      unfold eval_loc_ae in GET_AMEM. rewrite GET_AMEM in VAL_INTERP0. ss.
      rewrite RegFun.add_spec_neq; eauto.
    }
    {
      unfold sem_val_loc in *. ii.
      specialize (VAL_INTERP0 loc0).
      destruct (VALSET.get loc0 amem) eqn:GET_AMEM; tryfalse. eauto.
      destruct (Loc.eq_dec loc loc0); subst.

      des. exploit LOC_TYPE; eauto. ii. rewrite VAL_INTERP1 in x; ss.
      exploit le_strongrlx_tview_read_disj_loc_cur; eauto.
      {
        instantiate (1 := or).
        destruct or; eauto; tryfalse.
      }
      instantiate (1 := tview). instantiate (2 := ts). instantiate (1 := released).
      i. des. rewrite CUR_PLN. eauto.
    }
  }
Qed.

Lemma val_interp_write
      R tview mem loc to ow ord sc ae lo e
      (VAL_INTERP: val_interp R tview mem ae lo)
      (WRITABLE: Time.lt (View.pln (TView.cur tview) loc) to)
      (AVAL: forall v, eval_expr_ae e (fst ae) = LVal.VAL v -> lo loc = Ordering.nonatomic ->
                  exists from released, Memory.get loc to mem = Some (from, Message.concrete v released))
      (LOC_TYPE: (ow <> Ordering.plain /\ lo loc = Ordering.atomic) \/
                 (ow = Ordering.plain /\ lo loc = Ordering.nonatomic)):
  val_interp R (TView.write_tview tview sc loc to ord) mem
             (transf_instr (Inst.store loc e ow) ae) lo.
Proof.
  unfold val_interp in *. des1.
  unfold transf_instr. destruct ae as (aregs & amem).
  pose proof (nonatomic_or_atomic ow) as ORD. 
  des1.
  {
    subst. ss. split; eauto.
    unfold sem_val_loc in *. ii.
    destruct (Loc.eq_dec loc loc0); subst.
    {
      rewrite VALSET.gsspec; eauto.
      2: { ii; subst. specialize (VAL_INTERP0 loc0).
           rewrite VALSET.get_bot in VAL_INTERP0. ss. }
      2: { ii. exploit eval_expr_ae_bot; eauto. i. des1.
           clear - VAL_INTERP x0. unfold sem_val_reg in *.
           specialize (VAL_INTERP r). rewrite x0 in VAL_INTERP; ss. }
      des_if; ss.
      destruct (eval_expr_ae e aregs) eqn:EVAL_AEXPR; ss.
      exploit AVAL; eauto. des; subst; ss; eauto.
      i. do 2 des1.
      des1. des1; ss.
      des1.
      unfold TimeMap.join, TimeMap.singleton; simpl.
      rewrite Loc_add_eq; simpl.
      rewrite TimeFacts.le_join_r; eauto.
      auto_solve_time_rel.
      exploit eval_expr_ae_bot; eauto. i. des1.
      clear - VAL_INTERP x0. unfold sem_val_reg in *.
      specialize (VAL_INTERP r). rewrite x0 in VAL_INTERP; ss.
    }
    {
      rewrite VALSET.gsspec; eauto.
      2: { ii; subst. specialize (VAL_INTERP0 loc0).
           rewrite VALSET.get_bot in VAL_INTERP0. ss. }
      2: { ii. exploit eval_expr_ae_bot; eauto. i. des1.
           clear - VAL_INTERP x0. unfold sem_val_reg in *.
           specialize (VAL_INTERP r). rewrite x0 in VAL_INTERP; ss. }
      des_if; subst; tryfalse.
      specialize (VAL_INTERP0 loc0).
      destruct (VALSET.get loc0 amem) eqn: GET_AMEM; tryfalse; eauto.
      do 3 des1. clear n0.
      exploit le_relacq_tview_disj_loc_cur; eauto.
      instantiate (1 := tview). instantiate (3 := sc).
      instantiate (2 := to). instantiate (1 := ord).
      i. des1. rewrite CUR_PLN. eauto.
    }
  }
  {
    assert (TRANS: match ow with
                   | Ordering.plain => (aregs, VALSET.set loc (eval_expr_ae e aregs) amem)
                   | _ => (aregs, amem)
                   end = (aregs, amem)).
    {
      destruct ow; ss.
    } 
    unfold ValLat.t. unfold vmem in *. 
    rewrite TRANS. ss. clear TRANS.
    split; eauto.
    unfold sem_val_loc in *. ii.
    specialize (VAL_INTERP0 loc0).
    destruct (VALSET.get loc0 amem) eqn:GET_AMEM; ss.
    do 3 des1. des; ss.
    destruct (Loc.eq_dec loc loc0); subst; tryfalse.
    unfold TimeMap.join, TimeMap.singleton.
    rewrite Loc_add_neq; eauto. unfold LocFun.init.
    rewrite Time_join_bot. eauto.
  }
Qed.

Lemma val_interp_fence_rel
      R tview mem sc ae lo or ow
      (VAL_INTERP: val_interp R tview mem ae lo)
      (NOT_ACQ: Ordering.le or Ordering.strong_relaxed)
      (NOT_SC: ow <> Ordering.seqcst):
  val_interp R (TView.write_fence_tview (TView.read_fence_tview tview or) sc ow)
             mem (transf_instr Inst.fence_rel ae) lo.
Proof.
  unfold val_interp in *. des1.
  destruct ae as (aregs & amem); ss.
  split; eauto.
  unfold sem_val_loc in *. ii.
  specialize (VAL_INTERP0 loc).
  destruct (VALSET.get loc amem) eqn:GET_AMEM; ss. des.
  assert (Ordering.le Ordering.seqcst ow = false).
  {
    destruct ow; ss.
  }
  rewrite H.
  assert (Ordering.le Ordering.acqrel or = false).
  {
    destruct or; ss.
  }
  rewrite H0. eauto.
Qed.

Lemma val_interp_mem_concrete_incr
      R tview mem ae lo mem'
      (VAL_INTERP: val_interp R tview mem ae lo)
      (CONCRETE_MORE: forall loc ts f val R,
          Memory.get loc ts mem = Some (f, Message.concrete val R) ->
          exists f' R', Memory.get loc ts mem' = Some (f', Message.concrete val R')):
  val_interp R tview mem' ae lo.
Proof.
  unfold val_interp in *. des. split; eauto.
  destruct ae as (aregs & amem); ss.
  unfold sem_val_loc in *; ss. ii.
  specialize (VAL_INTERP0 loc).
  destruct (VALSET.get loc amem) eqn:GET_AMEM; ss.
  des.
  exploit CONCRETE_MORE; eauto. ii; des; eauto.
Qed.

Lemma val_interp_amem_to_top
      R tview mem tview' mem' aregs amem lo
      (VAL_INTERP: val_interp R tview mem (aregs, amem) lo):
  val_interp R tview' mem' (aregs, mem_to_top amem) lo.
Proof.
  unfold val_interp in *; ss. des.
  split; eauto.
  unfold sem_val_loc in *; ii.
  destruct amem.
  specialize (VAL_INTERP0 loc).
  rewrite VALSET.get_bot in VAL_INTERP0. ss.
  specialize (VAL_INTERP0 loc).
  unfold mem_to_top.
  rewrite VALSET.get_top. simpl. eauto.
Qed.

Lemma val_interp_expr_eval:
  forall e R tview mem aregs amem lo val
    (VAL_INTERP: val_interp R tview mem (aregs, amem) lo)
    (EVAL_EXPR: eval_expr_ae e aregs = LVal.VAL val),
    RegFile.eval_expr e R = val.
Proof.
  induction e; ii; eauto; ss.
  destruct aregs; ss. inv EVAL_EXPR. eauto.
  destruct aregs. tryfalse.
  unfold val_interp in *. des.
  unfold sem_val_reg in *.
  specialize (VAL_INTERP reg). unfold fst in VAL_INTERP.
  rewrite EVAL_EXPR in VAL_INTERP. eauto.
  destruct aregs; tryfalse.
  destruct (eval_expr_ae e1 (VALSET.Top_except t)) eqn:EVAL_EXPR1; tryfalse.
  destruct (eval_expr_ae e2 (VALSET.Top_except t)) eqn:EVAL_EXPR2; tryfalse.
  eapply IHe1 in EVAL_EXPR1; eauto.
  eapply IHe2 in EVAL_EXPR2; eauto.
  rewrite EVAL_EXPR1, EVAL_EXPR2. inv EVAL_EXPR; eauto.
Qed.

Lemma val_interp_assign_vtop
      R tview mem aregs amem v r lo
      (VAL_INTERP: val_interp R tview mem (aregs, amem) lo):
  val_interp (RegFun.add r v R) tview mem
             (VALSET.set r LVal.top aregs, amem) lo.
Proof.
  unfold val_interp in *. des. ss. split; eauto.
  unfold sem_val_reg in *; ss. ii.
  rewrite VALSET.gsspec; eauto.
  2: { ii; subst. specialize (VAL_INTERP r0). rewrite VALSET.get_bot in VAL_INTERP. ss. }
  2: { ii. inv H. }
  des_if; ss. rewrite RegFun.add_spec_neq; eauto.
  specialize (VAL_INTERP r0). eauto.
Qed.

Lemma val_interp_assign_val
      R tview mem aregs amem v r lo
      (VAL_INTERP: val_interp R tview mem (aregs, amem) lo):
  val_interp (RegFun.add r v R) tview mem
             (VALSET.set r (LVal.VAL v) aregs, amem) lo.
Proof.
  unfold val_interp in *. des. ss. split; eauto.
  unfold sem_val_reg in *; ss. ii.
  rewrite VALSET.gsspec; eauto.
  2: { ii; subst. specialize (VAL_INTERP r0). rewrite VALSET.get_bot in VAL_INTERP. ss. }
  2: { ii. inv H. }
  des_if; ss; subst.
  rewrite RegFun.add_spec_eq; eauto.
  rewrite RegFun.add_spec_neq; eauto.
  specialize (VAL_INTERP r0). eauto.
Qed.
  
(* memory lemmas *)
Lemma mem_add_rsv_id_inj
      mem1 loc from to mem2
      (ADD: Memory.add mem1 loc from to Message.reserve mem2):
  (spec_inj mem1) = (spec_inj mem2).
Proof.
  eapply functional_extensionality; eauto. ii.
  eapply functional_extensionality; eauto. ii.
  renames x to loc0, x0 to to0.
  unfold spec_inj.
  destruct (Memory.get loc0 to0 mem1) eqn:GET_MEM; ss.
  destruct p. destruct t0; ss.
  exploit Memory.add_get1; eauto. ii; des.
  rewrite x0. ss.
  destruct (Memory.get loc0 to0 mem2) eqn:GET_MEM'; ss.
  destruct p. destruct t1; ss.
  erewrite Memory.add_o in GET_MEM'; eauto.
  des_ifH GET_MEM'; ss.
  rewrite GET_MEM in GET_MEM'. tryfalse.
  destruct (Memory.get loc0 to0 mem2) eqn:GET_MEM'; ss.
  destruct p. destruct t0; ss.
  erewrite Memory.add_o in GET_MEM'; eauto.
  des_ifH GET_MEM'; ss. 
  rewrite GET_MEM in GET_MEM'. ss.
Qed.

Lemma mem_add_id_inj
      mem1 loc from to val R mem2
      (ADD: Memory.add mem1 loc from to (Message.concrete val R) mem2):
  incr_inj (spec_inj mem1) (spec_inj mem2).
Proof.
  unfold incr_inj, spec_inj; ii.
  destruct (Memory.get loc0 t mem1) eqn:GET_MEM; ss.
  destruct p. destruct t1; ss. inv H.
  exploit Memory.add_get1; eauto. ii.
  rewrite x0; eauto.
Qed.

Lemma mem_split_id_inj
      mem1 loc from to ts val1 R1 val2 R2 mem2
      (SPLIT: Memory.split mem1 loc from to ts (Message.concrete val1 R1) (Message.concrete val2 R2) mem2):
  incr_inj (spec_inj mem1) (spec_inj mem2).
Proof.
  unfold incr_inj, spec_inj; ii.
  destruct (Memory.get loc0 t mem1) eqn:GET_MEM; ss.
  destruct p. destruct t1; ss. inv H.
  exploit Memory.split_get1; eauto. ii. des.
  rewrite GET2; ss.
Qed.

Lemma mem_lower_id_inj'
      mem1 loc from to val1 R1 val2 R2 mem2
      (LOWER: Memory.lower mem1 loc from to (Message.concrete val1 R1) (Message.concrete val2 R2) mem2):
  (spec_inj mem1) = (spec_inj mem2).
Proof.
  eapply functional_extensionality; eauto. ii.
  eapply functional_extensionality; eauto. ii.
  renames x to loc0, x0 to to0.
  unfold spec_inj.
  destruct (Memory.get loc0 to0 mem1) eqn:GET_MEM; ss.
  destruct p. destruct t0; ss.
  exploit Memory.lower_get1; eauto. ii; des.
  inv MSG_LE. rewrite GET2. eauto.
  destruct (Memory.get loc0 to0 mem2) eqn:GET_MEM'; ss.
  destruct p. destruct t1; ss.
  erewrite Memory.lower_o in GET_MEM'; eauto.
  des_ifH GET_MEM'; ss. des; subst.
  exploit Memory.lower_get0; eauto. ii; des.
  rewrite GET_MEM in GET. ss.
  rewrite GET_MEM in GET_MEM'. ss.
  destruct (Memory.get loc0 to0 mem2) eqn:GET_MEM'; ss.
  destruct p. destruct t0; ss.
  erewrite Memory.lower_o in GET_MEM'; eauto.
  des_ifH GET_MEM'; ss. des; subst.
  exploit Memory.lower_get0; eauto. ii; des.
  rewrite GET_MEM in GET. ss.
  rewrite GET_MEM in GET_MEM'. ss.
Qed.

Lemma mem_lower_id_inj
      mem1 loc from to val1 R1 val2 R2 mem2
      (LOWER: Memory.lower mem1 loc from to (Message.concrete val1 R1) (Message.concrete val2 R2) mem2):
  incr_inj (spec_inj mem1) (spec_inj mem2).
Proof.
  eapply mem_lower_id_inj' in LOWER.
  rewrite <- LOWER. ii; eauto.
Qed.

Lemma mem_cancel_id_inj
      mem1 loc from to mem2
      (CCL: Memory.remove mem1 loc from to Message.reserve mem2):
  (spec_inj mem1) = (spec_inj mem2).
Proof.
  eapply functional_extensionality; eauto. ii.
  eapply functional_extensionality; eauto. ii.
  renames x to loc0, x0 to to0.
  unfold spec_inj.
  destruct (Memory.get loc0 to0 mem1) eqn:GET_MEM; ss.
  destruct p. destruct t0; ss.
  exploit Memory.remove_get1; eauto. ii; des; subst.
  exploit Memory.remove_get0; eauto. ii; des.
  rewrite GET_MEM in GET. ss.
  rewrite GET2. ss.
  exploit Memory.remove_get1; eauto. ii; des; subst.
  destruct (Memory.get loc to mem2) eqn:GET_MEM'; ss.
  destruct p. destruct t1; ss.
  erewrite Memory.remove_o in GET_MEM'; eauto.
  des_ifH GET_MEM'; ss.
  rewrite GET_MEM in GET_MEM'. ss.
  rewrite GET2. eauto.
  destruct (Memory.get loc0 to0 mem2) eqn:GET_MEM'; ss.
  destruct p. destruct t0; eauto.
  erewrite Memory.remove_o in GET_MEM'; eauto.
  des_ifH GET_MEM'; ss.
  rewrite GET_MEM in GET_MEM'. ss.
Qed.

Lemma Local_write_id_inj
      lc1 sc1 mem1 loc from to val Rr Rw ord lc2 sc2 mem2 kind lo
      (WRITE: Local.write_step lc1 sc1 mem1 loc from to val Rr Rw ord lc2 sc2 mem2 kind lo):
  incr_inj (spec_inj mem1) (spec_inj mem2) /\
  (forall l f t v R, Memory.get l t (Local.promises lc2) = Some (f, Message.concrete v R) ->
                exists f' R', Memory.get l t (Local.promises lc1) = Some (f', Message.concrete v R')).
Proof.
  inv WRITE. inv WRITE0. inv PROMISE; ss.
  - (* add *)
    lets MEM': MEM. eapply mem_add_id_inj in MEM'.
    split; eauto. ii.
    exploit MemoryMerge.add_remove; [eapply PROMISES | eapply REMOVE | eauto..].
    ii; subst. eauto.
  - (* split *)
    des; subst. inv RESERVE.
    lets MEM': MEM. eapply mem_split_id_inj in MEM'; eauto.
    split; eauto. ii. 
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss.
    erewrite Memory.split_o in H; eauto.
    des_ifH H; ss. des1. subst. des1; ss.
    des_ifH H; ss. des1; subst. inv H.
    exploit Memory.split_get0; eauto. i. do 3 des1. eauto.
    eauto.
  - (* lower *)
    des; subst.
    lets MEM': MEM. eapply mem_lower_id_inj in MEM'; eauto.
    split; eauto.
    ii.
    erewrite Memory.remove_o in H; eauto.
    des_ifH H; ss.
    erewrite Memory.lower_o in H; eauto.
    des_ifH H; ss. des1; subst. des1; ss. eauto.
Qed. 

Lemma Local_promise_id_inj
      lc1 mem1 loc from to msg lc2 mem2 kind
      (WRITE: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind):
  incr_inj (spec_inj mem1) (spec_inj mem2) /\
  (forall msg, kind = Memory.op_kind_lower msg -> (spec_inj mem1) = (spec_inj mem2)) /\
  (kind = Memory.op_kind_cancel -> (spec_inj mem1) = (spec_inj mem2)).
Proof.
  inv WRITE. inv PROMISE.
  - (* add *)
    destruct msg.
    eapply mem_add_id_inj in MEM; eauto.
    split; eauto. split; ii; tryfalse.
    eapply mem_add_rsv_id_inj in MEM; eauto.
    rewrite <- MEM. splits; ii; tryfalse; eauto.
  - (* split *)
    des; subst.
    eapply mem_split_id_inj in MEM; eauto.
    split; eauto. split; ii; tryfalse.
  - (* lower *)
    des; subst.
    exploit lower_succeed_wf; eauto. ii; des. inv MSG_LE.
    eapply mem_lower_id_inj' in MEM; eauto.
    rewrite <- MEM. splits; eauto.
    ii; eauto.
  - (* cancel *)
    eapply mem_cancel_id_inj in MEM; eauto.
    rewrite <- MEM. split; ii; eauto.
Qed.
    
(******************************************************)
Lemma atomic_or_out_step_case
      inj lo b te pf
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_cp inj lo b
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (TGT_STEP: Thread.step lo pf te 
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt'))
      (AT_OR_OUT: ThreadEvent.is_at_or_out_step te):
  exists state_src' tview_src' prm_src' sc_src' mem_src' inj',
    Thread.program_step te lo 
                        (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
                        (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
    incr_inj inj inj' /\ 
    match_state_cp inj' lo true
                   (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                   (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src').
Proof.
  inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
  lets INV': INV. unfold I_cp in INV'. simpl in INV'. do 2 des1.
  subst.
  inv TGT_STEP. inv STEP. simpl in AT_OR_OUT; tryfalse.
  destruct BB_src; simpl in STEP;
    try solve [inv STEP; inv STATE; ss; destruct te; ss].
  destruct c; simpl in STEP.
  - (* skip: contradiction *)
    inv STEP. inv STATE; tryfalse. inv BLK.
    destruct te; simpl in H0; tryfalse.
  - (* assign: contradiction *)
    assert (ASSIGN: exists e', match eval_expr_ae rhs (fst ae) with
                          | LVal.VAL v => Inst.assign lhs (Inst.expr_val v)
                          | _ => Inst.assign lhs rhs
                          end = Inst.assign lhs e').
    {
      destruct (eval_expr_ae rhs (fst ae)); eauto.
    }
    des1. rewrite ASSIGN in STEP.
    inv STEP. inv STATE; tryfalse. destruct te; simpl in H0; tryfalse.
  - (* load *)
    pose proof (nonatomic_or_atomic or) as NA_AT_LOC.
    destruct NA_AT_LOC as [NA_LOC | AT_LOC].

    (* na loc: contradiction *)
    subst or. 
    destruct (VALSET.get loc (snd ae)) eqn:GET_ALOC.
    inv STEP. inv STATE; tryfalse. inv BLK.
    destruct te; simpl in H0; tryfalse. inv H0.
    simpl in AT_OR_OUT. tryfalse.
    inv STEP. inv STATE; tryfalse. inv BLK.
    destruct te; tryfalse.
    inv STEP. inv STATE; tryfalse. inv BLK.
    destruct te; tryfalse. simpl in H0. inv H0.
    simpl in AT_OR_OUT. tryfalse.

    (* at loc *)
    assert (TGT_INST: match or with
                      | Ordering.plain =>
                        match VALSET.get loc (snd ae) with
                        | LVal.VAL v => Inst.assign lhs (Inst.expr_val v)
                        | _ => Inst.load lhs loc or
                        end
                      | _ => Inst.load lhs loc or
                      end = Inst.load lhs loc or).
    {
      clear - AT_LOC. destruct or; ss.
    }
    rewrite TGT_INST in STEP. clear TGT_INST.
    inv STEP. inv STATE; tryfalse. symmetry in BLK. inv BLK.
    destruct te; simpl in H0; tryfalse. symmetry in H0. inv H0.
    eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt' (spec_inj mem_src).
    splits.
    {
      (* source step *)
      econs; eauto. simpl. econs; eauto.
    }
    {
      (* incr inj *)
      clear - ATM_BIT. des; subst; eauto.
      unfold incr_inj; ii; eauto.
    }
    {
      (* match state *)
      inv LOCAL. inv LOCAL0. simpl in LC2. inv LC2.
      econs; eauto.

      (* match state tlocal *)
      econs; eauto. econs; eauto.
      eapply val_interp_read; eauto.
      {
        clear - AT_OR_OUT LO AI_INTERP. ss.
        pose proof (nonatomic_or_atomic or) as NA_AT_LOC.
        destruct NA_AT_LOC as [NA_LOC | AT_LOC]; subst; tryfalse.
        unfold val_interp in *. des.
        unfold sem_val_loc in *. ii.
        specialize (AI_INTERP0 loc). unfold eval_loc_ae in H; rewrite H in AI_INTERP0.
        des. rewrite AI_INTERP1 in LO. destruct or; ss.
      }
      {
        clear - AT_OR_OUT. ii; subst; ss.
      }
      {
        clear - LO. ii. destruct (lo loc) eqn:LOC_TYPE; ss.
      }
      introv GET_PRM. eapply PRM_INDOM in GET_PRM.
      clear - ATM_BIT GET_PRM. des; subst; eauto.
      eapply local_wf_read; eauto.
    }
  - (* store *)
    pose proof (nonatomic_or_atomic ow) as NA_AT_LOC.
    destruct NA_AT_LOC as [NA_LOC | AT_LOC].

    (* na loc: contradiction *)
    inv STEP. inv STATE; tryfalse. inv BLK. destruct te; simpl in H0; tryfalse.
    inv H0. simpl in AT_OR_OUT. tryfalse.

    (* at loc *)
    inv STEP. inv STATE; tryfalse. inv BLK. destruct te; simpl in H0; tryfalse. inv H0.
    inv LOCAL. 
    exploit Local_write_id_inj; eauto.
    introv INJ_MEM'. destruct INJ_MEM' as (INCR_INJ' & PROM'). simpl in PROM'.
    eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'. exists (spec_inj mem_tgt').
    splits.
    {
      (* source steps *)
      econs; eauto. simpl. econs; eauto.
    }
    {
      (* inj incr *)
      clear - ATM_BIT INCR_INJ'.
      eapply incr_inj_transitivity; eauto.
      des; subst; eauto. ss.
    }
    {
      (* match state *)
      econs; eauto.
      {
        (* invariant *)
        unfold I_cp. ss.
      }
      {
        (* match state tlocal *)
        econs; eauto. econs; eauto.
        inv LOCAL0. simpl in LC2. inv LC2.
        eapply val_interp_write; eauto.
        {
          eapply val_interp_mem_concrete_incr; eauto.
          ii. eapply write_step_concrete_msg_prsv; eauto.
        }
        {
          clear - LOCAL_WF_TGT WRITABLE. inv WRITABLE; ss.
          inv LOCAL_WF_TGT; ss. inv TVIEW_WF. inv CUR.
          unfold TimeMap.le in PLN_RLX. specialize (PLN_RLX loc0).
          auto_solve_time_rel.
        }
        {
          introv EVAL_AEXPR LOC_NA. clear - LOC_NA LO AT_OR_OUT. ss.
          rewrite LOC_NA in LO. destruct ord; ss.
        }
        {
          clear - LO AT_OR_OUT. ss.
          destruct (lo loc0) eqn:LOC_TYPE; ss.
          destruct ord; ss; eauto; try solve [left; split; [ii; ss | eauto]].
          destruct ord; ss; eauto; try solve [left; split; [ii; ss | eauto]].
        }
        {
          exploit local_wf_write; eauto.
          introv LOCAL_WF_TGT'. clear - LOCAL_WF_TGT'.
          inv LOCAL_WF_TGT'; ss. introv GET_PRM_TGT.
          eapply PROMISES in GET_PRM_TGT.
          unfold spec_inj. rewrite GET_PRM_TGT; eauto.
        }
      }
      {
        (* local wf tgt *)
        eapply local_wf_write; eauto.
      }
      {
        (* sc closed *)
        inv LOCAL0. simpl in LC2. inv LC2. ss. 
        eapply concrete_incr_closed_tm_prsv with (mem := mem_src); eauto.
        ii.
        eapply write_step_concrete_msg_prsv with (loc := loc0); eauto.
        econs; eauto.
        instantiate (3 := Local.mk tview_src prm_src). ss; eauto.
        simpl. eauto. ss; eauto.
      }
      {
        (* memory closed *)
        eapply write_step_closed_mem; eauto.
      }
    }
  - (* print *)
    inv STEP. inv STATE; tryfalse. inv BLK.
    destruct te; simpl in H0; tryfalse. inv H0.
    eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt' (spec_inj mem_tgt').
    splits.
    {
      (* source step *)
      econs; eauto. simpl. econs; eauto.
    }
    {
      (* incr inj *)
      clear - ATM_BIT LOCAL.
      inv LOCAL.
      des; subst; eauto; ss.
    }
    {
      (* match state *)
      inv LOCAL. inv LOCAL0; ss. inv LC2.
      econs; eauto. ss.
      econs; eauto. econs; eauto.
      destruct ae as (aregs & amem); simpl.
      eapply val_interp_amem_to_top; eauto.
      ii. clear - PRM_INDOM ATM_BIT H.
      eapply PRM_INDOM in H. des; subst; eauto.
      eapply local_wf_fence; eauto.
      inv LOCAL_WF_TGT; ss.
      exploit TViewFacts.read_fence_future; eauto.
      instantiate (1 := Ordering.seqcst). i. des1.
      exploit TViewFacts.write_fence_future; eauto.
      instantiate (1 := Ordering.seqcst). i. do 2 des1. eauto.
    }
  - (* cas *)
    inv STEP. inv STATE; tryfalse.
    {
      inv BLK. destruct te; simpl in H0; ss. inv H0.
      inv LOCAL.
      exploit Local_write_id_inj; eauto.
      introv INJ'. destruct INJ' as (INCR_INJ' & PRM').
      
      eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt' (spec_inj mem_tgt').
      splits.
      {
        (* source step *)
        econs; eauto. simpl. 
        eapply State.step_cas_same; eauto.
      }
      {
        (* incr inj *)
        clear - ATM_BIT INCR_INJ'.
        eapply incr_inj_transitivity; eauto.
        des; subst; eauto. ss.
      }
      {
        (* match state *)
        econs; eauto. ss.

        (* match state tlocal *)
        econs; eauto. econs; eauto. ss.
        inv LOCAL1. simpl in LOCAL2. inv LOCAL2. simpl in LC2. inv LC2. ss.
        lets AI_INTERP': AI_INTERP.
        eapply val_interp_read with (ts := tsr) in AI_INTERP; eauto.
        2: { instantiate (1 := Int.one). clear - LO ATOMIC AI_INTERP. 
              introv EVAL_AMEM. unfold val_interp in *.
              destruct ae as (aregs & amem); ss. des.
              unfold sem_val_loc, eval_loc_ae in *.
              specialize (AI_INTERP0 loc). rewrite EVAL_AMEM in AI_INTERP0.
              des. rewrite AI_INTERP1 in LO. ss. 
        }
        2: { instantiate (1 := ordr). clear - ATOMIC. ii; subst. ss. }
        instantiate (1 := r) in AI_INTERP. instantiate (1 := releasedr) in AI_INTERP.
        eapply val_interp_mem_concrete_incr with (mem' := mem_tgt') in AI_INTERP; eauto.
        2: { ii. eapply write_step_concrete_msg_prsv; eauto.
             econs; eauto. instantiate (3 := Local.mk (TView.read_tview tview_src loc tsr releasedr ordr) prm_src).
             simpl. eauto. simpl. eauto. simpl. eauto. }
        eapply val_interp_write in AI_INTERP; eauto. 
        2: { instantiate (1 := tsw). exploit local_wf_read; eauto.
             instantiate (3 := ordr). econs; eauto.
             introv LOCAL_WF_TGT'. simpl in LOCAL_WF_TGT'.
             clear - LOCAL_WF_TGT' WRITABLE. inv WRITABLE. inv LOCAL_WF_TGT'; ss.
             inv TVIEW_WF; ss. inv CUR; ss. unfold TimeMap.le in PLN_RLX.
             specialize (PLN_RLX loc). auto_solve_time_rel.
        }
        2: { instantiate (1 := ew0). clear - AT. ii; tryfalse.
        }
        instantiate (2 := sc_src) in AI_INTERP.
        instantiate (1 := ordw) in AI_INTERP.
        clear - AI_INTERP AI_INTERP' ATOMIC. unfold val_interp in *. des.
        destruct ae as (aregs & amem).
        split.
        {
          clear - AI_INTERP AI_INTERP'0 ATOMIC. ss. unfold sem_val_reg in *; ss. ii.
          des_if; ss. specialize (AI_INTERP r0).
          assert (match ordr with
                  | Ordering.plain =>
                    (VALSET.set r LVal.top aregs,
                     VALSET.set loc (eval_expr_ae ew0 (VALSET.set r LVal.top aregs)) (mem_to_top amem))
                  | _ => (VALSET.set r LVal.top aregs, mem_to_top amem)
                  end = (VALSET.set r LVal.top aregs, mem_to_top amem)).
          {
            destruct ordr; ss.
          }
          unfold ValLat.t in *. unfold vreg, vmem in *. unfold VALSET.t in *.
          rewrite H in AI_INTERP.
          eauto.
          specialize (AI_INTERP r0).
          assert (match ordr with
                  | Ordering.plain =>
                    (VALSET.set r (eval_loc_ae loc amem) aregs,
                     VALSET.set loc (eval_expr_ae ew0 (VALSET.set r (eval_loc_ae loc amem) aregs)) amem)
                  | _ => (VALSET.set r (eval_loc_ae loc amem) aregs, amem)
                  end = (VALSET.set r (eval_loc_ae loc amem) aregs, amem)).
          {
            destruct ordr; ss.
          }
          unfold ValLat.t in *. unfold vreg, vmem in *. unfold VALSET.t in *.
          rewrite H in AI_INTERP. clear H.
          rewrite VALSET.gsspec; eauto.
          2: { ii; subst. ss. }
          2: { ii. inv H; ss. }
          des_if; ss; eauto.
          rewrite VALSET.gsspec in AI_INTERP; eauto.
          2: { ii; subst. ss. }
          2: { ii. unfold sem_val_loc, eval_loc_ae in *; ss.
               specialize (AI_INTERP'0 loc). rewrite H in AI_INTERP'0. ss. }
          des_ifH AI_INTERP; ss.
        } 
        {
          unfold sem_val_loc in *; ss. des_if; ss.
          ii. destruct amem.
          specialize (AI_INTERP'0 loc). ss.
          unfold mem_to_top. rewrite VALSET.get_top. ss.
          ii.
          rewrite VALSET.gsspec.
          2: { ii; subst. specialize (AI_INTERP'0 loc).
               clear - AI_INTERP'0. rewrite VALSET.get_bot in AI_INTERP'0. ss.
          }
          2: { ii. inv H. }
          des_if; ss.
          specialize (AI_INTERP0 loc0).
          assert (match ordr with
                  | Ordering.plain =>
                    (VALSET.set r (eval_loc_ae loc amem) aregs,
                     VALSET.set loc (eval_expr_ae ew0 (VALSET.set r (eval_loc_ae loc amem) aregs)) amem)
                  | _ => (VALSET.set r (eval_loc_ae loc amem) aregs, amem)
                  end = (VALSET.set r (eval_loc_ae loc amem) aregs, amem)).
          {
            destruct ordr; ss; eauto.
          }
          unfold ValLat.t, vreg, vmem, VALSET.t in *.
          rewrite H in AI_INTERP0; clear H. eauto.
        }

        (* promise *)
        exploit local_wf_read; eauto. introv LOCAL_WF_READ.
        exploit local_wf_write; eauto. introv LOCAL_WF_WRITE.
        clear - LOCAL_WF_WRITE. ii. inv LOCAL_WF_WRITE; ss.
        eapply PROMISES in H. unfold spec_inj. rewrite H; ss. eauto.

        (* local wf *)
        exploit local_wf_read; eauto. introv LOCAL_WF_READ.
        exploit local_wf_write; eauto.

        (* closed sc timemap *)
        inv LOCAL2. inv LC2. ss. 
        eapply concrete_incr_closed_tm_prsv with (mem := mem_src); eauto.
        ii.
        eapply write_step_concrete_msg_prsv with (loc := loc); eauto.

        (* memory closed *)
        exploit local_wf_read; eauto. introv LOCAL_WF_READ.
        eapply write_step_closed_mem; [| eapply LOCAL2 | eauto..].
        inv LOCAL1; ss.
        eapply closed_mem_implies_closed_msg; eauto.
      }
    }
    {
      inv BLK. destruct te; simpl in H0; ss. inv H0.
      inv LOCAL.
      eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt' (spec_inj mem_tgt').
      splits.
      {
        (* source step *)
        econs; eauto. eapply State.step_cas_flip; eauto.
      }
      {
        (* incr inj *)
        clear - ATM_BIT. des; subst; ss; eauto.
      }
      {
        (* match state *)
        econs; eauto.

        (* match state tlocal *)
        econs; eauto. econs; eauto. inv LOCAL0. simpl in LC2. inv LC2.
        lets AI_INTERP': AI_INTERP.
        eapply val_interp_read with (ts := ts) in AI_INTERP; eauto.
        2: { instantiate (1 := Int.zero). instantiate (1 := loc).
             clear - LO ATOMIC AI_INTERP. 
             introv EVAL_AMEM. unfold val_interp in *.
             destruct ae as (aregs & amem); ss. des.
             unfold sem_val_loc, eval_loc_ae in *.
             specialize (AI_INTERP0 loc). rewrite EVAL_AMEM in AI_INTERP0.
             des. rewrite AI_INTERP1 in LO. ss. 
        }
        2: { instantiate (1 := ord). clear - ATOMIC. ii; subst. ss. }
        instantiate (1 := r) in AI_INTERP.
        instantiate (1 := released) in AI_INTERP.
        clear - AI_INTERP AI_INTERP'.
        unfold val_interp in *; des. destruct ae as (aregs & amem). split; ss.
        {
          des_if; ss. unfold sem_val_reg in *. ii.
          specialize (AI_INTERP r0).
          rewrite VALSET.gsspec; eauto.
          2: { ii; subst. specialize (AI_INTERP' r0).
               rewrite VALSET.get_bot in AI_INTERP'. ss. }
          2: { ii. inv H. }
          des_if; ss.
          rewrite VALSET.gsspec in AI_INTERP; eauto.
          2: { ii; subst. specialize (AI_INTERP' r0).
               rewrite VALSET.get_bot in AI_INTERP'. ss. }
          des_ifH AI_INTERP; ss.
          clear - AI_INTERP'0. unfold sem_val_loc, eval_loc_ae in *.
          specialize (AI_INTERP'0 loc). ii. rewrite H in AI_INTERP'0. ss.
        }
        {
          unfold sem_val_loc in *. ii. des_if; ss.
          destruct amem.
          specialize (AI_INTERP'0 loc).
          rewrite VALSET.get_bot in AI_INTERP'0. ss.
          unfold mem_to_top. rewrite VALSET.get_top; eauto. ss.
          rewrite VALSET.gsspec; eauto.
          2: { ii; subst. specialize (AI_INTERP0 loc0). ss. }
          2: { ii. inv H. }
          des_if; ss. specialize (AI_INTERP0 loc0). eauto.
        }
        clear - LO. ii. destruct (lo loc) eqn:LOC_TYPE; ss.

        (* promise *)
        exploit local_wf_read; eauto. introv LOCAL_WF_READ.
        clear - LOCAL_WF_READ. ii. inv LOCAL_WF_READ; ss.
        eapply PROMISES in H. unfold spec_inj. rewrite H; ss. eauto.

        (* local wf *)
        eapply local_wf_read; eauto.
      }
    }
  - (* fence rel *)
    inv STEP. inv STATE; tryfalse. inv BLK.
    destruct te; simpl in H0; tryfalse. inv H0.
    inv LOCAL.
    eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt' (spec_inj mem_tgt').
    splits.
    {
      (* source step *)
      econs; eauto. econs; eauto.
    }
    {
      (* incr inj *)
      clear - ATM_BIT. des; subst; ss. 
    }
    {
      (* match state *)
      econs; eauto. ss.

      (* match state tlocal *)
      econs; eauto. econs; eauto.
      inv LOCAL0. simpl in LC2. inv LC2.
      eapply val_interp_fence_rel; eauto. ii; ss.

      (* promise *)
      inv LOCAL0. simpl in LC2. inv LC2.
      clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; ss.
      introv GET_PRM. eapply PROMISES in GET_PRM.
      unfold spec_inj. rewrite GET_PRM; eauto.

      (* local wf *)
      eapply Local_wf_fence_not_sc; eauto. ii; ss.

      (* closed sc timemap *)
      inv LOCAL0. simpl in LC2. inv LC2. simpl.
      inv LOCAL_WF_TGT; ss.
    }
  - (* fence acq *)
    inv STEP. inv STATE; tryfalse. inv BLK.
    destruct te; simpl in H0; tryfalse. inv H0.
    inv LOCAL.
    eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt' (spec_inj mem_tgt').
    splits.
    {
      (* source step *)
      econs; eauto. econs; eauto.
    }
    {
      (* incr inj *)      
      clear - ATM_BIT. des; subst; ss.
    }
    {
      (* match state *)
      econs; eauto. ss.

      (* match state tlocal *)
      econs; eauto. econs; eauto.
      destruct ae as (aregs & amem); simpl.
      eapply val_interp_amem_to_top; eauto.

      (* promise *)
      inv LOCAL0; ss. inv LC2.
      ii. eapply PRM_INDOM in H. des; subst; eauto.

      (* local wf *)
      inv LOCAL0. inv LC2.
      eapply local_wf_fence; eauto.

      (* closed sc timestamp *)
      inv LOCAL0. simpl in LC2. inv LC2. simpl.
      inv LOCAL_WF_TGT; ss.
    }
  - (* fence sc *)
    inv STEP. inv STATE; tryfalse. inv BLK.
    destruct te; simpl in H0; tryfalse. inv H0.
    inv LOCAL.
    eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt' (spec_inj mem_tgt').
    splits.
    {
      (* source step *)
      econs; eauto. econs; eauto.
    }
    {
      (* incr inj *)      
      clear - ATM_BIT. des; subst; ss.
    }
    {
      (* match state *)
      inv LOCAL0. inv LC2.
      econs; eauto. ss.

      (* match state tlocal *)
      econs; eauto. econs; eauto.
      destruct ae as (aregs & amem); simpl.
      eapply val_interp_amem_to_top; eauto.

      (* promise *)
      ii. eapply PRM_INDOM in H. des; subst; eauto.

      (* local wf *)
      eapply local_wf_fence; eauto.

      (* closed sc timestamp *)
      inv LOCAL_WF_TGT; ss.
      exploit TViewFacts.read_fence_future; eauto. 
      instantiate (1 := Ordering.relaxed). i. des1.
      exploit TViewFacts.write_fence_future; eauto.
      instantiate (1 := Ordering.seqcst). i. do 2 des1. eauto.
    }
Qed.

Lemma silent_step_case
      inj lo b
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_cp inj lo b
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (TGT_STEP: Thread.program_step ThreadEvent.silent lo
                                     (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                                     (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')):
  exists state_src' tview_src' prm_src' sc_src' mem_src',
    Thread.na_step lo 
                   (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
                   (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
    match_state_cp inj lo false
                   (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                   (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src').
Proof.
  inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
  lets INV': INV. unfold I_cp in INV'. simpl in INV'. do 2 des1.
  subst. inv TGT_STEP. simpl in STATE.
  destruct BB_src.
  - (* jmp *)
    simpl in STATE. inv LOCAL.
    inv STATE; tryfalse. symmetry in BLK. inv BLK.
    renames b' to BB_tgt'.
    exploit transf_cdhp_prop; eauto.
    introv NXT_BB.
    destruct NXT_BB as (BB_src' & ae_pblk' & NXT_BB_src & ANALY_BLK & TRANS_BB & NXT').
    eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
    splits.
    {
      (* source step *)
      eapply Thread.na_tau_step_intro; eauto.
      econs; eauto. simpl. eapply State.step_jmp; eauto.
    }
    {
      (* match state *)
      econs; eauto.

      (* match state tlocal *)
      econs; eauto.
      econs. eapply FUNC_ANALYSIS. eauto.
      subst ae_pblk'. eauto.
      simpl in LINK. exploit LINK; eauto. introv GE.
      eapply ge_val_interp_prsv; eauto. eauto.
      rewrite ANALY_BLK. eauto.
      clear - ATM_BIT. des; subst; ss; eauto.
    }
  - (* call *)
    simpl in STATE. inv LOCAL.
    inv STATE; tryfalse. symmetry in BLK. inv BLK.
    renames ch0 to C_tgt1, b2 to BB_tgt1, b' to BB_tgt'.
    exploit transf_cdhp_prop; eauto.
    introv NXT_BB.
    destruct NXT_BB as (BB_src' & ae_pblk' & NXT_BB_src & ANALY_BLK & TRANS_BB & NXT').
    destruct (Prog_src ! f) eqn: PROG_SRC_F.
    {
      destruct f0 as (C_src', f1').
      exploit transform_prog_proper; eauto. i. do 2 des1.
      rewrite FIND_FUNC in x0. inv x0.
      exploit transform_func_init; eauto.
      introv TGT_FUN_ENTRY.
      destruct TGT_FUN_ENTRY as (BB_src1 & afunc' & SRC_FUNC_ENTRY & FUNC_ANALYSIS' & TRANS_CDHP' & FID).
      subst f1'.

      eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
      splits.
      {
        (* source step *)
        eapply Thread.na_tau_step_intro; eauto.
        econs; eauto. simpl. eapply State.step_call; eauto.
      }
      {
        (* match state *)
        exploit transf_cdhp_prop; eauto.
        introv ENTRY_F'. do 5 des1. subst ae_pblk.
        rewrite SRC_FUNC_ENTRY in ENTRY_F'. inv ENTRY_F'.
        econs; eauto.

        (* match state tlocal *)
        econs; eauto.
        econs. eapply FUNC_ANALYSIS'. eauto. eauto.
        exploit ValDS.analyze_func_entry1; eauto.
        eapply transf_blk_first; eauto.
        introv GE_TOP.
        eapply val_ge_top; eauto.
        eauto.
        eauto.
        econs; eauto.
        simpl in LINK. ii.
        destruct ae as (aregs & amem). simpl in LINK.
        exploit LINK; eauto. introv GET_TOP.
        destruct amem.
        clear - AI_INTERP. unfold val_interp in *. des; ss.
        unfold sem_val_loc in *; ss.
        unfold mem_to_top in GET_TOP.
        econs; eauto.
        eapply ge_val_interp_prsv; eauto.
        clear - AI_INTERP. unfold val_interp in *; ss. des.
        split; eauto.
        eapply vloc_ge_top; eauto. eapply VALSET.ge_refl; eauto. ss.
        clear - ATM_BIT. des; subst; ss; eauto.
      }
    }
    {
      exploit transform_prog_proper_none; eauto.
      ii. rewrite FIND_FUNC in x0; ss.
    }
  - (* be *)
    simpl in STATE. inv LOCAL.
    inv STATE; tryfalse. symmetry in BLK. inv BLK.
    des1.
    {
      renames b' to BB_tgt'. des1.
      exploit transf_cdhp_prop; eauto.
      introv NXT_BB.
      destruct NXT_BB as (BB_src' & ae_pblk' & NXT_BB_src & ANALY_BLK & TRANS_BB & NXT').
      eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
      splits.
      {
        (* source step *)
        eapply Thread.na_tau_step_intro; eauto.
        econs; eauto. simpl. eapply State.step_be; eauto.
      }
      {
        (* match state *)
        econs; eauto. econs; eauto.
        econs. eapply FUNC_ANALYSIS. eauto.
        subst ae_pblk'. eauto.
        simpl in LINK. exploit LINK. left. eauto. eauto.
        introv GE.
        eapply ge_val_interp_prsv; eauto. eauto.
        subst ae_pblk'. eauto.
        clear - ATM_BIT. des; subst; eauto.
      }
    }
    {
      renames b' to BB_tgt'. des1.
      exploit transf_cdhp_prop; eauto.
      introv NXT_BB.
      destruct NXT_BB as (BB_src' & ae_pblk' & NXT_BB_src & ANALY_BLK & TRANS_BB & NXT').
      eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
      splits.
      {
        (* source step *)
        eapply Thread.na_tau_step_intro; eauto.
        econs; eauto. simpl. eapply State.step_be; eauto.
      }
      {
        (* match state *)
        econs; eauto. econs; eauto.
        econs. eapply FUNC_ANALYSIS. eauto.
        subst ae_pblk'. eauto.
        simpl in LINK. exploit LINK. right. eauto. eauto.
        introv GE.
        eapply ge_val_interp_prsv; eauto. eauto.
        subst ae_pblk'. eauto.
        clear - ATM_BIT. des; subst; eauto.
      }
    }
  - (* ret *)
    simpl in STATE. inv LOCAL.
    inv STATE; tryfalse. clear BLK. inv STK_FRAMES. renames cont0 to cont_tgt0.
    eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
    splits.
    {
      (* source step *)
      eapply Thread.na_tau_step_intro; eauto.
      econs; eauto. simpl. eapply State.step_ret; eauto.
    }
    {
      (* match state *)
      econs; eauto. econs; eauto.
      clear - ATM_BIT. des; subst; eauto.
    }
  - (* instr *)
    destruct c; destruct ae as (aregs & amem); simpl in STATE;
      try solve [inv STATE; tryfalse].
    + (* skip *)
      inv LOCAL. inv STATE; tryfalse. inv BLK.
      eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
      splits.
      {
        (* source execution *)
        eapply Thread.na_tau_step_intro; eauto.
        econs; eauto. eapply State.step_skip; eauto.
      }
      {
        (* match state *)
        econs; eauto. econs; eauto. econs; eauto.
        clear - ATM_BIT. des; subst; eauto.
      }
    + (* assign *)
      inv LOCAL.
      destruct (eval_expr_ae rhs aregs) eqn:EVAL_AEXPR.
      {
        inv STATE; tryfalse. inv BLK.
        eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
        splits.
        {
          (* source execution *)
          eapply Thread.na_tau_step_intro; eauto.
          econs; eauto. eapply State.step_assign; eauto.
        }
        {
          (* match state *)
          econs; eauto. econs; eauto. econs; eauto.
          eapply val_interp_assign_vtop; eauto.
          simpl in LINK. rewrite EVAL_AEXPR in LINK. eauto.
          clear - ATM_BIT. des; subst; eauto.
        }
      }
      {
        inv STATE; tryfalse. inv BLK.
        eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
        splits.
        {
          (* source execution *)
          eapply Thread.na_tau_step_intro; eauto.
          econs; eauto. eapply State.step_assign; eauto.
        }
        {
          (* match state *)
          exploit val_interp_expr_eval; eauto. introv EVAL_AEXPR_VAL.
          econs; eauto. econs; eauto. econs; eauto.
          rewrite EVAL_AEXPR_VAL.
          eapply val_interp_assign_val; eauto.
          rewrite EVAL_AEXPR_VAL. simpl. eauto.
          simpl in LINK. rewrite EVAL_AEXPR in LINK. eauto.
          clear - ATM_BIT. des; subst; eauto.
        }
      }
      {
        eapply eval_expr_ae_bot in EVAL_AEXPR. des1.
        clear - EVAL_AEXPR AI_INTERP. unfold val_interp in *. des.
        unfold sem_val_reg in *; ss.
        specialize (AI_INTERP r). rewrite EVAL_AEXPR in AI_INTERP. ss.
      }
    + (* load *)
      pose proof (nonatomic_or_atomic or) as NA_AT_LOC.
      destruct NA_AT_LOC as [NA_LOC | AT_LOC].
      {
        subst or.
        destruct (VALSET.get loc amem) eqn:GET_AMEM;
          try solve [inv STATE; tryfalse].
        inv LOCAL.
        assert (GET: exists from released,
                   Memory.get loc (View.pln (TView.cur tview_tgt') loc) mem_tgt' =
                   Some (from, Message.concrete n released) /\
                   lo loc = Ordering.nonatomic).
        {
          clear - GET_AMEM AI_INTERP. unfold val_interp in *. des.
          unfold sem_val_loc in *. ss.
          specialize (AI_INTERP0 loc). rewrite GET_AMEM in AI_INTERP0.
          des; eauto.
        }
        destruct GET as (from & released & GET & NA_LOC').
        exploit read_na_cur_msg_local_stable; eauto. simpl. i. do 2 des1.
        assert (val = n /\ R = released).
        {
          clear - x0 GET. inv x0; ss. inv LC2.
          rewrite GET in GET0. inv GET0. eauto.
        }
        des1; subst.
        eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
        splits.
        {
          (* source execution *)
          eapply Thread.na_plain_read_step_intro; eauto.
          econs; eauto. simpl. eapply State.step_load; eauto.
        }
        {
          (* match state *)
          inv STATE; tryfalse. inv BLK.
          exploit val_interp_read; eauto.
          {
            simpl. unfold eval_loc_ae. introv EVAL_ALOC.
            rewrite GET_AMEM in EVAL_ALOC.
            instantiate (1 := n). inv EVAL_ALOC. eauto.
          }
          {
            instantiate (1 := Ordering.plain). ii; ss.
          }
          instantiate (1 := r). instantiate (1 := released).
          introv VAL_INTERP_READ.
          simpl.
          econs; eauto. econs; eauto. econs; eauto.
          inv x0. simpl in LC2. inv LC2.
          clear - VAL_INTERP_READ. unfold transf_instr in *. eauto.
          clear - ATM_BIT. des; subst; eauto.
        }
      }
      {
        assert (match or with
                | Ordering.plain =>
                    match VALSET.get loc amem with
                    | LVal.VAL v => Inst.assign lhs (Inst.expr_val v)
                    | _ => Inst.load lhs loc or
                    end
                | _ => Inst.load lhs loc or
                end = Inst.load lhs loc or).
        {
          destruct or; ss.
        }
        rewrite H in STATE. inv STATE; tryfalse.
      }
Qed.

Lemma na_read_write_step_case
      inj lo b te
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_cp inj lo b
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (TGT_STEP: Thread.program_step te lo
                                     (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                                     (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt'))
      (NA_READ_WRITE: (exists loc from to v R, te = ThreadEvent.write loc from to v R Ordering.plain) \/
                      (exists loc to v R, te = ThreadEvent.read loc to v R Ordering.plain)):
  exists state_src' tview_src' prm_src' sc_src' mem_src',
    Thread.program_step te lo 
                        (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
                        (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
    match_state_cp inj lo false
                   (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                   (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src').
Proof.
  inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
  assert (mem_tgt = mem_src /\ sc_tgt = sc_src).
  {
    clear - INV. unfold I_cp in *. des; ss.
  }
  des1. subst.
  destruct BB_src.
  - (* jmp: contradiction *)
    simpl in TGT_STEP. inv TGT_STEP. inv STATE; tryfalse.
    destruct te; ss; tryfalse.
    clear - NA_READ_WRITE. des; subst; tryfalse.
    clear - NA_READ_WRITE. des; subst; tryfalse.
  - (* call: contradiction *)
    simpl in TGT_STEP. inv TGT_STEP. inv STATE; tryfalse.
    destruct te; ss; tryfalse.
    clear - NA_READ_WRITE. des; subst; tryfalse.
    clear - NA_READ_WRITE. des; subst; tryfalse.
  - (* be e: contradiction *)
    simpl in TGT_STEP. inv TGT_STEP. inv STATE; tryfalse.
    destruct te; ss; tryfalse.
    clear - NA_READ_WRITE. des; subst; tryfalse.
    clear - NA_READ_WRITE. des; subst; tryfalse.
  - (* ret: contradiction *)
    simpl in TGT_STEP. inv TGT_STEP. inv STATE; tryfalse.
    destruct te; ss; tryfalse.
    clear - NA_READ_WRITE. des; subst; tryfalse.
    clear - NA_READ_WRITE. des; subst; tryfalse.
  - (* instr *)
    destruct c.
    + (* skip: contradiction *)
      simpl in TGT_STEP. inv TGT_STEP. inv STATE; tryfalse.
      destruct te; ss; tryfalse.
      clear - NA_READ_WRITE. des; ss.
      clear - NA_READ_WRITE. des; ss.
    + (* assign: contradiction *)
      simpl in TGT_STEP. inv TGT_STEP.
      assert (EVAL_AEXPR: exists e',
                 match eval_expr_ae rhs (fst ae) with
                 | LVal.VAL v => Inst.assign lhs (Inst.expr_val v)
                 | _ => Inst.assign lhs rhs
                 end = Inst.assign lhs e').
      {
        destruct (eval_expr_ae rhs (fst ae)) eqn:EVAL_AEXPR'; eauto.
      }
      des1. rewrite EVAL_AEXPR in STATE.
      inv STATE; tryfalse.
      destruct te; ss; tryfalse.
      clear - NA_READ_WRITE. des; ss.
      clear - NA_READ_WRITE. des; ss.
    + (* load *)
      simpl in TGT_STEP.
      destruct ae as (aregs & amem).
      pose proof (nonatomic_or_atomic or) as NA_OR_AT_ORD.
      des1. subst; unfold fst, snd in *.
      {
        destruct (VALSET.get loc amem) eqn:GET_AMEM.
        {
          inv TGT_STEP. inv STATE; tryfalse.
          destruct te; simpl in H0; tryfalse. inv H0.
          destruct NA_READ_WRITE as [NA_WRITE | NA_READ].
          des; tryfalse.
          inv BLK. 
          inv LOCAL.
          eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
          splits.

          (* source step *)
          econs; eauto. simpl. eapply State.step_load; eauto.

          (* match state *)
          econs; eauto. econs; eauto. econs; eauto.
          inv LOCAL0. simpl in LC2. inv LC2.
          eapply val_interp_read in AI_INTERP; eauto.
          {
            simpl. clear - AI_INTERP GET_AMEM.
            unfold eval_loc_ae. introv GET_AMEM'.
            rewrite GET_AMEM in GET_AMEM'; tryfalse.
          }
          {
            simpl. clear - GET_AMEM. unfold eval_loc_ae. ii.
            rewrite GET_AMEM in H0. tryfalse.
          }
          {
            ii; tryfalse.
          }

          (* promise *)
          inv LOCAL0. simpl in LC2. inv LC2. eauto.

          (* atom bit *)
          clear - ATM_BIT. des; subst; eauto.

          (* local wf *)
          eapply local_wf_read; eauto.
        }
        {
          inv TGT_STEP; tryfalse. inv STATE; tryfalse.
          destruct te; ss; tryfalse.
          clear - NA_READ_WRITE. des; ss.
          clear - NA_READ_WRITE. des; ss.
        }
        {
          clear - GET_AMEM AI_INTERP.
          unfold val_interp in *; ss. des.
          unfold sem_val_loc in *.
          specialize (AI_INTERP0 loc). rewrite GET_AMEM in AI_INTERP0. tryfalse.
        }
      }
      {
        assert (match or with
                | Ordering.plain =>
                  match VALSET.get loc (snd (aregs, amem)) with
                  | LVal.VAL v => Inst.assign lhs (Inst.expr_val v)
                  | _ => Inst.load lhs loc or
                  end
                | _ => Inst.load lhs loc or
                end = Inst.load lhs loc or).
        {
          clear - NA_OR_AT_ORD. destruct or; ss.
        }
        rewrite H in TGT_STEP. clear H.
        inv TGT_STEP. inv STATE; tryfalse. destruct te; simpl in H0; tryfalse.
        inv H0. inv BLK. clear - NA_READ_WRITE NA_OR_AT_ORD.
        des; ss. inv NA_READ_WRITE; tryfalse.
      }
    + (* store *)
      simpl in TGT_STEP. inv TGT_STEP.
      inv STATE; tryfalse. inv BLK.
      destruct te; simpl in H0; tryfalse. inv H0. inv LOCAL.
      destruct NA_READ_WRITE as [NA_WRITE | NA_READ].

      destruct NA_WRITE as (loc & from0 & to0 & v & R & NA_WRITE). inv NA_WRITE.
      exploit Local_write_id_inj; eauto. i. simpl in x0. des1.
      eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
      splits.
      {
        (* source step *)
        econs; eauto. simpl. eapply State.step_store; eauto.
      }
      {
        (* match state *)
        eapply match_state_cp_intro with (inj' := spec_inj mem_tgt'); eauto. ss.

        (* match state tlocal *)
        econs; eauto. econs; eauto.
        inv LOCAL0. simpl in LC2. inv LC2.
        eapply val_interp_write; eauto.
        eapply val_interp_mem_concrete_incr; eauto.
        ii. eapply write_step_concrete_msg_prsv; eauto.
        clear - LOCAL_WF_TGT WRITABLE. ss. inv WRITABLE.
        inv LOCAL_WF_TGT; ss. inv TVIEW_WF. inv CUR.
        unfold TimeMap.le in PLN_RLX. specialize (PLN_RLX loc).
        auto_solve_time_rel.
        clear - WRITE AI_INTERP. ss. ii.
        exploit val_interp_expr_eval; eauto. introv EVAL_AEXPR. rewrite EVAL_AEXPR in WRITE.
        exploit Memory.write_get2; eauto. i. des. eauto.
        right. split; eauto. clear - LO.
        destruct (lo loc) eqn:LOC_TYPE; ss. des; tryfalse.
        introv GET_PRM. clear - GET_PRM x1 PRM_INDOM.
        eapply x1 in GET_PRM. des. eauto.

        (* atomic bit *)
        clear - ATM_BIT x0 INV. unfold I_cp in *. des; subst; ss.
        left. split; eauto.
        left. split; eauto.

        (* local wf *)
        eapply local_wf_write; eauto.

        (* closed sc timemap *)
        inv LOCAL0. simpl in LC2. inv LC2. ss. 
        eapply concrete_incr_closed_tm_prsv with (mem := mem_src); eauto.
        ii.
        eapply write_step_concrete_msg_prsv with (loc := loc); eauto.
        econs; eauto.
        instantiate (3 := Local.mk tview_src prm_src). ss; eauto.
        simpl. eauto. eauto.
        
        (* memory closed *)
        eapply write_step_closed_mem; eauto.
      }

      clear - NA_READ. des; ss.
    + (* print: contradiction *)
      simpl in TGT_STEP. inv TGT_STEP. inv STATE; tryfalse.
      destruct te; ss; tryfalse.
      clear - NA_READ_WRITE. des; ss.
    + (* cas: contradiction *)
      simpl in TGT_STEP. inv TGT_STEP. inv STATE; tryfalse.
      destruct te; ss; tryfalse.
      clear - NA_READ_WRITE. des; ss.
      destruct te; ss; tryfalse.
      inv BLK. inv H0. clear - NA_READ_WRITE ATOMIC. des; ss.
      destruct ord; ss.
    + (* fence rel: contradiction *)
      simpl in TGT_STEP. inv TGT_STEP. inv STATE; tryfalse.
      destruct te; ss; tryfalse.
      clear - NA_READ_WRITE. des; ss.
    + (* fence acq: contradiction *)
      simpl in TGT_STEP. inv TGT_STEP. inv STATE; tryfalse.
      destruct te; ss; tryfalse.
      clear - NA_READ_WRITE. des; ss.
    + (* fence sc: contradiction *)
      simpl in TGT_STEP. inv TGT_STEP. inv STATE; tryfalse.
      destruct te; ss; tryfalse.
      clear - NA_READ_WRITE. des; ss.
Qed.

Lemma promise_step_case
      inj lo te
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_cp inj lo true
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (TGT_STEP: Thread.step lo false te 
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')):
  exists state_src' tview_src' prm_src' sc_src' mem_src' inj',
    rtc (Thread.prc_step lo) 
        (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
        (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
    incr_inj inj inj' /\ 
    match_state_cp inj' lo true
                   (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                   (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src').
Proof.
  inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
  assert (mem_tgt = mem_src /\ sc_tgt = sc_src /\ inj' = spec_inj mem_tgt).
  {
    clear - INV. unfold I_cp in *. des; ss.
  }
  do 2 des1. subst.
  inv TGT_STEP. inv STEP.
  lets LOCAL': LOCAL. eapply Local_promise_id_inj in LOCAL'. des1.
  eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'. exists (spec_inj mem_tgt').
  splits.
  {
    (* source step *)
    eapply Operators_Properties.clos_rt1n_step.
    econs; eauto. econs; eauto.
  }
  {
    (* incr inj *)
    clear - LOCAL' ATM_BIT. eapply incr_inj_transitivity; eauto.
    des; subst; eauto. ii; eauto.
  }
  {
    (* match state *)
    econs; eauto. ss.

    (* match state tlocal *)
    econs; eauto. econs; eauto. inv LOCAL. simpl in LC2. inv LC2.
    simpl in PROMISE.
    eapply val_interp_mem_concrete_incr; eauto.
    ii. eapply Memory_promise_memory_get in PROMISE; eauto.
    do 3 des1. eauto.
    inv LOCAL. simpl in LC2. inv LC2.
    simpl in PROMISE. eapply local_wf_promise in PROMISE; eauto.
    clear - PROMISE. inv PROMISE; ss. ii.
    eapply PROMISES in H. unfold spec_inj. rewrite H; eauto.

    (* local wf *)
    inv LOCAL. simpl in LC2. inv LC2.
    eapply local_wf_promise; eauto.

    (* memory sc timemap *)
    inv LOCAL. simpl in LC2. inv LC2.
    eapply Memory.promise_closed_timemap; eauto.

    (* closed memory *)
    eapply promise_step_closed_mem; eauto.
  }
Qed.

Lemma pf_promise_step_case
      inj lo b te
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_cp inj lo b
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (TGT_STEP: Thread.step lo true te 
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt'))
      (PRM_STEP: (exists loc t, ThreadEvent.is_promising te = Some (loc, t))):
  exists state_src' tview_src' prm_src' sc_src' mem_src',
    rtc (@Thread.pf_promise_step rtl_lang) 
        (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
        (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
    match_state_cp inj lo b
                   (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                   (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src').
Proof.
  inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
  assert (mem_tgt = mem_src /\ sc_tgt = sc_src /\ inj' = spec_inj mem_tgt).
  {
    clear - INV. unfold I_cp in *. des; ss.
  }
  do 2 des1. do 2 des1. subst.
  inv TGT_STEP; tryfalse.
  2: { clear - PRM_STEP STEP. inv STEP; ss. inv LOCAL; ss. }
  inv STEP.   
  destruct kind; simpl in PF; tryfalse.
  {
    (* lower to none *)
    destruct msg1; ss. destruct msg; ss. destruct released0; ss.
    eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
    lets LOCAL': LOCAL.
    eapply Local_promise_id_inj in LOCAL'. do 2 des1.
    clear LOCAL' LOCAL'1. exploit LOCAL'0; eauto.
    clear LOCAL'0. introv EQ_INJ.
    splits.
    {
      (* source step *)
      eapply Operators_Properties.clos_rt1n_step.
      econs; eauto. econs; eauto.
    }
    {
      (* match state *)
      econs; eauto. ss.

      (* match state tlocal *)
      econs; eauto. econs; eauto. inv LOCAL. simpl in LC2. inv LC2.
      simpl in PROMISE.
      eapply val_interp_mem_concrete_incr; eauto.
      ii. eapply Memory_promise_memory_get in PROMISE; eauto.
      do 3 des1. eauto.
      clear - PRM_INDOM LOCAL. inv LOCAL; ss. inv LC2.
      inv PROMISE; ss. des; subst. inv RESERVE.
      ii. erewrite Memory.lower_o in H; eauto. des_ifH H; ss.
      des1. subst. inv H.
      exploit Memory.lower_get0; [eapply PROMISES | eauto..]. i. do 2 des1. eauto.
      eauto.

      (* local wf *)
      inv LOCAL. simpl in LC2. inv LC2.
      eapply local_wf_promise; eauto.

      (* memory sc timemap *)
      inv LOCAL. simpl in LC2. inv LC2.
      eapply Memory.promise_closed_timemap; eauto.

      (* closed memory *)
      eapply promise_step_closed_mem; eauto.
    }
  }
  {
    (* cancel *)
    assert (msg = Message.reserve).
    {
      clear - LOCAL. inv LOCAL; ss. inv PROMISE; ss.
    }
    subst msg.
    eexists. exists tview_tgt' prm_tgt' sc_tgt' mem_tgt'.
    lets LOCAL': LOCAL.
    eapply Local_promise_id_inj in LOCAL'. do 2 des1.
    clear LOCAL' LOCAL'0. exploit LOCAL'1; eauto.
    clear LOCAL'1. introv EQ_INJ.
    splits.
    {
      (* source step *)
      eapply Operators_Properties.clos_rt1n_step.
      econs; eauto. econs; eauto.
    }
    {
      (* match state *)
      econs; eauto. ss.

      (* match state tlocal *)
      econs; eauto. econs; eauto. inv LOCAL. simpl in LC2. inv LC2.
      simpl in PROMISE.
      eapply val_interp_mem_concrete_incr; eauto.
      ii. eapply Memory_promise_memory_get in PROMISE; eauto.
      do 3 des1. eauto.
      clear - PRM_INDOM LOCAL. inv LOCAL; ss. inv LC2.
      inv PROMISE; ss. des; subst. inv RESERVE.
      ii. erewrite Memory.remove_o in H; eauto. des_ifH H; ss.
      eauto.
    
      (* local wf *)
      inv LOCAL. simpl in LC2. inv LC2.
      eapply local_wf_promise; eauto.

      (* memory sc timemap *)
      inv LOCAL. simpl in LC2. inv LC2.
      eapply Memory.promise_closed_timemap; eauto.

      (* closed memory *)
      eapply promise_step_closed_mem; eauto.
    }
  }
Qed.

Lemma rely_step_case
      inj inj' lo
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src
      sc_src' mem_src'
      (MATCH: match_state_cp inj lo true
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (RELY: Rely inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)
                  inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src')
                  prm_tgt prm_src lo)
      (INV: I_cp lo inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src')):
  match_state_cp inj' lo true
                 (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt' mem_tgt')
                 (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src' mem_src').
Proof.
  inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
  assert (mem_tgt = mem_src /\ sc_tgt = sc_src /\ inj'0 = spec_inj mem_tgt).
  {
    clear - INV0. unfold I_cp in *. des; ss.
  } 
  do 2 des1. subst.
  assert (mem_tgt' = mem_src' /\ sc_tgt' = sc_src' /\ inj' = spec_inj mem_tgt').
  {
    clear - INV. unfold I_cp in *. des; ss.
  }
  do 2 des1. subst.

  inv RELY; ss. inv ENV_STEPS; ss.

  econs; eauto. econs; eauto. econs; eauto.
  eapply val_interp_mem_concrete_incr; eauto.
  ii. unfold concrete_mem_incr in *.
  eapply MEM_SRC_INCR in H; eauto. des; eauto.

  eapply concrete_incr_local_wf_prsv with (mem' := mem_src') in LOCAL_WF_TGT; eauto.
  clear - LOCAL_WF_TGT. ii. inv LOCAL_WF_TGT; ss.
  eapply PROMISES in H. unfold spec_inj. rewrite H. eauto.
  ii. unfold concrete_mem_incr in *.
  eapply MEM_SRC_INCR in H; eauto. des; eauto.

  eapply concrete_incr_local_wf_prsv with (mem := mem_src); eauto.
  ii. unfold concrete_mem_incr in *.
  eapply MEM_SRC_INCR in H; eauto. des; eauto.
Qed.

Lemma done_step_case
      inj lo b
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_src tview_src prm_src sc_src mem_src
      (MATCH: match_state_cp inj lo b
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (DONE: Thread.is_done (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)):
  exists inj',
      Thread.is_done (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src) /\
      incr_inj inj inj' /\
      I_cp lo inj' (Build_Rss sc_tgt mem_tgt sc_src mem_src).
Proof.
  inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME. 
  unfold Thread.is_done in DONE. ss. des1. subst.
  unfold State.is_terminal in TERMINAL. ss. des1; subst.
  destruct BB_src; ss; try solve [tryfalse].
  assert (mem_tgt = mem_src /\ sc_tgt = sc_src /\ inj' = spec_inj mem_tgt).
  {
    clear - INV. unfold I_cp in *. des; ss.
  } 
  do 2 des1. subst.
  exists (spec_inj mem_src). splits; eauto.
  {
    unfold Thread.is_done. ss. split; eauto.
    unfold State.is_terminal; eauto. ss.
    inv STK_FRAMES; ss.
  }
  {
    clear - ATM_BIT. des; subst; eauto.
    ii; eauto.
  }
Qed.

Lemma abort_step_case
      inj lo b
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_src tview_src prm_src sc_src mem_src
      (MATCH: match_state_cp inj lo b
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (ABORT: Thread.is_abort (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt) lo):
  Thread.is_abort (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src) lo.
Proof.
  inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
  assert (mem_tgt = mem_src /\ sc_tgt = sc_src /\ inj' = spec_inj mem_tgt).
  {
    clear - INV. unfold I_cp in *. des; ss.
  } 
  do 2 des1. subst.
  unfold Thread.is_abort in ABORT. simpl in ABORT.
  des1.
  unfold Thread.is_abort. simpl. split; eauto.
  destruct ABORT0 as [NO_CONT_ABORT | MEM_ORD_ABORT].
  {
    left. introv CONT_S. contradiction NO_CONT_ABORT. clear NO_CONT_ABORT.
    des1.
    {
      do 2 des1. left.
      destruct BB_src; simpl.
      - (* jmp *)
        inv CONT_S; tryfalse. inv BLK.
        exploit transform_cdhp_prop; eauto. instantiate (1 := afunc).
        i. des1.
        do 2 eexists. eapply State.step_jmp; eauto.
      - (* call *)
        inv CONT_S; tryfalse. inv BLK.
        renames ch0 to C_src0, b2 to BB_src0, b' to BB_src'.
        exploit transform_cdhp_prop; eauto. instantiate (1 := afunc).
        i. des1.
        exploit transform_prog_proper; eauto. i. do 2 des1.
        destruct func_t as (C_tgt0 & f1').
        unfold transform_func in x2.
        destruct (ValDS.analyze_func (C_src0, f1) succ ValLat.top transf_blk); ss.
        inv x2. 
        exploit transform_cdhp_prop; [eapply ENTRY_BLK | eauto..]. instantiate (1 := a).
        i. destruct x2 as (BB_tgt0 & x2).
        do 2 eexists.
        eapply State.step_call; eauto.
      - (* be *)
        inv CONT_S; tryfalse. inv BLK. des1.
        {
          des1.
          exploit transform_cdhp_prop; eauto. instantiate (1 := afunc).
          i. des1.
          do 2 eexists. eapply State.step_be; eauto.
        }
        {
          des1.
          exploit transform_cdhp_prop; eauto. instantiate (1 := afunc).
          i. des1.
          do 2 eexists. eapply State.step_be; eauto.
        }
      - (* ret *)
        inv CONT_S; tryfalse. inv STK_FRAMES.
        do 2 eexists. eapply State.step_ret; eauto.
      - (* instr *)
        destruct c; simpl in CONT_S; simpl.
        + (* skip *)
          do 2 eexists. eapply State.step_skip; eauto.
        + (* assign *)
          assert (exists e, match eval_expr_ae rhs (fst ae) with
                       | LVal.VAL v => Inst.assign lhs (Inst.expr_val v)
                       | _ => Inst.assign lhs rhs
                       end = Inst.assign lhs e).
          {
            destruct (eval_expr_ae rhs (fst ae)) eqn:Heqe; eauto.
          }
          des1. rewrite H. clear H.
          do 2 eexists. eapply State.step_assign; eauto.
        + (* load *)
          pose proof (nonatomic_or_atomic or) as NA_OR_AT_ORD.
          des1. subst.
          destruct (VALSET.get loc (snd ae)) eqn:GET_ALOC.
          do 2 eexists. eapply State.step_load; eauto.
          do 2 eexists. eapply State.step_assign; eauto.
          do 2 eexists. eapply State.step_load; eauto.
          assert (match or with
                  | Ordering.plain =>
                    match VALSET.get loc (snd ae) with
                    | LVal.VAL v => Inst.assign lhs (Inst.expr_val v)
                    | _ => Inst.load lhs loc or
                    end
                  | _ => Inst.load lhs loc or
                  end = Inst.load lhs loc or).
          {
            destruct or; ss.
          }
          rewrite H. clear H.
          do 2 eexists. eapply State.step_load; eauto.
        + (* store *)
          do 2 eexists. eapply State.step_store; eauto.
        + (* print *)
          do 2 eexists. eapply State.step_out; eauto.
        + (* cas *)
          inv CONT_S; tryfalse. inv BLK.
          do 2 eexists. eapply State.step_cas_same; eauto.
          inv BLK.
          do 2 eexists. eapply State.step_cas_flip; eauto.
        + (* fence rel *)
          do 2 eexists. eapply State.step_fence_rel; eauto.
        + (* fence acq *)
          do 2 eexists. eapply State.step_fence_acq; eauto.
        + (* fence sc *)
          do 2 eexists. eapply State.step_fence_sc; eauto.
    }
    {
      unfold State.is_terminal in *; ss.
      des1; subst. simpl. inv STK_FRAMES.
      right; eauto.
    }
  }
  destruct MEM_ORD_ABORT as [MEM_ORD_ABORT1 | MEM_ORD_ABORT2].
  {
    do 5 des1.
    destruct MEM_ORD_ABORT1 as [MEM_ORD_ABORT_READ | MEM_ORD_ABORT_WRITE].
    {
      right. left.
      destruct BB_src; simpl in MEM_ORD_ABORT_READ; inv MEM_ORD_ABORT_READ; tryfalse.
      destruct c; simpl in BLK; tryfalse.
      
      destruct (eval_expr_ae rhs (fst ae)) eqn:EVAL_AEXPR; tryfalse.
      pose proof (nonatomic_or_atomic or) as NA_AT_ORD.
      des1; subst.
      destruct (VALSET.get loc (snd ae)) eqn:GET_AMEM; ss.
      inv BLK.
      do 4 eexists. split; eauto. left. eapply State.step_load; eauto.
      inv BLK.
      do 4 eexists. split; eauto. left. eapply State.step_load; eauto.
      assert (match or with
              | Ordering.plain =>
                match VALSET.get loc (snd ae) with
                | LVal.VAL v => Inst.assign lhs (Inst.expr_val v)
                | _ => Inst.load lhs loc or
                end
              | _ => Inst.load lhs loc or
              end = Inst.load lhs loc or).
      {
        destruct or; ss; eauto.
      }
      rewrite H in BLK; clear H. inv BLK.
      do 4 eexists. split; eauto. left. eapply State.step_load; eauto.

      destruct c; simpl in BLK; tryfalse.
      destruct (eval_expr_ae rhs (fst ae)) eqn:EVAL_AEXPR; tryfalse.
      pose proof (nonatomic_or_atomic or) as NA_AT_ORD.
      des1; subst.
      destruct (VALSET.get loc (snd ae)) eqn:GET_AMEM; ss.
      assert (match or with
              | Ordering.plain =>
                match VALSET.get loc (snd ae) with
                | LVal.VAL v => Inst.assign lhs (Inst.expr_val v)
                | _ => Inst.load lhs loc or
                end
              | _ => Inst.load lhs loc or
              end = Inst.load lhs loc or).
      {
        destruct or; ss; eauto.
      }
      rewrite H in BLK. inv BLK.
      inv BLK. do 4 eexists. split; eauto.
      left. eapply State.step_cas_flip; eauto.
    }
    {
      right. left.
      destruct BB_src; simpl in MEM_ORD_ABORT_WRITE; inv MEM_ORD_ABORT_WRITE; tryfalse.
      destruct c; simpl in BLK; tryfalse.
      destruct (eval_expr_ae rhs (fst ae)) eqn:EVAL_AEXPR; tryfalse.
      pose proof (nonatomic_or_atomic or) as NA_AT_ORD.
      des1; subst.
      destruct (VALSET.get loc (snd ae)) eqn:GET_AMEM; ss.
      assert (match or with
              | Ordering.plain =>
                match VALSET.get loc (snd ae) with
                | LVal.VAL v => Inst.assign lhs (Inst.expr_val v)
                | _ => Inst.load lhs loc or
                end
              | _ => Inst.load lhs loc or
              end = Inst.load lhs loc or).
      {
        destruct or; ss; eauto.
      }
      rewrite H in BLK. ss.
      inv BLK. do 4 eexists. split; eauto. right. eapply State.step_store; eauto.
    }
  }
  {
    do 7 des1.
    right. right.
    destruct BB_src; simpl in MEM_ORD_ABORT2; inv MEM_ORD_ABORT2; tryfalse.
    destruct c; simpl in BLK; tryfalse.
    destruct (eval_expr_ae rhs (fst ae)) eqn:EVAL_AEXPR; tryfalse.
    assert (match or0 with
            | Ordering.plain =>
              match VALSET.get loc (snd ae) with
              | LVal.VAL v => Inst.assign lhs (Inst.expr_val v)
              | _ => Inst.load lhs loc or0
              end
            | _ => Inst.load lhs loc or0
            end = Inst.load lhs loc or0).
    {
      destruct or0; ss; eauto.
      destruct (VALSET.get loc (snd ae)) eqn:GET_AMEM; ss.
    }
    rewrite H in BLK. ss.
    inv BLK.
    do 6 eexists. split; eauto.
    eapply State.step_cas_same; eauto.
  }
  Unshelve.
  exact Int.zero. exact Int.zero. exact Int.zero.
  exact Int.zero. exact Int.zero. exact Int.zero.
Qed.
