Require Import RelationClasses.          
Require Import List. 

Require Import sflib.
From Paco Require Import paco. 

Require Import Basic.
Require Import Axioms.
Require Import Loc.
Require Import Coqlib.
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

Require Import CompAuxDef.
Require Import MemoryProps.
Require Import promiseCertifiedAux.
Require Import ConsistentProp.
Require Import Mem_at_eq_lemmas.

Require Import ValAnalysis.
Require Import ConstProp.
Require Import ConstPropProofMState.
Require Import Lib_Step.
Require Import ConstPropProofStep.
  
(** * Correctness proof of Constant Propagation *)
(** ** Well-formed invariant *)
(** The invariant [I_cp] for ConstProp proof is well-formed. *)
Lemma WF_I_cp: wf_I I_cp.
Proof.
  unfold wf_I. ii.
  destruct S; ss. unfold I_cp in *; ss. des.
  econs; eauto; subst.
  - ii. unfold spec_inj. rewrite MSG. do 3 eexists. splits; eauto.
  - ii. unfold spec_inj in *. destruct (Memory.get loc t (S_MEM)) eqn:Heqe; ss.
    destruct p, t0; ss; tryfalse; eauto;
      try solve [destruct t1; ss; eauto].
  - unfold spec_inj; ii.
    destruct (Memory.get loc t1 S_MEM) eqn:Heqe1; ss. destruct p, t0; ss. inv INJ1.
    destruct (Memory.get loc t2 S_MEM) eqn:Heqe2; ss. destruct p, t1; ss. inv INJ2.
    eauto.
Qed.

Lemma I_cp_hold_init
      lo:
  I_cp lo inj_init (Build_Rss TimeMap.bot Memory.init TimeMap.bot Memory.init).
Proof.
  econs; eauto. ss.
  eapply functional_extensionality. ii.
  eapply functional_extensionality. ii.
  unfold inj_init, spec_inj.
  des_if; subst. unfold Memory.init. ss.
  unfold Memory.init; ss. unfold Memory.get.
  rewrite Cell.init_get. des_if; eauto.
  ss.
Qed.

Lemma match_state_implies_SI
      inj lo b
      state_tgt lc_tgt sc_tgt mem_tgt
      state_src lc_src sc_src mem_src
      (MATCH_STATE: match_state_cp inj lo b
                                   (Thread.mk rtl_lang state_tgt lc_tgt sc_tgt mem_tgt)
                                   (Thread.mk rtl_lang state_src lc_src sc_src mem_src)):
  SI inj lo (state_tgt, lc_tgt, mem_tgt) (state_src, lc_src, mem_src) (@dset_init nat).
Proof.
  inv MATCH_STATE; ss. unfold I_cp in INV. simpl in INV.
  assert (INCR_INJ: incr_inj inj inj').
  {
    des; subst. unfold incr_inj; ii; eauto.
    unfold incr_inj; ii; eauto.
  }
  clear ATM_BIT. des. subst.
  econs; eauto; ss.
  inv MATCH_THRD_LOCAL; eauto. ii; eauto.
  eapply INCR_INJ in H. unfold spec_inj in H.
  destruct (Memory.get loc t mem_src) eqn:GET; ss.
  destruct p. destruct t1; ss. inv H. eauto.
  exists (@dset_init nat). split.
  ii. rewrite dset_gempty in H; ss.
  inv MATCH_THRD_LOCAL; ss.
  econs; eauto.
  ii. rewrite dset_gempty in H; ss.
  ii. exploit PRM_INDOM; eauto. ii; des1.
  exists to' f val R. split; eauto.
  eapply INCR_INJ in H0. unfold spec_inj in H0.
  inv LOCAL_WF_TGT; ss. lets GET_PRM: H.
  eapply PROMISES in H. rewrite H in H0; ss.
  inv H0. eauto.
  ii. exploit PRM_INDOM; eauto. ii; des.
  assert (t' = to').
  {
    eapply INCR_INJ in H0.
    exploit spec_inj_identity_inj; eauto.
  }
  subst.
  exists to'. splits; eauto.
Qed.

Lemma match_state_cp_implies_sim:
  forall inj lo b
    state_tgt lc_tgt sc_tgt mem_tgt
    state_src lc_src sc_src mem_src
    (MATCH_STATE: match_state_cp inj lo b
                                  (Thread.mk rtl_lang state_tgt lc_tgt sc_tgt mem_tgt)
                                  (Thread.mk rtl_lang state_src lc_src sc_src mem_src)),
    @local_sim_state nat lt rtl_lang I_cp lo inj dset_init b
                     (Thread.mk rtl_lang state_tgt lc_tgt sc_tgt mem_tgt)
                     (Thread.mk rtl_lang state_src lc_src sc_src mem_src).
Proof.
  cofix COFIX_HP.
  introv MATCH_STATE. 
  destruct (classic (Local.promise_consistent lc_tgt)) as [PROMS_CONS | NOT_PROM_CONS].
  2: {
    eapply local_sim_state_tgt_not_prm_consistent_intro; eauto.
  } 
  destruct (classic (Thread.is_abort (Thread.mk rtl_lang state_src lc_src sc_src mem_src) lo)).
  eapply local_sim_state_abort_intro; eauto.

  eapply local_sim_state_step_intro.
  - eapply match_state_implies_SI; eauto.
  - introv THRD_STEP. splits.
    {
      (* atomic or out step *)
      introv THRD_AT_OR_OUT.
      destruct lc_tgt as (tview_tgt & prm_tgt).
      destruct lc_src as (tview_src & prm_src).
      destruct e_tgt'.
      renames state to state_tgt', local to lc_tgt', sc to sc_tgt', memory to mem_tgt'.
      destruct lc_tgt' as (tview_tgt' & prm_tgt').
      eapply atomic_or_out_step_case in THRD_STEP; eauto. des.
      do 4 eexists.
      split. eauto. split. eauto.
      split. eauto. split. eapply COFIX_HP; eauto.
      destruct te; ss. splits; eauto.
    }
    {
      (* non-atomic step *)
      introv NA_STEP. destruct te; ss.
      + (* silent *)
        inv THRD_STEP; ss. inv STEP.
        destruct lc_tgt as (tview_tgt & prm_tgt).
        destruct lc_src as (tview_src & prm_src).
        destruct e_tgt'.
        renames state to state_tgt', local to lc_tgt', sc to sc_tgt', memory to mem_tgt'.
        destruct lc_tgt' as (tview_tgt' & prm_tgt'). 
        eapply silent_step_case in STEP; eauto. des; tryfalse.
        eexists. exists (@dset_init nat) (@dset_init nat) (@dset_init nat).
        splits.
        {
          eapply dset_become_na_read. ii; ss. eauto.
        }
        {
          eapply Operators_Properties.clos_rt1n_step.
          eapply Thread_na_step_to_na_step_dset; eauto.
        }
        {
          econs. introv DSET_GET. rewrite dset_gempty in DSET_GET. tryfalse.
          introv DSET_GET. rewrite dset_gempty in DSET_GET. tryfalse.
        }
        {
          eapply COFIX_HP; eauto.
        }
      + (* non-atomic read *)
        destruct ord; tryfalse.
        inv THRD_STEP; ss. inv STEP.
        destruct lc_tgt as (tview_tgt & prm_tgt).
        destruct lc_src as (tview_src & prm_src).
        destruct e_tgt'.
        renames state to state_tgt', local to lc_tgt', sc to sc_tgt', memory to mem_tgt'.
        destruct lc_tgt' as (tview_tgt' & prm_tgt').
        eapply na_read_write_step_case in STEP; eauto.
        des.
        eexists. exists (@dset_init nat) (@dset_init nat) (@dset_init nat).
        splits.
        {
          eapply dset_become_na_read. ii; ss. eauto.
        }
        {
          eapply Operators_Properties.clos_rt1n_step.
          eapply Thread_na_step_to_na_step_dset; eauto. 
          eapply Thread.na_plain_read_step_intro; eauto.
        }
        {
          econs. introv DSET_GET. rewrite dset_gempty in DSET_GET. tryfalse.
          introv DSET_GET. rewrite dset_gempty in DSET_GET. tryfalse.
        }
        {
          eapply COFIX_HP; eauto.
        }
        {
          right. eauto.
        }
      + (* non-atomic write *)
        destruct ord; tryfalse.
        inv THRD_STEP; ss. inv STEP.
        destruct lc_tgt as (tview_tgt & prm_tgt).
        destruct lc_src as (tview_src & prm_src).
        destruct e_tgt'.
        renames state to state_tgt', local to lc_tgt', sc to sc_tgt', memory to mem_tgt'.
        destruct lc_tgt' as (tview_tgt' & prm_tgt').
        eapply na_read_write_step_case in STEP; eauto.
        2: { left. exists loc from to val released. eauto. }
        des.
        do 2 eexists. exists (@dset_init nat) (@dset_init nat).
        splits.
        {
          econs; eauto.
        }
        {
          instantiate (2 := 5%nat).
          eapply Operators_Properties.clos_rt1n_step.
          eapply na_steps_dset_write. eapply STEP.
          right. exists to. rewrite dset_remove_add; eauto.
        }
        {
          econs. introv DSET_GET. rewrite dset_gempty in DSET_GET. tryfalse.
          introv DSET_GET. rewrite dset_gempty in DSET_GET. tryfalse.
        }
        {
          eapply COFIX_HP; eauto.
        }
    }
    {
      (* promise step *)
      introv PROM_STEP. ii; subst.
      destruct lc_tgt as (tview_tgt & prm_tgt).
      destruct lc_src as (tview_src & prm_src).
      destruct e_tgt'.
      renames state to state_tgt', local to lc_tgt', sc to sc_tgt', memory to mem_tgt'.
      destruct lc_tgt' as (tview_tgt' & prm_tgt').
      eapply promise_step_case in THRD_STEP; eauto. clear PROM_STEP.
      des.
      do 2 eexists. split. eauto. split. eauto.
      eapply COFIX_HP. eauto.
    }
    {
      (* pf promise step *)
      introv PF_PROM_STEP. ii; subst.
      destruct lc_tgt as (tview_tgt & prm_tgt).
      destruct lc_src as (tview_src & prm_src).
      destruct e_tgt'.
      renames state to state_tgt', local to lc_tgt', sc to sc_tgt', memory to mem_tgt'.
      destruct lc_tgt' as (tview_tgt' & prm_tgt').
      eapply pf_promise_step_case in THRD_STEP; eauto.
      des.
      eexists. split; eauto.
    }
  - ii; subst.
    split.
    {
      clear - MATCH_STATE. inv MATCH_STATE. destruct ATM_BIT.
      destruct H; tryfalse. destruct H; subst. eauto.
    }
    {
      introv RELY INV.
      destruct lc_tgt as (tview_tgt & prm_tgt).
      destruct lc_src as (tview_src & prm_src).
      eapply rely_step_case in RELY; eauto.
    }
  - introv THRD_DONE.
    destruct lc_tgt as (tview_tgt & prm_tgt).
    destruct lc_src as (tview_src & prm_src).
    lets MATCH_STATE': MATCH_STATE.
    eapply done_step_case in MATCH_STATE; eauto. des.
    eexists. exists inj'.
    splits; eauto.
  - introv THRD_ABORT.
    destruct lc_tgt as (tview_tgt & prm_tgt).
    destruct lc_src as (tview_src & prm_src).
    lets MATCH_STATE': MATCH_STATE.
    eapply abort_step_case in MATCH_STATE; eauto.
Qed.

(** ** Correctness of the Constant propagation *)
(** Constant propagation is verified. *)
Theorem verif_constprop:
  forall code_s code_t lo,
      constprop_optimizer lo code_s = Some code_t 
      ->
      @local_sim nat lt rtl_lang I_cp lo code_t code_s.
Proof.
  ii. econs.
  - (* well_founded index *)
    eapply nat_lt_is_well_founded.
  - (* well-formed I_dce *)
    eapply WF_I_cp; eauto.
  - (* I_cp holds in initial state *)
    eapply I_cp_hold_init; eauto.
  - (* local simulation *)
    introv TGT_INIT.
    unfold Language.init in *; ss.
    unfold State.init in *; ss.
    destruct (code_t ! fid) eqn:FUNC_T; ss. destruct f; ss.
    renames c to c_t.
    destruct (c_t ! f) eqn:ENTRY_BB_T; ss. inv TGT_INIT; ss.
    destruct (code_s ! fid) eqn:FUNC_S; ss.
    exploit transform_prog_proper; eauto. ii; des.
    rewrite FUNC_T in H0. inv H0. destruct f0 as (c_s & f_s).
    exploit transform_func_init; eauto.
    ii; des; subst. rewrite H0.
    eexists. split. eauto.
    eapply match_state_cp_implies_sim; eauto.
    econs; eauto.
    eapply I_cp_hold_init; eauto.

    econs; eauto.
    {
      exploit transf_cdhp_prop; eauto. i. do 5 des1. subst.
      rewrite H0 in H3. inv H3.
      econs; eauto.
      eapply ValDS.analyze_func_entry1 in H2; eauto.
      clear - H2. unfold ValDS.AI.ge in *; ss.
      eapply val_ge_top; eauto.
      ii. rewrite transf_blk_first; eauto.
    }
    {
      econs; eauto.
    }

    introv GET_PRM. rewrite Memory.bot_get in GET_PRM. ss.
    eapply Local.wf_init; eauto.
    eapply Memory.closed_timemap_bot; eauto.
    eapply Memory.init_closed; eauto.

    unfold constprop_optimizer in *. 
    exploit transform_prog_proper_none; eauto.
    introv contr. rewrite FUNC_T in contr. ss.
Qed.

(** Constant propagation optimizer is correct. *)
Theorem correct_constprop:
  Correct constprop_optimizer.
Proof.
  eapply Verif_implies_Correctness.
  unfolds Verif. intros. exists I_cp nat lt. 
  eapply verif_constprop; eauto.
Qed.
