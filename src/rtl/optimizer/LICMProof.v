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
Require Import WFConfig.
Require Import MsgMapping.
Require Import DelaySet.
Require Import LocalSim.
Require Import MemoryMerge.

Require Import CompAuxDef.
Require Import MemoryProps.
Require Import promiseCertifiedAux.
Require Import ConsistentProp.
Require Import Mem_at_eq_lemmas.
Require Import ConsistentStableEnv.
Require Import ConsistentLemmas.

Require Import DetLoop.
Require Import LICM.
Require Import Lib_Step.
Require Import LICMProofMState.
Require Import LICMProofStep.
Require Import CSEProof.
  
(** * Correctness Proof of Loop Invariant Code Motion *)
(** ** Well-Formed Invariant *)
(** The invariant [I_linv] is well-formed. *)
Lemma WF_I_linv: wf_I I_linv.
Proof.
  unfold wf_I. ii.
  destruct S; ss. des.
  econs; eauto; subst.
  - ii. unfold spec_inj. rewrite MSG.
    inv MEM_LE. exploit COMPLETE; eauto. i. des1.
    do 3 eexists. splits; eauto.
  - ii. unfold spec_inj in *. destruct (Memory.get loc t T_MEM) eqn:Heqe; ss.
    destruct p. destruct t1; ss. inv INJ.
    inv MEM_LE. exploit COMPLETE; eauto.
  - unfold spec_inj; ii.
    destruct (Memory.get loc t1 T_MEM) eqn:Heqe1; ss. destruct p. destruct t0; ss. inv INJ1.
    destruct (Memory.get loc t2 T_MEM) eqn:Heqe2; ss. destruct p. destruct t1; ss. inv INJ2.
    eauto.
Qed.

Lemma I_linv_hold_init
      lo:
  I_linv lo inj_init (Build_Rss TimeMap.bot Memory.init TimeMap.bot Memory.init).
Proof.
  econs; eauto. eapply mem_id_le_identity; eauto.
  split. eapply View.TimeMap.le_PreOrder_obligation_1; eauto.
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
      (MATCH_STATE: match_state_linv inj lo b
                                     (Thread.mk rtl_lang state_tgt lc_tgt sc_tgt mem_tgt)
                                     (Thread.mk rtl_lang state_src lc_src sc_src mem_src)):
  SI inj lo (state_tgt, lc_tgt, mem_tgt) (state_src, lc_src, mem_src) (@dset_init nat).
Proof.
  inv MATCH_STATE; ss. do 2 des1.
  assert (INCR_INJ: incr_inj inj inj').
  {
    des; subst. unfold incr_inj; ii; eauto.
    unfold incr_inj; ii; eauto.
  }
  clear ATM_BIT.
  econs; eauto; ss.
  - ii. unfold incr_inj in INCR_INJ. exploit INCR_INJ; eauto.
    ii. subst. unfold spec_inj in H1.
    destruct (Memory.get loc t mem_tgt) eqn:GET_MEM; ss.
    destruct p. destruct t1; ss. inv H1.
    clear - TVIEW_LE H0. inv TVIEW_LE.
    inv CUR. unfold TimeMap.le in RLX.
    specialize (RLX loc).
    auto_solve_time_rel.
  - exists (@dset_init nat). split.
    ii. rewrite dset_gempty in H; ss.
    econs; eauto.
    ii. rewrite dset_gempty in H; ss.
    ii. exploit PRM_INDOM; eauto. ii; des1.
    exploit INCR_INJ; eauto. ii; subst.
    unfold spec_inj in H1.
    destruct (Memory.get loc t mem_tgt) eqn:GET; ss.
    destruct p. destruct t1; ss. inv H1.
    exists to' f val R. split; eauto.
    ii. exploit PRM_INDOM; eauto. ii; des.
    assert (t' = to').
    {
      eapply INCR_INJ in H0. subst.
      exploit spec_inj_identity_inj; eauto.
    }
    subst.
    exists to'. splits; eauto.
  - subst.
    eapply mem_id_le_2_mem_at_eq; eauto.
Qed.

Lemma match_state_linv_implies_sim:
  forall inj lo b
    state_tgt lc_tgt sc_tgt mem_tgt
    state_src lc_src sc_src mem_src
    (MATCH_STATE: match_state_linv inj lo b
                                   (Thread.mk rtl_lang state_tgt lc_tgt sc_tgt mem_tgt)
                                   (Thread.mk rtl_lang state_src lc_src sc_src mem_src)),
    @local_sim_state nat lt rtl_lang I_linv lo inj dset_init b
                     (Thread.mk rtl_lang state_tgt lc_tgt sc_tgt mem_tgt)
                     (Thread.mk rtl_lang state_src lc_src sc_src mem_src).
Proof.
  cofix COFIX_HP.
  introv MATCH_STATE. 
  destruct (classic (Local.promise_consistent lc_tgt)) as [PROMS_CONS | NOT_PROM_CONS].
  2: {
    eapply local_sim_state_tgt_not_prm_consistent_intro; eauto.
  }
  assert (CONS_SRC: Local.promise_consistent lc_src).
  {
    clear - MATCH_STATE PROMS_CONS. inv MATCH_STATE; ss.
    clear - PROMS_CONS TVIEW_LE. unfold Local.promise_consistent in *; ss.
    ii. exploit PROMS_CONS; eauto. i.
    inv TVIEW_LE. inv CUR; ss. unfold TimeMap.le in *; ss.
    specialize (RLX loc).
    auto_solve_time_rel.
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
      eauto. 
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
          eapply Thread_na_steps_to_na_steps_dset; eauto.
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
        eapply na_read_step_case in STEP; eauto.
        des.
        eexists. exists (@dset_init nat) (@dset_init nat) (@dset_init nat).
        splits.
        {
          eapply dset_become_na_read. ii; ss. eauto.
        }
        {
          eapply Thread_na_steps_to_na_steps_dset; eauto.
        }
        {
          econs. introv DSET_GET. rewrite dset_gempty in DSET_GET. tryfalse.
          introv DSET_GET. rewrite dset_gempty in DSET_GET. tryfalse.
        }
        {
          eapply COFIX_HP; eauto.
        }
      + (* non-atomic write *)
        destruct ord; tryfalse.
        inv THRD_STEP; ss. inv STEP.
        destruct lc_tgt as (tview_tgt & prm_tgt).
        destruct lc_src as (tview_src & prm_src).
        destruct e_tgt'.
        renames state to state_tgt', local to lc_tgt', sc to sc_tgt', memory to mem_tgt'.
        destruct lc_tgt' as (tview_tgt' & prm_tgt').
        eapply na_write_step_case in STEP; eauto.
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

(** ** Correctness of the Loop Invariant Code Motion *)
(** [LInv] is verified. *)
Theorem verif_linv:
  forall code_s code_t lo,
      LInv lo code_s = Some code_t 
      ->
      @local_sim nat lt rtl_lang I_linv lo code_t code_s.
Proof.
  ii. econs.
  - (* well_founded index *)
    eapply nat_lt_is_well_founded.
  - (* well-formed I_linv *)
    eapply WF_I_linv; eauto.
  - (* I_linv holds in initial state *)
    eapply I_linv_hold_init; eauto.
  - (* local simulation *)
    introv TGT_INIT.
    unfold Language.init in *; ss.
    unfold State.init in *; ss.
    destruct (code_t ! fid) eqn:FUNC_T; ss. destruct f; ss.
    renames c to cdhp_t. renames f to l_t.
    destruct (cdhp_t ! l_t) eqn:ENTRY_BB_T; ss. inv TGT_INIT; ss.
    unfold LInv in H. inv H.
    rewrite PTree.gmap in FUNC_T. unfold option_map in FUNC_T.
    destruct (code_s ! fid) eqn:SCODE_GET; ss.
    unfold det_loop_invs in FUNC_T.
    rewrite PTree.gmap in FUNC_T. unfold option_map in FUNC_T.
    rewrite SCODE_GET in FUNC_T. inv FUNC_T.
    destruct f as (cdph_s & l_s). renames t to BB_t.
    destruct (cdph_s ! l_s) eqn:CDHP_S.
    {
      renames t to BB_s.
      eapply transC_prop in H0; eauto.
      2: {  instantiate (1 := lo). right. exists BB_s. split; eauto. }
      do 7 des1.
      eexists. split; eauto.
      eapply match_state_linv_implies_sim.
      econs; eauto.
      {
        eapply I_linv_hold_init; eauto.
      }
      {
        econs; eauto. 2: { econs; eauto. }
        des1.
        {
          des1.
          rewrite CDHP_S in GET_BB_S. symmetry in GET_BB_S. inv GET_BB_S.
          eapply EXEC_NOT_PH; eauto.
          unfold det_loop_invs.
          rewrite PTree.gmap. unfold option_map. rewrite SCODE_GET.
          rewrite CDHP_S. eauto.
          ii. eapply reg_in_blk_in_cdhp; eauto.
        }
        {
          des1. 
          eapply EXEC_PH with (f := fid); eauto.
          unfold det_loop_invs.
          rewrite PTree.gmap. unfold option_map.
          rewrite SCODE_GET. rewrite CDHP_S. eauto.
        }
      }
      {
        eapply TView.TView.le_PreOrder_obligation_1; eauto.
      }
      {
        ii. rewrite Memory.bot_get in H. ss.
      }
      {
        eapply Local.wf_init; eauto.
      }
      {
        unfold Memory.closed_timemap. ii.
        unfold TimeMap.bot.
        unfold Memory.get, Memory.init.
        rewrite Cell.init_get. des_if; ss; eauto.
        unfold Message.elt. eauto.
      }
      {
        eapply Memory.init_closed; eauto.
      }
      {
        eapply Local.wf_init; eauto.
      }
      {
        unfold Memory.closed_timemap. ii.
        unfold TimeMap.bot.
        unfold Memory.get, Memory.init.
        rewrite Cell.init_get. des_if; ss; eauto.
        unfold Message.elt. eauto.
      }
      {
        eapply Memory.init_closed; eauto.
      }
    }
    {
      ss.
      assert (GET_EMPTY: (PTree.empty positive) ! l_s = None).
      rewrite PTree.gempty. eauto.
      rewrite GET_EMPTY in H0; ss. inv H0. tryfalse.
    }
Qed.

(** Loop invariant code motion optimizer is correct. *)
Theorem correct_licm:
  Correct licm.
Proof.
  unfold licm.
  eapply correct_optimizer_transitive; eauto.
  eapply correct_cse; eauto.
  eapply Verif_implies_Correctness.
  unfolds Verif. intros. exists I_linv nat lt. 
  eapply verif_linv; eauto.
Qed.
