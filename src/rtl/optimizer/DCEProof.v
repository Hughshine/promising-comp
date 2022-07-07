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

Require Import CompAuxDef.
Require Import DCEProofMState.
Require Import MemoryProps.
Require Import promiseCertifiedAux.
Require Import ConsistentProp.
Require Import Mem_at_eq_lemmas.
Require Import DCE.
Require Import DCEProofStep.
Require Import Lib_Step.

(** * Correctness Proof of Dead Code Elimination *)

(** ** Well-Formed Invariant *)
(** The invariant [I_dce] for DCE proof is well-formed. *)
Lemma WF_I_dce: wf_I I_dce.
Proof.
  unfold wf_I. ii.
  destruct S; ss. des.
  eapply msgInj_implies_weak_msgInj; eauto.
Qed.

Lemma I_dce_hold_init
      lo:
  I_dce lo inj_init (Build_Rss TimeMap.bot Memory.init TimeMap.bot Memory.init).
Proof.
  econs; eauto.
  (* TMapInj init *)
  rewrite inj_init_eq_spec_inj_init_mem.
  eapply spec_inj_tmapinj; eauto.

  split.
  (* MsgInj init *)
  eapply MsgInj_init.

  split.
  (* reserving timestamps *)
  ii. unfold inj_init in H0; ss. des_ifH H0; ss; subst.
  inv H1. auto_solve_time_rel.

  split.
  (* reservation only on atomic locations *)
  ii. unfold Memory.get, Memory.init in H; ss.
  rewrite Cell.init_get in H; ss.
  des_ifH H; ss.

  split.
  ii.
  unfold inj_init in H0; eauto.
  des_ifH H0; ss; subst. inv H0; eauto.
  eapply Memory.init_closed; eauto.
Qed.

Lemma ai_interp_init
      ai:
  ai_interp inj_init RegFile.init TView.bot RegFile.init TView.bot ai.
Proof.
  unfold ai_interp. destruct ai; ss.
Qed.

Lemma TM_init
      loc:
  TM inj_init loc TimeMap.bot TimeMap.bot Memory.init.
Proof.
  econs; eauto.
  introv INJ. unfold inj_init in INJ. des_ifH INJ; subst; ss.
  inv INJ. ss.
  exists Time.bot. split; ss.
  split; ss. eapply Time.le_lteq; eauto.
  ii; simpl. inv H; ss. unfold TimeMap.bot in *; ss.
  eapply Time.le_lteq in TO. des; subst.
  auto_solve_time_rel.
  auto_solve_time_rel.
Qed.

Lemma promises_rel_init
      lo:
  promises_relation inj_init lo Memory.bot Memory.bot.
Proof.
  econs; eauto.
  econs; eauto.
  introv DSET_EMPTY_GET. rewrite dset_gempty in DSET_EMPTY_GET. ss.
  introv GET_BOT. rewrite Memory.bot_get in GET_BOT. ss.
  introv GET_BOT. rewrite Memory.bot_get in GET_BOT. ss.
Qed.

(** ** Match state for DCE implies local simulation *)
(** [match_state_implies_SI] shows that the match state for dce implies the step invariant.  *)
Lemma match_state_implies_SI
      inj lo b
      state_tgt lc_tgt sc_tgt mem_tgt
      state_src lc_src sc_src mem_src
      (MATCH_STATE: match_state_dce inj lo b
                                    (Thread.mk rtl_lang state_tgt lc_tgt sc_tgt mem_tgt)
                                    (Thread.mk rtl_lang state_src lc_src sc_src mem_src)):
  SI inj lo (state_tgt, lc_tgt, mem_tgt) (state_src, lc_src, mem_src) (@dset_init nat).
Proof.
  inv MATCH_STATE; ss.
  econs; eauto.
  - simpl. introv INJ LT.
    assert (INJ_INCR: forall loc t t', inj loc t = Some t' -> inj' loc t = Some t').
    {
      clear - ATM_BIT. des; subst; ss.
    }
    clear - VIEW_MATCH INJ LT INJ_INCR INV. des. clear INJ_SC TS_RSV NO_RSVs. inv VIEW_MATCH.
    destruct (lo loc) eqn:Heqe.
    {
      inv INJ_MEM.
      eapply ATM_LOC_CUR_RLX in Heqe.
      eapply INJ_INCR in INJ.
      eauto.
    }
    {
      eapply NA_LOC_CUR_RLX in Heqe. inv Heqe.
      eapply INJ_INCR in INJ. eauto.
    }
  - simpl. exists (@dset_init nat). unfold promises_relation in PROM_INJ.
    destruct PROM_INJ. split; eauto.
    eapply init_dset_subset.
Qed. 

(** [match_state_dce_implies_sim] shows that the match state for dce implies the thread-local simulation.  *)
Lemma match_state_dce_implies_sim:
  forall inj lo b
    state_tgt lc_tgt sc_tgt mem_tgt
    state_src lc_src sc_src mem_src
    (MATCH_STATE: match_state_dce inj lo b
                                  (Thread.mk rtl_lang state_tgt lc_tgt sc_tgt mem_tgt)
                                  (Thread.mk rtl_lang state_src lc_src sc_src mem_src)),
    @local_sim_state nat lt rtl_lang I_dce lo inj dset_init b
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
      split. eauto. split. eapply COFIX_HP; eauto. eauto.
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
        2: {eapply match_state_dce_implies_promise_consistent; eauto. }
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
        2: { right. eauto. }
        2: { eapply match_state_dce_implies_promise_consistent; eauto. }
        des.
        eexists. exists (@dset_init nat) (@dset_init nat) (@dset_init nat).
        splits.
        {
          eapply dset_become_na_read. ii; ss. eauto.
        }
        {
          eapply Operators_Properties.clos_rt1n_step.
          eapply Thread_na_step_to_na_step_dset; eauto. 
          destruct te'; ss; des; tryfalse. des; subst.
          eapply Thread.na_plain_read_step_intro; eauto.
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
        eapply na_read_write_step_case in STEP; eauto.
        2: { left. exists loc from to val released. eauto. }
        2: { eapply match_state_dce_implies_promise_consistent; eauto. }
        des.
        do 2 eexists. exists (@dset_init nat) (@dset_init nat).
        splits.
        {
          econs; eauto.
        }
        {
          instantiate (2 := 5%nat).
          eapply Operators_Properties.clos_rt1n_step.
          destruct te'; ss; des; subst; ss. des; subst.
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
      2: {eapply match_state_dce_implies_promise_consistent; eauto. }
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
      2: {eapply match_state_dce_implies_promise_consistent; eauto. }
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

(** ** Correctness of the Dead Code Elimination *)
(** Dead code elimination is verified. *)
Theorem verif_dce:
  forall code_s code_t lo,
      dce_optimizer lo code_s = Some code_t 
      ->
      @local_sim nat lt rtl_lang I_dce lo code_t code_s.
Proof.
  ii. econs.
  - (* well_founded index *)
    eapply nat_lt_is_well_founded.
  - (* well-formed I_dce *)
    eapply WF_I_dce.
  - eapply I_dce_hold_init; eauto.
  - introv TGT_INIT.
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
    eapply match_state_dce_implies_sim; eauto.
    econs; eauto.
    {
      eapply I_dce_hold_init.
    }
    {
      eapply Mem_at_eq_init; eauto.
    }
    {
      econs; simpl; eauto.
      assert (TRANS_BLK: exists ai ai_pblk, transf_blk (LvDS.AI.getLast (ab !! f)) B_s = LvDS.AI.Cons ai ai_pblk).
      {
        eapply transf_blk_cons; eauto.
      }
      des.
      econs; eauto.
      unfold transform_cdhp in ENTRY_BB_T.
      rewrite PTree.gmap in ENTRY_BB_T. unfold option_map in ENTRY_BB_T.
      rewrite H0 in ENTRY_BB_T. inv ENTRY_BB_T.
      destruct ((snd ab) ! f) eqn:GET_AB.
      {
        unfold transform_blk. unfold "!!". rewrite GET_AB.
        exploit LvDS.analyze_func_solution_backward_get; eauto.
        ii. eapply wf_transf_blk; eauto.
        introv TRANS_BLK'; subst.
        rewrite TRANS_BLK. eauto.
      }
      {
        exploit LvDS.analyze_func_solution_backward_get_none; eauto.
        ii. eapply wf_transf_blk; eauto. introv GET_NONE.
        rewrite GET_NONE in TRANS_BLK. simpl in TRANS_BLK. rewrite GET_NONE.
        simpl. rewrite TRANS_BLK. eauto.
      }

      eapply ai_interp_init; eauto.
 
      introv SUCC NXT.
      eapply LvDS.analyze_func_solution_backward'; eauto.
      ii.
      eapply wf_transf_blk; eauto.

      econs; eauto.
    }
    {
      econs; try solve [ii; ss]; ss.
      ii. eapply TM_init; eauto.
      ii. eapply TM_init; eauto.
      ii. split.
      rewrite inj_init_eq_spec_inj_init_mem.
      eapply spec_inj_tmapinj; eauto.
      rewrite inj_init_eq_spec_inj_init_mem.
      eapply spec_inj_tmapinj; eauto.
    }
    {
      simpl. unfold cur_acq. ii. right; ss.
    }
    {
      simpl. unfold cur_acq_pln. ii. right; ss.
      split. eapply Time.le_lteq; eauto. eapply Time.le_lteq; eauto.
    }
    {
      eapply promises_rel_init; eauto.
    }
    {
      eapply Local.wf_init; eauto.
    }
    {
      eapply Memory.closed_timemap_bot; eauto.
    }
    {
      eapply Memory.init_closed; eauto.
    }
    {
      eapply Local.wf_init; eauto.
    }
    {
      eapply Memory.closed_timemap_bot; eauto.
    }

    exploit transform_prog_proper_none; eauto.
    introv TGT_NONE_CONTR. rewrite FUNC_T in TGT_NONE_CONTR. ss.
Qed.

(** Dead code elimination optimizer is correct. *)
Theorem correct_dce:
  Correct dce_optimizer.
Proof.
  eapply Verif_implies_Correctness.
  unfolds Verif. intros. exists I_dce nat lt. 
  eapply verif_dce; eauto.
Qed.
