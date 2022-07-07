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

Require Import CSEProofAux.
Require Import CSEProofMState.
Require Import CSEProofStep.

(** * Correctness Proof of Common subexpression elimination *)

(** Top level proofs for Common Subexpression Elimination's correctness *)

(** the top lemma organizes individual transition's correctness *)
Theorem cse_match_state_implies_sim:
  forall inj lo e_tgt e_src b,
  cse_match_state inj lo e_tgt e_src b
  -> @local_sim_state nat lt rtl_lang cse_invariant lo inj DelaySet.dset_init b e_tgt e_src.
Proof.
  cofix COFIX.
  intros.
  destruct e_tgt as (st_tgt, lc_tgt, sc_tgt, mem_tgt) eqn:EqETgt.
  destruct e_src as (st_src, lc_src, sc_src, mem_src) eqn:EqESrc.

  pose proof (classic (Local.promise_consistent lc_tgt)).
  destruct H0 as [CsstTgt|NotCsstTgt].
  2: {
    eapply local_sim_state_tgt_not_prm_consistent_intro; eauto.
  }

  pose proof (classic (Thread.is_abort e_tgt lo)).
  destruct H0 as [|NotAbort]. 
  { 
    eapply local_sim_state_abort_intro; eauto.
    eapply cse_match_state_implies_abort_preserving. splits; eauto.
    rewrite EqETgt in H0; eauto.
  } 

  eapply local_sim_state_step_intro; eauto.
  eapply cse_match_state_implies_si; eauto.
  4: { (** case: abort step -> sim. proved. *)
    intro. rewrite EqETgt in NotAbort. contradiction.
  }
  3: { (** case: done step -> sim *)
    pose proof (classic (Thread.is_done e_tgt)).

    destruct H0 as [Done|NotDone].
    2: {
      intros. rewrite <- EqETgt in DONE. contradiction.
    }
    (** case: done. straightforward. *)
    intros. clear DONE.
    inversion H. simpls.
    exists e_src; exists inj'.
    splits; eauto.
    { (** na_steps *)
      rewrite <- EqESrc.
      eapply rtc_refl.
      econs.
    }
    2: { (** trivial incr_inj *)
      destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
      apply eq_inj_implies_incr; trivial.
      trivial.
    }
    2: { (** trivial invariant *)
      rewrite EqESrc; simpls.
      trivial.
    }
    { (** tgt done -> src done *)
      unfolds Thread.is_done.
      destruct Done as (IsTermTgt & NoPrmTgt).
      splits.
      2: { (** src promise free *)
        rewrite EqESrc. rewrite EqETgt in NoPrmTgt. simpls.
        inv H. inv MATCH_LOCAL. simpls.
        rewrite <- PROMISES_EQ. trivial. 
      }
      { (** src done *)
        unfolds Language.is_terminal; simpls.
        unfolds State.is_terminal.
        destruct IsTermTgt as (RetTgt & ContDoneTgt).
        inv H.
        inv MATCH_LOCAL. 
        inv MATCH_RTL_STATE. simpls.
        splits.
        inv MATCH_FRAME.
        remember (AveAI.br_from_i analysis !! l i) as ai. 
        rewrite RetTgt in TRANSF_BLK.
        eapply ret_transformed_by_ret; eauto.

        inv MATCH_CONT.  
        destruct DONE; trivial.
        rewrite ContDoneTgt in CONT_T; discriminate.
      }
    }
  }
  2: { (** case: rely step -> sim *)
    intro.
    splits.
    { (** I still holds *)
      inv H; simpls. 
      destruct PREEMPT as [(_&EQ_INJ) | (B&INCR_INJ)].
      2: { discriminate. }
      eapply eq_inj_implies_invariant; eauto.
      eapply eq_inj_sym.
      trivial. 
    }
    intros.
    rewrite OUT_ATMBLK in H.
    eapply cse_match_state_preserving_rely in H; eauto.
  }
  (** case: thread step -> sim *)
  intros. splits.
  { (** case: at step -> sim *)
    intros.
    destruct e_tgt' as (st_tgt', lc_tgt', sc_tgt', mem_tgt') eqn:EqETgt'.
    eapply cse_match_state_preserving_at 
      with (st_tgt' := st_tgt') (lc_tgt' := lc_tgt') 
           (sc_tgt' := sc_tgt') (mem_tgt' := mem_tgt')
      in H; eauto. 
    2: {
          { 
            inversion STEP.
            {
              (** at is not prc *)
              inv STEP0.
              unfolds ThreadEvent.is_at_or_out_step. contradiction.
            }
            trivial.
          } 
      }
      {
        destruct H as (st_src' & lc_src' & sc_src' & mem_src' & inj' & H & H1 & H2).
        remember {|
                Thread.state := st_src';
                Thread.local := lc_src';
                Thread.sc := sc_src';
                Thread.memory := mem_src'
              |} as e_src'.
        
        exists e_src. exists e_src'. exists inj'. exists te.
        rewrite <- EqESrc.
        splits; eauto.
        rewrite EqESrc.
        trivial.
        eapply thrdevt_eq_refl.
      }
  }
  { (** case: na step -> sim *)
    intros.
    destruct e_tgt' as (st_tgt', lc_tgt', sc_tgt', mem_tgt') eqn:EqETgt'.
    pose proof classic (ThreadEvent.is_na_access te).
    destruct H0 as [IS_NA_ACCESS | NOT_NA_ACCESS].
    { (** is na access *)
      eapply cse_match_state_preserving_na_access 
      with (st_tgt' := st_tgt') (lc_tgt' := lc_tgt') 
          (sc_tgt' := sc_tgt') (mem_tgt' := mem_tgt')
      in H; eauto. 
      destruct H as (st_src' & lc_src' & sc_src' & mem_src' & H1 & H2).
      2: {
          { 
            inversion STEP.
            {
              inv STEP0.
              unfolds ThreadEvent.is_at_or_out_step. contradiction.
            }
            trivial.
          } 
        }
        remember {|
        Thread.state := st_src';
        Thread.local := lc_src';
        Thread.sc := sc_src';
        Thread.memory := mem_src'
      |} as e_src'.
      pose proof classic (ThreadEvent.is_na_write te).
      destruct H as [IS_NA_WRITE | NOT_NA_WRITE].
      2: { (** na read *)
        exists e_src'. 
        do 3 exists (@DelaySet.dset_init nat).
        unfolds ThreadEvent.is_na_write; unfolds ThreadEvent.is_na_access.
        inversion H1.
        simpls.
        destruct te; simpls; try contradiction; eauto.
        destruct ord; simpls; try contradiction; eauto.
        splits; eauto.
        - eapply DelaySet.dset_become_na_read; eauto.
        - eapply DelaySet.na_steps_dset_read with (dset:=DelaySet.dset_init) in H1; eauto.
          {
            eapply Operators_Properties.clos_rt1n_step in H1.
            rewrite <- H6 in H1.
            rewrite H1.
            eapply rtc_refl. econs.
          }
          {
            simpls. intros.
            rewrite DelaySet.dset_gempty in H.
            discriminate.
          }           
        - eapply DelaySet.dset_reduce_init; eauto.
        - rewrite <- H6 in H2. auto.
      }
      (** is na write *)
      unfolds ThreadEvent.is_na_write. 
      destruct te; try contradiction; eauto.
      destruct ord; try contradiction; eauto.
      exists e_src'. 
      exists (DelaySet.dset_add loc to 0 DelaySet.dset_init).
      do 2 exists (@DelaySet.dset_init nat).
      splits; eauto. 
      - eapply DelaySet.dset_become_na_write; eauto. 
      - eapply DelaySet.na_steps_dset_write in H1; eauto.
        right. exists to.
        rewrite DelaySet.dset_remove_add. trivial.
      - eapply DelaySet.dset_reduce_init.
    }
    { (** is na silent *)
      unfolds ThreadEvent.is_na_access.
      unfolds ThreadEvent.is_na_step.
      destruct te eqn:EqTe; simpls; eauto; try contradiction.
      clear NA_STEP; clear NOT_NA_ACCESS.
      eapply cse_match_state_preserving_na_silent
      with (st_tgt' := st_tgt') (lc_tgt' := lc_tgt') 
          (sc_tgt' := sc_tgt') (mem_tgt' := mem_tgt')
      in H; eauto.
      2: {
        inversion STEP. inversion STEP0.   auto.
      } 
      destruct H as (st_src' & lc_src' & sc_src' & mem_src' & te' & SILENT & SRCSTEP & MATCH_STATE).
      remember {|
        Thread.state := st_src';
        Thread.local := lc_src';
        Thread.sc := sc_src';
        Thread.memory := mem_src'
      |} as e_src'.
      exists e_src'.
      do 3 exists (@DelaySet.dset_init nat).
      splits; eauto.
      - eapply DelaySet.dset_become_na_read; eauto.
      - destruct SILENT; eauto. 
        { 
          rewrite H in SRCSTEP.
          eapply DelaySet.na_steps_dset_tau in SRCSTEP; eauto. 
        }
        { 
          unfold ThreadEvent.is_na_read in H.
          destruct te'; try discriminate; try contradiction; eauto.
          destruct ord; try contradiction; eauto.
          eapply DelaySet.na_steps_dset_read in SRCSTEP; eauto.
          simpls.
          intros.
          rewrite DelaySet.dset_gempty in H0; discriminate.
        }
      - eapply DelaySet.dset_reduce_init; eauto.
    }
  }
  { (** case: promise step -> sim *)
    intros.
    destruct e_tgt' as (st_tgt', lc_tgt', sc_tgt', mem_tgt') eqn:EqETgt'.
    eapply cse_match_state_preserving_prm 
      with (st_tgt' := st_tgt') (lc_tgt' := lc_tgt') 
          (sc_tgt' := sc_tgt') (mem_tgt' := mem_tgt')
          (te := te)
      in H; eauto.
    2: {
      rewrite PROMISE in STEP.
      destruct PRM_STEP as (loc & t & PRM_STEP).
      unfolds ThreadEvent.is_promising.
      destruct te; try discriminate; eauto. 
      inv PRM_STEP.
      inv STEP.
      trivial.
    }
    destruct H as (st_src' & lc_src' & sc_src' & mem_src' & inj' & H & H1 & H2).
    remember {|
        Thread.state := st_src';
        Thread.local := lc_src';
        Thread.sc := sc_src';
        Thread.memory := mem_src'
      |} as e_src'.
    exists e_src'. exists inj'. 
    splits; eauto.
    eapply rtc_n1 with (b:=e_src).
    - rewrite EqESrc. eapply rtc_refl. trivial.
    - rewrite EqESrc.  
      rewrite PROMISE in STEP.
      destruct PRM_STEP as (loc & t & PRM_STEP).
      unfolds ThreadEvent.is_promising.
      destruct te; try discriminate; eauto.
      inv PRM_STEP. 
      eapply Thread.prc_step_intro; eauto.
  }
  { (** case: promise-free step -> sim *)
    intros.
    destruct e_tgt' as (st_tgt', lc_tgt', sc_tgt', mem_tgt') eqn:EqETgt'.
    eapply cse_match_state_preserving_pf_prm 
      with (st_tgt' := st_tgt') (lc_tgt' := lc_tgt') 
           (sc_tgt' := sc_tgt') (mem_tgt' := mem_tgt')
      in H; eauto.
    2: {
        eapply Thread.pf_promise_step_intro with (e:=te).
        rewrite PF in STEP.
        destruct PRM_STEP as (loc & t & PRM_STEP).
        unfolds ThreadEvent.is_promising.
        destruct te; try discriminate; eauto. 
        inv PRM_STEP. simpls.
        inv STEP; eauto.
        inversion STEP0.
        inv LOCAL; try discriminate; eauto. 
    } 
    destruct H as (st_src' & lc_src' & sc_src' & mem_src' & H & H1).
    remember {|
        Thread.state := st_src';
        Thread.local := lc_src';
        Thread.sc := sc_src';
        Thread.memory := mem_src'
      |} as e_src'.
    exists e_src'.
    splits; eauto.
  }
Qed.

(** ** Correctness of the Common subexpression elimination *)
(** proof for initial match state *)
Theorem verif_cse:
  forall code_s code_t lo,
      cse_optimizer lo code_s = Some code_t 
      ->
      @local_sim nat lt rtl_lang cse_invariant lo code_t code_s.
Proof.
  intros.
  constructor.
  - apply nat_lt_is_well_founded.
  - apply wf_cse_invariant.
  - apply cse_invariant_init.
  - intros.
    inv INIT_STATE.
    unfolds State.init; simpls. 
    destruct (code_t ! fid) eqn:CodetFunc; try discriminate.
    destruct f eqn:FunctCdhp. destruct (c ! f0) eqn:CdhptBlk; try discriminate.
    inversion H1. clear H1. rewrite H2.
    pose proof H as OPT.
    unfold cse_optimizer in H. inversion H. clear H.
    unfolds transform_prog.
    pose proof CodetFunc.
    rewrite <- H1 in H.

    rewrite PTree.gmap in H.
    unfolds Coqlib.option_map.
    destruct (code_s ! fid) eqn:CodeSFunc; try discriminate.
    inversion H. clear H.
    destruct f1 eqn:FuncS.
    rename f1 into func_s, c0 into cdhp_s, f2 into fentry_s.
    rename f into func_t, c into cdhp_t, f0 into fentry_t, t into blk_t.
    (** 
      code_t -> func_t -> (cdhp_t, fentry_t) -> blk_t
      code_s -> func_s -> chdp_s [] -> [] 
    *)
    unfolds transform_func.
    remember (AveDS.analyze_program code_s succ AveLat.top Ave_B.transf_blk) ! fid as AFunc.
    assert (fentry_s = fentry_t). {
      destruct AFunc; inv H3; auto. 
    } 
    remember (cdhp_s ! fentry_s) as opt_blk_s.
    destruct opt_blk_s eqn:BlkS.
    2: {  (** blk_t exists implies blk_s exists  *)
      destruct AFunc eqn:AFuncEq. 
      2: { (** AFunc = None => blk_t = blk_s *)
        inversion H3. rewrite H4 in Heqopt_blk_s. rewrite H5 in Heqopt_blk_s. rewrite <- Heqopt_blk_s in CdhptBlk. discriminate.
      } (** AFunc = Some res => blk_t becomes from blk_s *)
      inversion H3.
      pose proof CdhptBlk.
      unfolds transform_cdhp.
      rewrite <- H4 in H0.
      rewrite PTree.gmap in H0.
      unfolds Coqlib.option_map.  
      destruct (cdhp_s ! fentry_t) eqn:BlkSS; try discriminate. 
      rename t into blk_s. rewrite <- H5 in BlkSS. rewrite BlkSS in Heqopt_blk_s. discriminate.
    }
    rename t into blk_s.
    clear BlkS opt_blk_s.
    (** Some prepare clean-up finished.*)
    (** Now we have:  
        fid & AFunc
        code_t -> func_t -> (cdhp_t, fentry_t) -> blk_t
          SS       SS          SS       ||         SS
        code_s -> func_s -> (chdp_s, fentry_t) -> blk_s 
    *)
    (** Let prove match_state_init *)
    remember (State.mk RegFile.init blk_s cdhp_s Continuation.done code_s) as st_src.
    exists st_src.
    splits.
    { (** Init(code_s, fid) = st_src*)
        unfolds State.init. rewrite CodeSFunc. rewrite <- Heqopt_blk_s. eapply f_equal. eauto.
    }
    (** let's prove local simulation *)  
    (** 1. we have match_state on initial states *)
    pose proof (cse_invariant_init lo).
  assert (cse_match_state inj_init lo 
    (Thread.mk rtl_lang st_tgt Local.init TimeMap.bot Memory.init) 
    (Thread.mk rtl_lang st_src Local.init TimeMap.bot Memory.init) true). {
      eapply cse_match_state_intro with (inj' := inj_init); simpls; eauto.
      2: { (** inj = inj' = init_inj *)
        left. splits; eauto.
        unfolds eq_inj. intros; eauto.
      }
      2: {
        eapply Local.wf_init.
      }
      2: {
        eapply Memory.closed_timemap_bot.
        unfolds Memory.inhabited; intros; eauto.
      }
      2: {
        eapply Memory.init_closed.
      }
      (** match local state *)
      eapply cse_match_local_state_intro; eauto.
      2: {
        unfolds Local.init; simpl; eauto. unfolds TView.eq; eauto.
      }
      destruct AFunc eqn:AFunc_is_None.
      (** match rtl state *)
      eapply cse_match_rtl_state_intro; eauto.
      { (** transform code_s aprog = code_t *) 
        rewrite Heqst_src; simpls. 
        rewrite <- H2; simpls. auto.
      }
      2: { (* match_cont *)
      rewrite Heqst_src; rewrite <- H2; simpls. 
      eapply cse_match_cont_base; auto. 
      }
      { (* cse_match_frame *)
        rename a into acdhp.
        eapply cse_match_frame_intro with (i := 0) (l := fentry_s) (enode := fentry_s) (blk := blk_s) (analysis:= acdhp); 
        try rewrite Heqst_src; try rewrite <- H2; simpls; eauto.
        2: { inv H3; trivial. }
        3: { (** match abstract interp *)
          unfolds match_abstract_interp; unfolds AveAI.br_from_i; simpls.
          assert (AveAI.ge (AveAI.getFirst (acdhp !! fentry_s)) AveLat.top).
          {
            eapply AveDS.analyze_func_entry; eauto.
            eapply Ave_B.wf_transf_blk.
          }
          remember (AveAI.getFirst acdhp!!fentry_s) as aentry.
          - destruct aentry; eauto. 
            simpls.
            intros.
            pose proof W.empty_1. unfolds W.Empty. unfolds W.Subset.
            eapply H4 in H5. eapply H6 in H5. contradiction.
        }
        2: {  (** transform blk_s analysis fentry_s => blk_t *)
            unfolds AveAI.br_from_i; simpls.
            inversion H3; clear H6.
            unfold transform_cdhp in H5.
            pose proof CdhptBlk.
            rewrite <- H5 in H4.
            rewrite PTree.gmap in H4; unfolds Coqlib.option_map; simpls.
            rewrite <- H in H4; rewrite <- Heqopt_blk_s in H4.
            inversion H4.
            unfold transform_blk'. rewrite H; auto.
        }
        {
            pose proof HeqAFunc.
            unfold AveDS.analyze_program in H4.
            rewrite PTree.gmap1 in H4.
            unfolds Coqlib.option_map.
            rewrite CodeSFunc in H4. simpls.
            inversion H4. 
            remember (AveDS.fixpoint_blk cdhp_s succ fentry_s AveLat.top
                (fun (n : positive) (ai : AveDS.AI.t) =>
                match cdhp_s ! n with
                | Some b => Ave_B.transf_blk ai b
                | None => AveDS.AI.Atom ai
                end)) as acdhp_partial.
            destruct acdhp_partial eqn:acdhp_partial_eq.
             - left.  trivial.
             - right. trivial.  
        }
        { (** link *)
          unfolds AveAI.br_from_i; simpls.
          intros.
          eapply AveDS.analyze_func_solution; eauto.
          eapply Ave_B.wf_transf_blk.
          eapply Ave_B.wf_transf_blk2.
        }
        {
          unfolds AveAI.br_from_i; simpls.
          assert (AveAI.ge (AveAI.getFirst (acdhp !! fentry_s)) AveLat.top).
          {
            eapply AveDS.analyze_func_entry; eauto.
            eapply Ave_B.wf_transf_blk.
          }
          unfold AveAI.ge in H4. unfold AveDS.L.ge in H4.
          destruct (AveAI.getFirst acdhp !! fentry_s) eqn:EqEntry; unfolds AveLat.top; try contradiction; eauto.
          assert (W.Empty tuples). {
            unfolds W.Subset.
            pose proof (classic (exists a, W.In a tuples)). destruct H5; trivial.
            2: {
              unfold W.Empty.
              eapply not_ex_all_not. trivial.
            }
            destruct H5.
            specialize (H4 x H5).
            pose proof W.empty_1. unfolds W.Empty. 
            specialize (H6 x). contradiction.
          }
          unfolds loc_fact_valid.
          intros. 
          unfolds W.Empty. 
          specialize (H5 (AveTuple.AVar r loc)). 
          contradiction.
        }
      }
      {
          rewrite <- H2.
          rewrite Heqst_src.
          simpls.
          eapply AveDS.wf_analyze_func with (eval := AveLat.top) (transfb := Ave_B.transf_blk) in CodeSFunc; eauto.
          destruct CodeSFunc as (acdhp & ACdhp).
          rewrite ACdhp in HeqAFunc. discriminate.
      }
      {
        unfold mem_injected.
        intros.
        unfold Local.init in MSG; simpls. 
        rewrite Memory.bot_get in MSG. discriminate.
      }
    }
    apply cse_match_state_implies_sim in H4; simpls; auto.
Qed.
 
(** Common subexpression elimination optimizer is correct. *)
Theorem correct_cse:
  Correct cse_optimizer.
Proof.
  eapply Verif_implies_Correctness.
  unfolds Verif. intros. exists cse_invariant nat lt. 
  eapply verif_cse; eauto.
Qed.
