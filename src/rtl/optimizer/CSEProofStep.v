
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

(** Correctness for individual steps *)

(** Match State implies Framework's Step Invariant*)
Theorem cse_match_state_implies_si:
forall inj lo (st_tgt st_src: Language.state rtl_lang) 
              (lc_tgt lc_src: Local.t) 
              (mem_tgt mem_src: Memory.t) 
              sc_tgt sc_src 
              b,
  cse_match_state inj lo 
    (Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) (Thread.mk rtl_lang st_src lc_src sc_src mem_src) b -> 
  @SI rtl_lang nat inj lo (st_tgt, lc_tgt, mem_tgt) (st_src, lc_src, mem_src) DelaySet.dset_init.
Proof.
    intros.
    inv H. 
    inv INVARIANT.
    inv MATCH_LOCAL.
    destruct lc_tgt as (tview_tgt, prm_tgt) eqn:EqLcTgt.
    destruct lc_src as (tview_src, prm_src) eqn:EqLcSrc.    

    eapply SI_intro; simpls; eauto.
    3: {
    destruct H0. unfolds Mem_at_eq.
    intros. rewrite H0. unfolds Mem_approxEq_loc. tauto.  
    }
    {
    (* SI.a: mapping *)
    intros.
    destruct H0.  
    destruct PREEMPT.
    { 
        unfolds eq_ident_mapping.
        destruct H3.
        destruct H4 as (PREEMPT & EQ_INJ).
        unfold eq_inj in EQ_INJ.
        rewrite EQ_INJ in H1.
        eapply H5 in H1.
        rewrite <- H1.
        rewrite <- TVIEW_EQ.
        trivial.
    }
    { (** FIXME: dup *)
        unfolds eq_ident_mapping.
        destruct H3.
        unfold incr_inj in H4.
        apply H4 in H1.
        eapply H5 in H1.
        rewrite <- H1.
        rewrite <- TVIEW_EQ.
        trivial.
    }
    }
    { (** delay set *)
        exists (@DelaySet.dset_init nat).
        splits.
        eapply DelaySet.init_dset_subset.
        rewrite PROMISES_EQ.
        eapply rel_promises_intro; eauto.
        {
        intros.
        pose proof (DelaySet.dset_gempty nat loc t).
        rewrite H2 in H1. discriminate. 
        }
        {
        intros.
        exists t f val R; eauto. splits; eauto.
        destruct H0.
        rewrite PROMISES_EQ in INJ_PROMISES.
        unfolds mem_injected.
        eapply INJ_PROMISES in H1. destruct H1.
        
        unfolds eq_ident_mapping. destruct H2.
        destruct PREEMPT as [(B&EQ_INJ) | (B&INCR_INJ)].
        { unfolds eq_inj.
            pose proof H1.
            apply EQ_INJ in H1.
            apply H3 in H1.
            rewrite <- H1 in H4; trivial.
        }
        { unfolds incr_inj.
            pose proof H1.
            apply INCR_INJ in H1.
            apply H3 in H1.
            rewrite <- H1 in H4; trivial.
        }
        }
    { 
        intros.
        exists t'.
        splits.
        2: { right. repeat eexists; eauto. }
        destruct H0. (** FIXME: dup *)
        rewrite PROMISES_EQ in INJ_PROMISES.
        unfolds mem_injected.
        eapply INJ_PROMISES in H1. destruct H1.
        unfolds eq_ident_mapping. destruct H2.
        destruct PREEMPT as [(B&EQ_INJ) | (B&INCR_INJ)].
        { unfolds eq_inj.
        pose proof H1.
        apply EQ_INJ in H1.
        apply H3 in H1.
        rewrite <- H1 in H4; trivial.
        }
        { unfolds incr_inj.
        pose proof H1.
        apply INCR_INJ in H1.
        apply H3 in H1.
        rewrite <- H1 in H4; trivial.
        }
    } 
    }
Qed.

(** Tgt Abort implies Src Abort *)
Theorem cse_match_state_implies_abort_preserving:
  forall inj lo e_tgt e_src b,
  (cse_match_state inj lo e_tgt e_src b /\ Thread.is_abort e_tgt lo) 
  -> Thread.is_abort e_src lo.
Proof.
  intros.
  destruct H as (MatchState, AbortTgt).
  destruct e_tgt as (st_tgt, lc_tgt, sc_tgt, mem_tgt) eqn:EqETgt.
  destruct e_src as (st_src, lc_src, sc_src, mem_src) eqn:EqESrc.
  unfolds Thread.is_abort.
  destruct AbortTgt as (CsstTgt & AbortTgt).
  destruct AbortTgt as [StuckTgt | [RWOrdNotMatch | UpdOrdNotMatch]];
  destruct lc_tgt as (tview_tgt, prm_tgt) eqn:EqLcTgt;
  destruct lc_src as (tview_src, prm_src) eqn:EqLcSrc;
  assert (LcEq: lc_tgt = lc_src).
  {
    inv MatchState.
    inv MATCH_LOCAL.
    inv MATCH_RTL_STATE;
    simpls;
    rewrite <- TVIEW_EQ;
    rewrite <- PROMISES_EQ;
    trivial. 
  }
  - (** tgt is stuck -> src is stuck *)
    splits; eauto; simpls.
    { 
      rewrite <- EqLcSrc.
      rewrite <- LcEq.
      rewrite <- EqLcTgt in CsstTgt.
      trivial.
    }
    left.
    (** stuck tgt: no step & not done *)
    eapply not_or_and in StuckTgt. 
    destruct StuckTgt as (NotStepTgt, NotDoneTgt).
    eapply and_not_or. 
    destruct st_tgt as (regs_tgt, blk_tgt, cdhp_tgt, cont_tgt, code_tgt).
    destruct st_src as (regs_src, blk_src, cdhp_src, cont_src, code_src).
    splits.
    { (** no step *) 
      inv MatchState.
      inv MATCH_LOCAL.
      inv MATCH_RTL_STATE.
      (** frame match *)
      simpls.
      inversion MATCH_FRAME.  
      simpls.
      intro. 
      apply NotStepTgt.
      destruct H as (e & st_src' & STEP).
      destruct st_src' as (regs_src', blk_src', cdhp_src', cont_src', code_src') eqn:EqStSrcMid.
      inversion STEP. 
      - (** skip *)
        rewrite BLK0 in TRANSF_BLK.
        eapply transform_blk_induction in TRANSF_BLK; eauto.
        destruct TRANSF_BLK as (i' & b_tgt' & B_TGT & TRSF).  
        destruct TRSF as (TRSF_INST & TRSF_BLK).
        *   
          exists (ProgramEvent.silent) {|
                State.regs := regs_tgt;
                State.blk := b_tgt';
                State.cdhp := cdhp_tgt;
                State.cont := cont_tgt;
                State.code := code_tgt
              |}.
          eapply State.step_skip; eauto.
          rewrite B_TGT.
          unfolds transform_inst.
          rewrite TRSF_INST.
          trivial.
      - (** assign *)
        rewrite BLK0 in TRANSF_BLK.
        eapply transform_blk_induction in TRANSF_BLK; eauto.
        destruct TRANSF_BLK as (i' & b_tgt' & B_TGT & TRSF).  
        destruct TRSF as (TRSF_INST & TRSF_BLK).
        *   
          exists (ProgramEvent.silent) {|
                State.regs := RegFun.add r (RegFile.eval_expr e0 regs_src) regs_tgt;
                State.blk := b_tgt';
                State.cdhp := cdhp_tgt;
                State.cont := cont_tgt;
                State.code := code_tgt
              |}.
          eapply transform_assign_rhs_eval_eq in TRSF_INST; eauto. 
          destruct TRSF_INST as (e' & I' & EQEVAL).
          eapply State.step_assign with (r:=r) (e:= e'); eauto.
          rewrite I' in B_TGT; trivial.
          rewrite EQEVAL; rewrite REG_EQ. trivial.
       - (** load *)
        rewrite BLK0 in TRANSF_BLK.
        eapply transform_blk_induction in TRANSF_BLK; eauto.
        destruct TRANSF_BLK as (i' & b_tgt' & B_TGT & TRSF).  
        destruct TRSF as (TRSF_INST & TRSF_BLK).
        * (** load -> assign | load -> load 不变 *)
          unfolds transform_inst.
          pose proof (classic (or = Ordering.plain)).
          destruct H0.
          2: {
            destruct or; try contradiction; eauto; 
            exists (e) {|
              State.regs := RegFun.add r v regs_tgt;
              State.blk := b_tgt';
              State.cdhp := cdhp_tgt;
              State.cont := cont_tgt;
              State.code := code_tgt
            |}; 
            rewrite <- H;
            eapply State.step_load with (r:=r); eauto;
            rewrite <- TRSF_INST in B_TGT; trivial.
          }
          destruct or; try contradiction; try discriminate; eauto.
          remember (AveLat.GetRegByLoc loc (AveAI.getFirst analysis_blk)) as cse.
          destruct cse eqn:EqCse; try discriminate; eauto.
          2: { (** no cse for load, no opt *)
              exists (e) {|
              State.regs := RegFun.add r v regs_tgt;
              State.blk := b_tgt';
              State.cdhp := cdhp_tgt;
              State.cont := cont_tgt;
              State.code := code_tgt
            |}.
            rewrite <- H.
            eapply State.step_load with (r:=r); eauto.
            rewrite <- TRSF_INST in B_TGT; trivial.
          }
          (** there is cse, transform load to assign *)
          rename t into reg'.
          exists (ProgramEvent.silent) {|
               (* State.regs := RegFun.add r v regs_tgt; *)
                State.regs := RegFun.add r (RegFile.eval_expr (Inst.expr_reg reg') regs_tgt) regs_tgt;
                State.blk := b_tgt';
                State.cdhp := cdhp_tgt;
                State.cont := cont_tgt;
                State.code := code_tgt
              |}.
          (** load r loc or -> assign r r'. 证明abort使用的还是反证法，只要说明src not abort 可以推出tgt也可能not abort就好，证明是简单的*)
          eapply State.step_assign with (r:=r) (e:= (Inst.expr_reg reg')); eauto.
          (* destruct or; try contradiction; eauto. *)
          rewrite <- TRSF_INST in B_TGT; trivial.
      - (** store *)
        rewrite BLK0 in TRANSF_BLK.
        eapply transform_blk_induction in TRANSF_BLK; eauto.
        destruct TRANSF_BLK as (i' & b_tgt' & B_TGT & TRSF).  
        destruct TRSF as (TRSF_INST & TRSF_BLK).
        * 
          exists (e) {|
                State.regs := regs_tgt;
                State.blk := b_tgt';
                State.cdhp := cdhp_tgt;
                State.cont := cont_tgt;
                State.code := code_tgt
              |}.
          rewrite <- H.          
          eapply State.step_store with(e:=e0); eauto.
          rewrite B_TGT.
          unfolds transform_inst.
          rewrite TRSF_INST.
          trivial.
          rewrite REG_EQ.
          rewrite <- H in STEP. inversion STEP. trivial.
      - (** syscall *) 
        rewrite BLK0 in TRANSF_BLK.
        eapply transform_blk_induction in TRANSF_BLK; eauto.
        destruct TRANSF_BLK as (i' & b_tgt' & B_TGT & TRSF).  
        destruct TRSF as (TRSF_INST & TRSF_BLK).
          * 
            exists (e) {|
                  State.regs := regs_tgt;
                  State.blk := b_tgt';
                  State.cdhp := cdhp_tgt;
                  State.cont := cont_tgt;
                  State.code := code_tgt
                |}.
            rewrite <- H.          
          eapply State.step_out with(e:=e0); eauto.
          rewrite B_TGT.
          unfolds transform_inst.
          rewrite TRSF_INST.
          trivial.
          rewrite REG_EQ.
          rewrite <- H in STEP. inversion STEP. trivial.
      - (** cas1 *) 
        rewrite BLK0 in TRANSF_BLK.
        eapply transform_blk_induction in TRANSF_BLK; eauto.
        destruct TRANSF_BLK as (i' & b_tgt' & B_TGT & TRSF).  
        destruct TRSF as (TRSF_INST & TRSF_BLK).
          * 
            exists (e) {|
                  State.regs := RegFun.add r Integers.Int.one regs_tgt;
                  State.blk := b_tgt';
                  State.cdhp := cdhp_tgt;
                  State.cont := cont_tgt;
                  State.code := code_tgt
                |}.
            rewrite <- H.          
          eapply State.step_cas_same with (r:=r) (er:=er) (ew:=ew); eauto.
          rewrite B_TGT.
          unfolds transform_inst.
          rewrite TRSF_INST.
          trivial.
          rewrite REG_EQ. trivial.
          rewrite REG_EQ. trivial.
      - (** cas2 *) 
        rewrite BLK0 in TRANSF_BLK.
        eapply transform_blk_induction in TRANSF_BLK; eauto.
        destruct TRANSF_BLK as (i' & b_tgt' & B_TGT & TRSF).  
        destruct TRSF as (TRSF_INST & TRSF_BLK).
          * 
            exists (e) {|
                  State.regs := RegFun.add r Integers.Int.zero regs_tgt;
                  State.blk := b_tgt';
                  State.cdhp := cdhp_tgt;
                  State.cont := cont_tgt;
                  State.code := code_tgt
                |}.
            rewrite <- H.          
          eapply State.step_cas_flip with (r:=r) (er:=er) (ew:=ew); eauto.
          rewrite B_TGT.
          unfolds transform_inst.
          rewrite TRSF_INST.
          trivial.
          rewrite REG_EQ. 
          rewrite VALR.
          trivial.
      - (** call *) 
        rewrite BLK0 in TRANSF_BLK.
        unfold transform_blk in TRANSF_BLK.
        (* destruct blk_tgt; destruct analysis_blk; try discriminate; eauto. *)
        assert (blk_tgt = BBlock.call f fret). {
          destruct blk_tgt; destruct analysis_blk; try discriminate; eauto.
        }
        rewrite <- H10 in FIND_FUNC.
        eapply cse_wf_transform_blk in OPT; eauto.
        destruct OPT as (cdhp_tgt' & blk_tgt' & TgtCdhp & TgtBlk).
        eapply eq_sym in TRANSL_CDHP.
        eapply cse_wf_transform_cdhp in TRANSL_CDHP; eauto.
        destruct TRANSL_CDHP as (b'' & TCDHP).
        exists e {|
                  State.regs := RegFile.init;
                  State.blk := blk_tgt';
                  State.cdhp := cdhp_tgt';
                  State.cont := Continuation.stack regs_tgt b'' cdhp_tgt cont_tgt;
                  State.code := code_tgt
                |}.
        rewrite <- H.
        eapply State.step_call; eauto.
      - (** ret *) 
        exists e.
        inversion MATCH_CONT.
        * destruct DONE.
          rewrite BLK0 in STEP.
          rewrite H11 in STEP.
          inversion STEP; try discriminate; eauto.
        *  
          exists {|
            State.regs := regs_t;
            State.blk := blk_t;
            State.cdhp := cdhp_t;
            State.cont := cont_tgt';
            State.code := code_tgt
          |}.
        rewrite <- H.
        eapply State.step_ret; eauto.
        unfold transform_blk in TRANSF_BLK.
        rewrite BLK0 in TRANSF_BLK. 
        destruct analysis_blk; try discriminate; eauto.
      - (** fence_rel *) 
        rewrite BLK0 in TRANSF_BLK.
        eapply transform_blk_induction in TRANSF_BLK; eauto.
        destruct TRANSF_BLK as (i' & b_tgt' & B_TGT & TRSF).  
        destruct TRSF as (TRSF_INST & TRSF_BLK).
        * 
          exists (e) {|
                State.regs := regs_tgt;
                State.blk := b_tgt';
                State.cdhp := cdhp_tgt;
                State.cont := cont_tgt;
                State.code := code_tgt
              |}.
          rewrite <- H.          
        eapply State.step_fence_rel; eauto.
        rewrite B_TGT.
        unfolds transform_inst.
        rewrite TRSF_INST.
        trivial.

      - (** fence_acq *)
        rewrite BLK0 in TRANSF_BLK.
        eapply transform_blk_induction in TRANSF_BLK; eauto.
        destruct TRANSF_BLK as (i' & b_tgt' & B_TGT & TRSF).  
        destruct TRSF as (TRSF_INST & TRSF_BLK).
        * 
          exists (e) {|
                State.regs := regs_tgt;
                State.blk := b_tgt';
                State.cdhp := cdhp_tgt;
                State.cont := cont_tgt;
                State.code := code_tgt
              |}.
          rewrite <- H.          
        eapply State.step_fence_acq; eauto.
        rewrite B_TGT.
        unfolds transform_inst.
        rewrite TRSF_INST.
        trivial.

      - (** fence_sc *) 
        rewrite BLK0 in TRANSF_BLK.
        eapply transform_blk_induction in TRANSF_BLK; eauto.
        destruct TRANSF_BLK as (i' & b_tgt' & B_TGT & TRSF).  
        destruct TRSF as (TRSF_INST & TRSF_BLK).
        * 
          exists (e) {|
                State.regs := regs_tgt;
                State.blk := b_tgt';
                State.cdhp := cdhp_tgt;
                State.cont := cont_tgt;
                State.code := code_tgt
              |}.
          rewrite <- H.          
        eapply State.step_fence_sc; eauto.
        rewrite B_TGT.
        unfolds transform_inst.
        rewrite TRSF_INST.
        trivial.
      - (** jmp *) 
         exists e.
         eapply eq_sym in TRANSL_CDHP. 
         rewrite <- H8 in TGT.
         eapply cse_wf_transform_cdhp with (f:=f) in TRANSL_CDHP; eauto.
         destruct TRANSL_CDHP as (b_tgt' & TCDHP).
         rewrite <- H.
         exists {|
          State.regs := regs_tgt;
          State.blk := b_tgt';
          State.cdhp := cdhp_tgt;
          State.cont := cont_tgt;
          State.code := code_tgt
          |}.
          eapply State.step_jmp; eauto.
          unfold transform_blk in TRANSF_BLK.
          rewrite BLK0 in TRANSF_BLK. 
          destruct analysis_blk; try discriminate; eauto.
      - (** be *)  
        exists e.
        destruct BRANCH as [(CdhpSrc & Cond) | (CdhpSrc & Cond)].
        *  
        eapply eq_sym in TRANSL_CDHP. 
        rewrite <- H8 in CdhpSrc.
        eapply cse_wf_transform_cdhp with (f:=f1) in TRANSL_CDHP; eauto.
        destruct TRANSL_CDHP as (b_tgt' & TCDHP).
        rewrite <- H.
        exists {|
          State.regs := regs_tgt;
          State.blk := b_tgt';
          State.cdhp := cdhp_tgt;
          State.cont := cont_tgt;
          State.code := code_tgt
          |}.
        eapply State.step_be; eauto.
        unfold transform_blk in TRANSF_BLK.
        rewrite BLK0 in TRANSF_BLK. 
        destruct analysis_blk; try discriminate; eauto.
        left. splits; eauto.
        rewrite REG_EQ; rewrite H6; rewrite <- COND in Cond; eauto.
        * 
          eapply eq_sym in TRANSL_CDHP. 
          rewrite <- H8 in CdhpSrc.
          eapply cse_wf_transform_cdhp with (f:=f2) in TRANSL_CDHP; eauto.
          destruct TRANSL_CDHP as (b_tgt' & TCDHP).
          rewrite <- H.
          exists {|
            State.regs := regs_tgt;
            State.blk := b_tgt';
            State.cdhp := cdhp_tgt;
            State.cont := cont_tgt;
            State.code := code_tgt
            |}.
          eapply State.step_be; eauto.
          unfold transform_blk in TRANSF_BLK.
          rewrite BLK0 in TRANSF_BLK. 
          destruct analysis_blk; try discriminate; eauto.
          right. splits; eauto.
          rewrite REG_EQ; rewrite H6; rewrite <- COND in Cond; eauto.
    }
    { (** not done *)
      inv MatchState.
      inv MATCH_LOCAL.
      inv MATCH_RTL_STATE.
      (** frame match *)
      simpls. 
      inversion MATCH_FRAME.  
      simpls.
      intro. 
      apply NotDoneTgt.
      unfolds State.is_terminal; simpls.
      inv MATCH_CONT. 
      destruct DONE; trivial. subst.
      destruct H. subst.
      simpl. destruct (AveAI.br_from_i analysis !! l i); eauto.
      destruct H. discriminate.
    } 
  - (** tgt -> src: load/store unmatch access*) 
    { (** FIXME: dup*)
      inv MatchState.
      inv MATCH_LOCAL.
      inv MATCH_RTL_STATE;
      simpls;
      rewrite <- TVIEW_EQ;
      rewrite <- PROMISES_EQ;
      trivial. 
    }
    - 
    splits; eauto; simpls.
    { 
      rewrite <- EqLcSrc.
      rewrite <- LcEq.
      rewrite <- EqLcTgt in CsstTgt.
      trivial.
    }
    inv MatchState.
    inv MATCH_LOCAL.
    inv MATCH_RTL_STATE.
    (** frame match *)
    simpls.
    inversion MATCH_FRAME.  
    simpls.
    right. 
    trivial. left. 
    destruct RWOrdNotMatch as (st_tgt' & x & o & v & RW & NOT_MATCH).
    destruct RW.
      * inversion H.
         { 
          destruct st_src as (regs_src, blk_src, cdhp_src, cont_src, code_src) eqn:EqStSrc.
          rewrite <- H0 in REG_EQ.
          simpls.
          (* rewrite REG_EQ in VAL. *)
          rewrite <- H0 in TRANSF_BLK; simpls. rewrite BLK0 in TRANSF_BLK.
          pose proof TRANSF_BLK.
          eapply load_transformed_by_load in H5.
          destruct H5 as (b'' & H').
          eexists.
          exists x o v. 
          splits; eauto.
          left.
          eapply State.step_load; eauto.
         }
         { 
          destruct st_src as (regs_src, blk_src, cdhp_src, cont_src, code_src) eqn:EqStSrc.
          rewrite <- H0 in REG_EQ.
          simpls.
          (* rewrite REG_EQ in VAL. *)
          rewrite <- H0 in TRANSF_BLK; simpls. rewrite BLK0 in TRANSF_BLK.
          pose proof TRANSF_BLK.
          eapply cas_transformed_by_cas in H5.
          destruct H5 as (b'' & H').
          eexists.
          exists x o v. 
          splits; eauto.
          left.
          eapply State.step_cas_flip with (er:= er); eauto.
          {
            rewrite REG_EQ in VALR. rewrite VALR.
            unfold Integers.Int.cmp. trivial.
          }
         }
      * inversion H.
        destruct st_src as (regs_src, blk_src, cdhp_src, cont_src, code_src) eqn:EqStSrc.
        rewrite <- H0 in REG_EQ.
        simpls.
        rewrite REG_EQ in VAL.
        rewrite <- H0 in TRANSF_BLK; simpls. rewrite BLK0 in TRANSF_BLK.
        pose proof TRANSF_BLK.
        eapply store_transformed_by_store in H5.
        destruct H5 as (b'' & H').
        eexists.
        exists x o v. 
        splits; eauto.
        right.
        eapply State.step_store with (e:=e); eauto.
  - (** tgt -> src: upd unmatch access *)
    { (** FIXME: dup*)
      inv MatchState.
      inv MATCH_LOCAL.
      inv MATCH_RTL_STATE;
      simpls;
      rewrite <- TVIEW_EQ;
      rewrite <- PROMISES_EQ;
      trivial. 
    }
    - 
    splits; eauto; simpls.
    { 
      rewrite <- EqLcSrc.
      rewrite <- LcEq.
      rewrite <- EqLcTgt in CsstTgt.
      trivial.
    }
    inv MatchState.
    inv MATCH_LOCAL.
    inv MATCH_RTL_STATE.
    (** frame match *)
    simpls.
    inversion MATCH_FRAME.  
    simpls.
    right; right. 
    destruct UpdOrdNotMatch as (st_tgt' & x & vr & vw & or & ow & UPD & NOT_MATCH).
    inversion UPD.
    destruct st_src as (regs_src, blk_src, cdhp_src, cont_src, code_src) eqn:EqStSrc.
    rewrite <- H5 in REG_EQ.
    simpls.
    (* rewrite REG_EQ in VAL. *)
    rewrite <- H5 in TRANSF_BLK; simpls. rewrite BLK0 in TRANSF_BLK.
    pose proof TRANSF_BLK.
    eapply cas_transformed_by_cas in H.
    destruct H as (b'' & H).
    eexists.
    exists x vr vw or ow. 
    splits; eauto.
    eapply State.step_cas_same with (er:= er); eauto.
    {
      rewrite REG_EQ in VALR. rewrite VALR.
      unfold Integers.Int.cmp. trivial.
    }
    {
      rewrite REG_EQ in VALW. rewrite VALW.
      unfold Integers.Int.cmp. trivial.
    }
Qed.

(** Local step's correctness: [skip], [assign], [jmp], [be], [call], [ret] *)
Theorem cse_match_state_preserving_na_silent:
  forall te lo inj st_tgt st_src sc_tgt lc_src lc_tgt mem_tgt sc_src mem_src b st_tgt' lc_tgt' sc_tgt' mem_tgt', 
    Thread.program_step te lo 
        (@Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) 
        (@Thread.mk rtl_lang st_tgt' lc_tgt' sc_tgt' mem_tgt') 
    -> 
    ThreadEvent.silent = te 
    ->   
    (cse_match_state inj lo 
      (Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) 
      (Thread.mk rtl_lang st_src lc_src sc_src mem_src) b)
    -> 
      (exists st_src' lc_src' sc_src' mem_src' te,
          (te = ThreadEvent.silent \/ ThreadEvent.is_na_read te)
          /\
          Thread.program_step te lo (@Thread.mk rtl_lang st_src lc_src sc_src mem_src) 
                                    (@Thread.mk rtl_lang st_src' lc_src' sc_src' mem_src') 
          /\
          (cse_match_state inj lo 
          (Thread.mk rtl_lang st_tgt' lc_tgt' sc_tgt' mem_tgt') (Thread.mk rtl_lang st_src' lc_src' sc_src' mem_src') false)
      ).
Proof.
  intros.
  destruct st_tgt as (regs_tgt, blk_tgt, cdhp_tgt, cont_tgt, code_tgt).
  destruct st_tgt' as (regs_tgt', blk_tgt', cdhp_tgt', cont_tgt', code_tgt').
  destruct st_src as (regs_src, blk_src, cdhp_src, cont_src, code_src); simpls.
  inv H1.
  pose proof MATCH_LOCAL as MATCH_LOCAL'.
  inv MATCH_LOCAL.
  inv MATCH_RTL_STATE; simpls. 
  inv MATCH_FRAME; simpls.
  inv H; simpls. 
  inversion STATE; simpls; subst.

  - (*** skip *) 
    remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
    remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
    eapply eq_sym in Heqblk_tgt.
    rewrite BLK0 in Heqblk_tgt.
    eapply transform_blk_induction' in Heqblk_tgt; eauto.
    destruct Heqblk_tgt as (inst & b_src' & EqBlkSrc & TRSF).
    destruct TRSF as (TRSF_INST & TRSF_BLK).
    * 
      exists {|
          State.regs := regs_tgt';
          State.blk := b_src';
          State.cdhp := cdhp_src;
          State.cont := cont_src;
          State.code := code_src
        |} lc_src sc_src mem_src (ThreadEvent.silent).
      splits; eauto.
      { (** skip -> skip  *)
          eapply Thread.program_step_intro; simpls; eauto.
          eapply State.step_skip; eauto.
          eapply skip_transformed_inst_by_skip in TRSF_INST.
          rewrite <- TRSF_INST; trivial.
      }
      { (** match state *)
        inversion LOCAL.
        eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
        { (** invariant *)
          rewrite <- H5. rewrite <- H4. trivial.
        }
        {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { 
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                eapply H7 in H.
                folds AveAI.b.
                rewrite H.
                eapply always_match_top.
              }
              eapply Ave_B.wf_transf_blk_step in H; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H.
              eapply skip_transformed_inst_by_skip in TRSF_INST.
              rewrite TRSF_INST in H.
              unfolds Ave_I.transf.
              rewrite <- H.
              trivial.
            }
            {
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H; eauto.
                folds AveAI.b.
                rewrite H.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H; eauto.
              rewrite <- H. trivial.
            }
            {
              destruct ANALYSIS as [ANALYSIS | ANALYSIS].
              eapply transf_step_psrv_loc_fact_valid; eauto.
              eapply Ave_B.wf_transf_blk_step; eauto.
              pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
              apply A in ANALYSIS.
              folds AveAI.b.
              rewrite ANALYSIS. 
              eapply top_is_loc_fact_valid.
            }
        }
        {
          right. 
          splits; trivial.
          destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
          apply eq_inj_implies_incr; trivial.
          trivial.
        }
        {
          rewrite <- H3; rewrite <- H5.
          trivial.
        }
        {
          rewrite <- H4; rewrite <- H5. 
          trivial.
        }
        {
          rewrite <- H5.
          trivial.
        }
      }
  - (** assign *)
    remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
    remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
    eapply eq_sym in Heqblk_tgt.
    rewrite BLK0 in Heqblk_tgt.
    eapply transform_blk_induction' in Heqblk_tgt; eauto.
    destruct Heqblk_tgt as (inst & b_src' & EqBlkSrc & TRSF).
    destruct TRSF as (TRSF_INST & TRSF_BLK).
    * 
      eapply assign_transformed_inst_by_assign_or_na_load in TRSF_INST.
      destruct TRSF_INST as [ASSIGN|[(loc & r' & LOAD & GET_REG & E) | (expr & r' & ASSIGN & GET_REG & E)]].
      { (** assign = assign, seems no need for this case... *)
        exists {|
            State.regs := RegFun.add r (RegFile.eval_expr e regs_src) regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_src sc_src mem_src (ThreadEvent.silent). 
        splits; eauto. 
        { (** assign = assign  *)
            eapply Thread.program_step_intro; simpls.
            eapply State.step_assign; eauto.
            rewrite <- ASSIGN; trivial.
            eapply Local.step_silent; eauto.
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            rewrite <- H5. rewrite <- H4. trivial.
          }
          {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { 
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                eapply H7 in H.
                folds AveAI.b.
                rewrite H.
                eapply always_match_top.
              }
              eapply Ave_B.wf_transf_blk_step in H; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H.
              rewrite ASSIGN in H.
              pose proof MATCH_AI as MATCH_AI'.
              unfold match_abstract_interp in MATCH_AI.
              unfold match_abstract_interp.
              remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
              remember (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1))) as ai'.
              unfold Ave_I.transf in H.
              remember (AveLat.opt_expr_with_ave e (AveLat.kill_reg ai r)) as opt_e.
              remember (AveLat.GetRegByExpr opt_e (AveLat.kill_reg ai r)) as GetReg.
              destruct GetReg eqn:EqGetReg.
              {
                destruct ai eqn:EqAi.
                { 
                  unfold AveLat.kill_reg in H. rewrite <- H. trivial.
                }
                {
                  unfold AveLat.kill_reg in H. rewrite <- H.
                  intros.
                  rename t into r'.
                  simpls. discriminate. 
                }
                {
                  unfold AveLat.kill_reg in H. rewrite <- H.
                  intros.
                  rename t into r'.
                  des_ifH H.
                  2: {
                    intros.
                    assert (W.In tu tuples). {
                      eapply W.filter_1 in H7; trivial.
                      eapply AveTuple.compat_bool_freeOfReg.
                    }
                    specialize (MATCH_AI tu H8).
                    (** get_reg tu <> r *)
                    unfolds match_abstract_fact.
                    destruct tu eqn:EqTu.
                    { (** (r, e) *)
                      assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inv H.
                          eapply W.filter_2 in H7. 
                          unfolds AveTuple.freeOfReg.
                          eapply sflib__andb_split in H7.
                          destruct H7.
                          unfolds negb.
                          destruct (reg =? r)%positive eqn:RegEq.
                          try discriminate; eauto.
                          rewrite Pos.eqb_sym in RegEq.
                          eapply Pos.eqb_neq; eauto. 
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }

                      inv H.

                      pose proof H9.
                      eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr e regs_src)) (regs:=regs_src) in H9.
                      folds Const.t.
                      rewrite H9. 
                      assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                        eapply W.filter_2 in H7.
                        unfolds AveTuple.freeOfReg.
                        intro.
                        eapply sflib__andb_split in H7.
                        destruct H7.
                        unfolds negb.
                        des_ifH H1; try discriminate; eauto.
                        rewrite H0 in H2. discriminate.
                        eapply (AveTuple.compat_bool_freeOfReg r).
                      }
                      eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=(RegFile.eval_expr e regs_src)) in H0.
                        folds Const.t.
                        rewrite <- H0.
                        trivial.
                    }
                    { (** (r, x) *)
                      assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inv H.
                          eapply W.filter_2 in H7. 
                          unfolds AveTuple.freeOfReg.
                          unfolds negb.
                          destruct (reg =? r)%positive eqn:RegEq.
                          try discriminate; eauto.
                          rewrite Pos.eqb_sym in RegEq.
                          eapply Pos.eqb_neq; eauto. 
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }
                      eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr e regs_src)) (regs:=regs_src) in H9.
                      folds Const.t.
                      rewrite H9.
                      trivial.
                    } 
                  }
                  intros.
                  pose proof (classic (tu = AveTuple.AExpr r' (Inst.expr_reg r))) as IS_R_R'.
                  destruct IS_R_R' as [IS_R_R' | NOT_R_R'].
                  { (** (r', r) *)
                    rewrite IS_R_R'.
                    unfolds match_abstract_fact.
                      unfolds AveLat.GetRegByExpr.
                      pose proof Heqai'.
                      remember  (RegFile.eval_expr e regs_src) as val.
                      unfold RegFile.eval_expr. rewrite RegFun.add_spec_eq.
                      destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn: KillReg; try discriminate.
                      remember (W.choose (W.filter (AveTuple.isSameExpr opt_e) tuples0)) as Choose.
                      destruct Choose eqn:EqChoose; try discriminate.
                      inversion H2.
                      eapply eq_sym in HeqChoose.
                      eapply W.choose_1 in HeqChoose.
                      pose proof HeqChoose.
                      eapply W.filter_1 in HeqChoose.
                      eapply W.filter_2 in H10.
                      unfold AveTuple.isSameExpr in H10.
                      destruct e0 eqn:EqE; try discriminate.
                      eapply Inst.beq_expr_eq in H10.
                      unfolds AveTuple.get_reg.
                      inversion HeqGetReg.
                      subst reg. 
                      assert (r' <> r). {
                        eapply AveLat.mem_of_kill_reg_implies_neq with (tuples:=tuples) (r:=r)in KillReg; eauto.
                        unfolds AveTuple.get_reg. trivial.
                      }
                      subst val.
                      inv STATE; try discriminate.
                      rewrite Loc_add_neq; eauto.
                      assert (regs_src r' = RegFile.eval_expr e regs_src). {
                        clear - MATCH_AI' MATCH_AI HeqChoose KillReg.
                        remember ((AveLat.opt_expr_with_ave e (AveLat.CSet tuples0))) as opt_e.
                        remember (AveTuple.AExpr r' opt_e) as tu.
                        unfolds AveLat.kill_reg. inversion KillReg.
                        rewrite <- H0 in HeqChoose.
                        eapply W.filter_1 in HeqChoose.
                        specialize (MATCH_AI tu HeqChoose).
                        rewrite Heqtu in MATCH_AI.
                        rewrite MATCH_AI.
                        eapply eq_sym.
                        subst opt_e.
                        eapply match_ai_implies_opt_expr_eval_eq; eauto.
                        eapply ge_prsv_match_ai; eauto.
                        { 
                          unfold AveAI.ge.
                          unfold AveDS.L.ge.
                          unfold W.Subset.
                          intros.
                          rewrite <- H0 in H.
                          eapply W.filter_1 in H; eauto.
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                        eapply AveTuple.compat_bool_freeOfReg.
                      }
                      trivial.
                      eapply AveTuple.compat_bool_isSameExpr.
                      eapply AveTuple.compat_bool_isSameExpr.
                  }
                  (** old tu *)
                  assert (W.In tu tuples). {
                    eapply W.add_3 in H7.
                    eapply W.filter_1 in H7; trivial.
                    eapply AveTuple.compat_bool_freeOfReg.
                    intro. rewrite H8 in NOT_R_R'. contradiction.
                  }
                  specialize (MATCH_AI tu H8).
                  unfolds match_abstract_fact.
                  destruct tu eqn:EqTu.
                  { (** (r, e) *)
                    assert (r <> reg). {
                      destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                      {
                        subst. discriminate. 
                      }
                      {
                        subst. discriminate. 
                      }
                      {
                        inv H.
                        eapply W.add_3 in H7.
                        2: {
                          intro. 
                          rewrite H in NOT_R_R'.
                          contradiction.
                        }
                        eapply W.filter_2 in H7. 
                        unfolds AveTuple.freeOfReg.
                        eapply sflib__andb_split in H7.
                        destruct H7.
                        unfolds negb.
                        destruct (reg =? r)%positive eqn:RegEq.
                        try discriminate; eauto.
                        rewrite Pos.eqb_sym in RegEq.
                        eapply Pos.eqb_neq; eauto. 
                        eapply AveTuple.compat_bool_freeOfReg.
                      }
                    }

                    inv H.
                    eapply W.add_3 in H7; eauto.
                    pose proof H9.
                    eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr e regs_src)) (regs:=regs_src) in H9.
                    folds Const.t.
                    rewrite H9. 
                    assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                      eapply W.filter_2 in H7.
                      unfolds AveTuple.freeOfReg.
                      intro.
                      eapply sflib__andb_split in H7.
                      destruct H7.
                      unfolds negb.
                      des_ifH H1; try discriminate; eauto.
                      rewrite H0 in H2. discriminate.
                      eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                    eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=(RegFile.eval_expr e regs_src)) in H0.
                      folds Const.t.
                      rewrite <- H0.
                      trivial.
                  }
                  { (** (r, x) *)
                    assert (r <> reg). {
                      destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                      {
                        subst. discriminate. 
                      }
                      {
                        subst. discriminate. 
                      }
                      {
                        inv H.
                        eapply W.add_3 in H7.
                        2: {
                          intro. 
                          rewrite H in NOT_R_R'.
                          contradiction.
                        }
                        eapply W.filter_2 in H7. 
                        unfolds AveTuple.freeOfReg.
                        unfolds negb.
                        destruct (reg =? r)%positive eqn:RegEq.
                        try discriminate; eauto.
                        rewrite Pos.eqb_sym in RegEq.
                        eapply Pos.eqb_neq; eauto. 
                        eapply AveTuple.compat_bool_freeOfReg.
                      }
                    }
                    eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr e regs_src)) (regs:=regs_src) in H9.
                    folds Const.t.
                    rewrite H9.
                    trivial.
                  } 
                }
              }
              {
                destruct ai eqn:EqAi.
                { 
                  unfold AveLat.kill_reg in H. rewrite <- H. trivial.
                }
                {
                  unfold AveLat.kill_reg in H. rewrite <- H. 
                  intros.
                  destruct (negb (RegSet.mem r (Inst.regs_of_expr opt_e))) eqn:MEM.
                  2: {
                    contradiction.
                  }
                  intros.

                  pose proof classic (tu = (AveTuple.AExpr r opt_e)).
                  destruct H8.
                  2: {
                    eapply W.add_3 in H7.
                    2: {
                      intro.
                      rewrite H9 in H8; contradiction.
                    }
                    pose proof W.empty_1. unfolds W.Empty. 
                    specialize (H9 tu). 
                    contradiction.
                  }
                  rewrite H8.
                  unfold match_abstract_fact.
                  rewrite Loc_add_eq.
                  subst opt_e.
                  unfolds AveLat.kill_reg.
                  assert (RegFile.eval_expr (AveLat.opt_expr_with_ave e AveLat.Undef)
                  (RegFun.add r (RegFile.eval_expr e regs_src) regs_src) = RegFile.eval_expr (AveLat.opt_expr_with_ave e AveLat.Undef) regs_src). {
                    eapply eq_sym.
                    eapply regs_add_nonfree_var_eq_eval_expr.
                    intro.
                    rewrite H9 in MEM. 
                    unfolds negb.
                    discriminate.
                  }
                  rewrite H9.
                  eapply match_ai_implies_opt_expr_eval_eq; eauto.
                }
                {
                  remember (AveLat.kill_reg (AveLat.CSet tuples) r ) as Kill.
                  destruct Kill; try discriminate; eauto.
                  destruct (negb (RegSet.mem r (Inst.regs_of_expr opt_e))) eqn:MEM.
                  2: {
                    rewrite <- H.
                    intros.
                    assert (W.In tu tuples). {
                      unfold AveLat.kill_reg in HeqKill.
                      inv HeqKill.
                      eapply W.filter_1 in H7; subst; trivial.
                      eapply AveTuple.compat_bool_freeOfReg.
                    }
                    specialize (MATCH_AI tu H8). 
                    unfolds match_abstract_fact.
                    destruct tu eqn:EqTu.
                    { (** (r, e) *)
                      assert (r <> reg). {
                      destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                      {
                        subst. discriminate. 
                      }
                      {
                        subst. discriminate. 
                      }
                      {
                        inversion HeqKill.
                        rewrite H10 in H7.
                        unfold AveLat.kill_reg in EqKillReg.
                        inversion EqKillReg.
                        rewrite <- H11 in H7.
                        eapply W.filter_2 in H7. 
                        unfolds AveTuple.freeOfReg.
                        eapply sflib__andb_split in H7.
                        destruct H7.
                        unfolds negb.
                        destruct (reg =? r)%positive eqn:RegEq.
                        try discriminate; eauto.
                        rewrite Pos.eqb_sym in RegEq.
                        eapply Pos.eqb_neq; eauto. 
                        eapply AveTuple.compat_bool_freeOfReg.
                      }
                      }
                      inversion HeqKill.
                      rewrite H11 in H7.

                      pose proof H9.
                      eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr e regs_src)) (regs:=regs_src) in H9.
                      folds Const.t.
                      rewrite H9. 
                      assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                        eapply W.filter_2 in H7.
                        unfold AveTuple.freeOfReg in H7.
                        intro.
                        eapply sflib__andb_split in H7.
                        destruct H7.
                        unfolds negb.
                        des_ifH H13; try discriminate; eauto.
                        eapply (AveTuple.compat_bool_freeOfReg r).
                      }
                      eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=(RegFile.eval_expr e regs_src)) in H12.
                      folds Const.t.
                      rewrite <- H12.
                      trivial.
                    }
                    { (** (r, x) *)
                      assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inversion HeqKill.
                          rewrite H10 in H7.
                          unfold AveLat.kill_reg in EqKillReg.
                          inversion EqKillReg.
                          rewrite <- H11 in H7.
                          eapply W.filter_2 in H7. 
                          unfolds AveTuple.freeOfReg.
                          unfolds negb.
                          destruct (reg =? r)%positive eqn:RegEq.
                          try discriminate; eauto.
                          rewrite Pos.eqb_sym in RegEq.
                          eapply Pos.eqb_neq; eauto. 
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }
                      eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr e regs_src)) (regs:=regs_src) in H9.
                      folds Const.t.
                      rewrite H9.
                      trivial.
                    }
                  }
                  rewrite <- H.
                  intros.
                  unfolds match_abstract_fact.
                  destruct tu eqn:EqTu.
                  { (** (r, e) *)
                    pose proof (classic (tu = AveTuple.AExpr r opt_e)).
                    destruct H8.
                    { (** (r, opt_e) *)
                      rewrite EqTu in H8.
                      inversion H8. subst expr. subst reg.
                      rewrite Loc_add_eq.
                      subst opt_e.
                      unfolds AveLat.kill_reg.
                      assert (RegFile.eval_expr (AveLat.opt_expr_with_ave e (AveLat.CSet tuples0))
                      (RegFun.add r (RegFile.eval_expr e regs_src) regs_src) = RegFile.eval_expr (AveLat.opt_expr_with_ave e (AveLat.CSet tuples0)) regs_src). {
                        eapply eq_sym.
                        eapply regs_add_nonfree_var_eq_eval_expr.
                        intro.
                        rewrite H9 in MEM. 
                        unfolds negb.
                        discriminate.
                      }
                      rewrite H9.
                      eapply match_ai_implies_opt_expr_eval_eq; eauto.
                      eapply ge_prsv_match_ai; eauto.
                      inversion HeqKill.
                      {
                        unfold AveAI.ge.
                        unfold AveDS.L.ge.
                        unfold W.Subset.
                        intros.
                        eapply W.filter_1 in H10; eauto.
                        eapply AveTuple.compat_bool_freeOfReg.
                      }
                    }
                    { (** old (r, e) *)
                      eapply W.add_3 in H7; eauto.
                      2: {subst; eauto. }
                      clear H8.
                      assert (r <> reg). {
                      destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                      {
                        subst. discriminate. 
                      }
                      {
                        subst. discriminate. 
                      }
                      {
                        inversion HeqKill.
                        rewrite H9 in H7.
                        unfold AveLat.kill_reg in EqKillReg.
                        inversion EqKillReg.
                        rewrite <- H10 in H7.
                        eapply W.filter_2 in H7. 
                        unfolds AveTuple.freeOfReg.
                        eapply sflib__andb_split in H7.
                        destruct H7.
                        unfolds negb.
                        destruct (reg =? r)%positive eqn:RegEq.
                        try discriminate; eauto.
                        rewrite Pos.eqb_sym in RegEq.
                        eapply Pos.eqb_neq; eauto. 
                        eapply AveTuple.compat_bool_freeOfReg.
                      }
                      }
                      inversion HeqKill.
                      rewrite H10 in H7.

                      pose proof H8.
                      eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr e regs_src)) (regs:=regs_src) in H8.
                      folds Const.t.
                      rewrite H8. 
                      assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                        eapply W.filter_2 in H7.
                        unfold AveTuple.freeOfReg in H7.
                        intro.
                        eapply sflib__andb_split in H7.
                        destruct H7.
                        unfolds negb.
                        des_ifH H12; try discriminate; eauto.
                        eapply (AveTuple.compat_bool_freeOfReg r).
                      }
                      eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=(RegFile.eval_expr e regs_src)) in H11.
                      folds Const.t.
                      rewrite <- H11.
                      trivial.
                      assert (W.In tu tuples). {
                        eapply W.filter_1 in H7; subst; trivial.
                        eapply AveTuple.compat_bool_freeOfReg.
                      }
                      specialize (MATCH_AI tu H12).
                      rewrite EqTu in MATCH_AI. trivial.
                    }
                  }
                  { (** (r, x) *)
                    assert (r <> reg). {
                      destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                      {
                        subst. discriminate. 
                      }
                      {
                        subst. discriminate. 
                      }
                      {
                        inversion HeqKill.
                        rewrite H9 in H7.
                        unfold AveLat.kill_reg in EqKillReg.
                        inversion EqKillReg.
                        rewrite <- H10 in H7.
                        eapply W.add_3 in H7.
                        2: {intro. discriminate. }
                        eapply W.filter_2 in H7. 
                        unfolds AveTuple.freeOfReg.
                        unfolds negb.
                        destruct (reg =? r)%positive eqn:RegEq.
                        try discriminate; eauto.
                        rewrite Pos.eqb_sym in RegEq.
                        eapply Pos.eqb_neq; eauto. 
                        eapply AveTuple.compat_bool_freeOfReg.
                      }
                    }
                    eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr e regs_src)) (regs:=regs_src) in H8.
                    folds Const.t.
                    rewrite H8.
                    assert (W.In tu tuples). {
                      eapply W.add_3 in H7.
                      inv HeqKill.
                      eapply W.filter_1 in H7; subst; trivial.
                      eapply AveTuple.compat_bool_freeOfReg.
                      intro; discriminate.
                    }
                    specialize (MATCH_AI tu H9). subst; trivial.                    
                  }
                }
              }
            }
            { 
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H; eauto.
                folds AveAI.b.
                rewrite H.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H; eauto.
              rewrite <- H. trivial.
            }
            {
              destruct ANALYSIS as [ANALYSIS | ANALYSIS].
              eapply transf_step_psrv_loc_fact_valid; eauto.
              eapply Ave_B.wf_transf_blk_step; eauto.
              pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
              apply A in ANALYSIS.
              folds AveAI.b.
              rewrite ANALYSIS. 
              eapply top_is_loc_fact_valid.
            }
        }
          {
            right. 
            splits; trivial.
            destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
            apply eq_inj_implies_incr; trivial.
            trivial.
          }
          {
            rewrite <- H3; rewrite <- H5.
            trivial.
          }
          {
            rewrite <- H4; rewrite <- H5. 
            trivial.
          }
          {
            rewrite <- H5.
            trivial.
          }
        }
      }
      { (** load -opt-> assign *)
      assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
        {
          destruct ANALYSIS as [ANALYSIS | ANALYSIS].
          eapply transf_step_psrv_loc_fact_valid; eauto.
          eapply Ave_B.wf_transf_blk_step; eauto.
          pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
          apply A in ANALYSIS.
          folds AveAI.b.
          rewrite ANALYSIS. 
          eapply top_is_loc_fact_valid.
        }
      }
      rename H into LOC_FACT_VALID.
        exists {|
            State.regs := RegFun.add r (RegFile.eval_expr e regs_src) regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_src sc_src mem_src. 

        remember ((AveAI.getFirst (AveAI.br_from_i analysis !! l i))) as ai.
        pose proof GET_REG as GET_REG'.
        unfold AveLat.GetRegByLoc in GET_REG.
        destruct ai eqn:EqAi; try discriminate; eauto.
        remember (W.choose (W.filter (AveTuple.isSameLoc loc) tuples)) as ai_tmp.
        destruct ai_tmp eqn:EqAiTmp; try discriminate; eauto.
        rename e0 into tu.
        eapply eq_sym in Heqai_tmp.
        eapply W.choose_1 in Heqai_tmp.
        pose proof Heqai_tmp as TU.
        eapply W.filter_1 in Heqai_tmp.
        eapply W.filter_2 in TU.
        unfold AveTuple.isSameLoc in TU.
        destruct tu eqn:EqTu; try discriminate; eauto.
        pose proof (MATCH_AI tu).
        rewrite <- EqTu in Heqai_tmp.
        apply H in Heqai_tmp.
        clear H.
        unfolds match_abstract_fact. rewrite EqTu in Heqai_tmp. 
        destruct Heqai_tmp as (NON_ATOMIC & t & f & R & PLN & RLX & MSG).
        eapply Pos.eqb_eq in TU. 
        rewrite <- TU in MSG.
        2: {eapply AveTuple.compat_bool_isSameLoc. }
        2: {eapply AveTuple.compat_bool_isSameLoc. }
        pose proof MSG as MSG'.
        assert (regs_src reg = regs_src r'). {
          inv GET_REG. trivial. }
        rename H into REG_R'.

        assert (exists te, te = ThreadEvent.read loc t (RegFile.eval_expr e regs_src) R Ordering.plain). {
          eexists; eauto.
        }
        destruct H as (te & TE).  
        exists te.
        splits; eauto. 
        {
          right. unfold ThreadEvent.is_na_read. rewrite TE. trivial. 
        }
        { (** load -> assign  *)
            eapply Thread.program_step_intro; simpls.
            unfold ThreadEvent.get_program_event.
            rewrite TE.
            eapply State.step_load; eauto.
            rewrite <- LOAD; trivial.
            rewrite TE.
            eapply Local.step_read; eauto.

            (** get abstract fact *)
            eapply Local.read_step_intro with (from:=f); eauto.
            {
              rewrite MSG.
              rewrite E.
              unfold RegFile.eval_expr.
              assert (regs_src reg = regs_src r'). {
                inv GET_REG. trivial. }
              rewrite H.
              trivial.
            }
            { 
              subst.
              unfold Ordering.mem_ord_match.
              rewrite NON_ATOMIC. trivial.
            }
            { 
              econs; subst; eauto.
              replace (Ordering.le Ordering.relaxed Ordering.plain) with false; trivial.
              unfold is_true.
              intro. discriminate.
            }
            {
              assert (lc_src = lc_tgt). {eapply cse_match_local_state_implies_eq_local; eauto. }
              pose proof TU as TU'.
              subst. destruct lc_tgt eqn:EqLcTgt; simpls. 
              unfold TView.read_tview.
              replace (Ordering.le Ordering.relaxed Ordering.plain) with false; trivial.
              replace (Ordering.le Ordering.acqrel Ordering.plain) with false; trivial.
              unfold View.singleton_ur_if.
              unfold View.singleton_rw.
              unfold View.join; unfold View.bot; simpls.
              repeat rewrite TimeMap.join_bot.
              destruct tview eqn:EqTview; simpls; eauto.
              destruct cur eqn:EqCur; simpls; eauto.
              destruct acq eqn:EqAcq; simpls; eauto.
              assert (TimeMap.join rlx (TimeMap.singleton loc0 t) = rlx). {
                eapply TimeMap.le_join_l; eauto.
                unfold TimeMap.singleton.  
                unfold TimeMap.le. intro. 
                pose proof (classic (loc = loc0)).
                destruct H.
                rewrite H. rewrite Loc_add_eq; eauto.
                rewrite Loc_add_neq; eauto. 
                unfold LocFun.init.
                eapply Time.bot_spec.
              }
              assert (TimeMap.join rlx0 (TimeMap.singleton loc0 t) = rlx0). {
                inv LOCAL_WF.
                inv TVIEW_WF. 
                simpls.
                inv CUR_ACQ. simpls.
                eapply TimeMap.le_join_l.
                assert (TimeMap.le  (TimeMap.singleton loc0 t) rlx). {
                  unfold TimeMap.singleton.  
                  unfold TimeMap.le. intro. 
                  pose proof (classic (loc = loc0)).
                  destruct H0.
                  rewrite H0. rewrite Loc_add_eq; eauto.
                  rewrite Loc_add_neq; eauto. 
                  unfold LocFun.init.
                  eapply Time.bot_spec.
                }
                unfolds TimeMap.le.
                intros.
                specialize (RLX0 loc).
                specialize (H0 loc).
                auto_solve_time_rel. 
              }
              rewrite H.
              rewrite H0.
              trivial.
            }
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            rewrite <- H5. rewrite <- H4. trivial.
          }
          {
              eapply cse_match_local_state_intro; 
              try rewrite <- H3; eauto.
              eapply cse_match_rtl_state_intro; eauto.
              simpls.
              eapply cse_match_frame_intro with(i:=i+1); eauto.
              rewrite EqBlkSrc in PARTIAL_BLK.
              eapply bb_from_i_plus_one; eauto.
              rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
              { (** match ai *)
                destruct ANALYSIS.
                2: { (** case: analysis = top; always match_ai *)
                pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                eapply H7 in H.
                folds AveAI.b.
                rewrite H.
                eapply always_match_top.
              }
              eapply Ave_B.wf_transf_blk_step in H; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H.
              rewrite LOAD in H.
              unfolds Ave_I.transf.
                rewrite <- H.
                subst.
                unfolds match_abstract_interp.
                rename loc0 into loc.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.GetRegByLoc loc (AveLat.kill_reg ai r)) as ai'.
                destruct ai eqn:EqAi.
                {
                  discriminate.
                }
                { discriminate.
                }
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1))) as ai''.
                destruct ai'' eqn:EqAi''.
                {subst. rewrite H. 
                  destruct (AveLat.kill_reg (AveLat.CSet tuples0) r ) eqn:Eq1; 
                  destruct (AveLat.GetRegByLoc loc (AveLat.kill_reg (AveLat.CSet tuples) r)) eqn:Eq2; try discriminate;  eauto.
                }
                {subst. rewrite H. 
                  destruct (AveLat.kill_reg (AveLat.CSet tuples0) r ) eqn:Eq1; 
                  destruct (AveLat.GetRegByLoc loc (AveLat.kill_reg (AveLat.CSet tuples) r)) eqn:Eq2; try discriminate;  eauto.
                }
                rewrite H.
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  (** kill_reg r implies r' <> r /\ r not in fv(e), implies eval(e) & eval(r) not changed, still match as in ai *)
                  destruct ai' eqn:EqAi'.
                  { 
                    rename t0 into reg'.
                    pose proof (classic (tu = AveTuple.AExpr reg' (Inst.expr_reg r))).
                    destruct H1.
                    { (** (r', r) *)
                      assert (r' = reg'). {
                        assert (W.In (AveTuple.AVar r' loc) tuples). {
                          clear - GET_REG'.
                          remember (W.choose (W.filter (AveTuple.isSameLoc loc) tuples)) as Choose.
                          destruct Choose eqn:EqChoose; try discriminate.
                          eapply eq_sym in HeqChoose.
                          eapply W.choose_1 in HeqChoose.
                          pose proof HeqChoose.
                          eapply W.filter_1 in HeqChoose.
                          eapply W.filter_2 in H.
                          unfolds AveTuple.isSameLoc.
                          destruct e eqn:EqE; try discriminate.
                          eapply Pos.eqb_eq in H. subst loc0.
                          unfolds AveTuple.get_reg. inv GET_REG'. trivial.
                          eapply AveTuple.compat_bool_isSameLoc.
                          eapply AveTuple.compat_bool_isSameLoc.
                        }
                        assert (W.In (AveTuple.AVar reg' loc) tuples). {
                          inv Heqai.
                          clear - Heqai'.
                          unfolds AveLat.GetRegByLoc.
                          remember (AveLat.kill_reg (AveLat.CSet tuples0) r) as KillReg.
                          destruct KillReg; try discriminate; eauto.
                          remember (W.choose (W.filter (AveTuple.isSameLoc loc) tuples)) as Choose.
                          destruct Choose; try discriminate.
                          inv Heqai'.
                          eapply eq_sym in HeqChoose.
                          eapply W.choose_1 in HeqChoose.
                          pose proof HeqChoose.
                          eapply W.filter_1 in HeqChoose.
                          eapply W.filter_2 in H.
                          unfolds AveTuple.isSameLoc.
                          destruct e eqn:EqE; try discriminate.
                          eapply Pos.eqb_eq in H. subst loc0.
                          unfolds AveTuple.get_reg. 
                          unfolds AveLat.kill_reg.
                          inv HeqKillReg.
                          eapply W.filter_1 in HeqChoose. trivial.
                          eapply AveTuple.compat_bool_freeOfReg.
                          eapply AveTuple.compat_bool_isSameLoc.
                          eapply AveTuple.compat_bool_isSameLoc.
                        }
                        specialize (LOC_FACT r' reg' loc H2 H3). trivial.
                      }
                      rename H2 into CHOOSE_EQ.
                      rewrite H1 in EqTu.
                      inversion EqTu.
                      rewrite <- H3.
                      unfolds transform_inst.
                      unfolds AveLat.GetRegByLoc.
                      pose proof Heqai'.
                      remember (RegFile.eval_expr (Inst.expr_reg r') regs_src) as val.
                      unfold RegFile.eval_expr. rewrite RegFun.add_spec_eq.
                      destruct (AveLat.kill_reg (AveLat.CSet tuples0) r) eqn: KillReg; try discriminate.
                      remember (W.choose (W.filter (AveTuple.isSameLoc loc) tuples2)) as Choose.
                      destruct Choose eqn:EqChoose; try discriminate.
                      inversion H2.
                      eapply eq_sym in HeqChoose.
                      eapply W.choose_1 in HeqChoose.
                      pose proof HeqChoose.
                      eapply W.filter_1 in HeqChoose.
                      eapply W.filter_2 in H5.
                      unfold AveTuple.isSameLoc in H5.
                      destruct e eqn:EqE; try discriminate.
                      eapply Pos.eqb_eq in H5.
                      unfolds AveTuple.get_reg.
                      subst reg'. subst reg0.
                      assert (reg1 <> r). {
                        eapply AveLat.mem_of_kill_reg_implies_neq with (tuples:=tuples0) (r:=r)in KillReg; eauto.
                        unfolds AveTuple.get_reg. trivial.
                      }
                      inv STATE; try discriminate.
                      rewrite Loc_add_neq; eauto.
                      eapply AveTuple.compat_bool_isSameLoc.
                      eapply AveTuple.compat_bool_isSameLoc.
                    } 
                    {
                      (** similar proof *)
                      inv GET_REG.
                      rename reg0 into reg.
                      assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inv H.
                          eapply W.add_3 in H0.
                          2: {
                            intro. 
                            inversion H. simpls. try contradiction.
                            rewrite <- H in H1. 
                            simpls. subst.
                            try contradiction. 
                          }
                          remember (AveLat.kill_reg (AveLat.CSet tuples) r) as _ai.
                          remember (AveTuple.AExpr reg expr) as tu.
                          eapply W.filter_2 in H0.
                          unfold AveTuple.freeOfReg in H0. subst tu.
                          eapply sflib__andb_split in H0.
                          destruct H0.
                          unfolds negb.
                          destruct (reg =? r)%positive eqn:RegEq.
                          try discriminate; eauto.
                          rewrite Pos.eqb_sym in RegEq.
                          eapply Pos.eqb_neq; eauto. 
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }
                      inv H.
                      eapply W.add_3 in H0; eauto.
                      pose proof H0.
                      eapply W.filter_1 in H0.
                      inv Heqai.
                      pose proof (MATCH_AI (AveTuple.AExpr reg expr)).
                      apply H3 in H0.
                      pose proof H2.
                      eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr (Inst.expr_reg r') regs_src)) (regs:=regs_src) in H2.
                      folds Const.t.
                      rewrite H2. 
                      assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                        eapply W.filter_2 in H.
                        unfolds AveTuple.freeOfReg.
                        intro.
                        eapply sflib__andb_split in H.
                        destruct H.
                        unfolds negb.
                        des_ifH H; try discriminate; eauto.
                        rewrite H5 in H6. discriminate.
                        eapply (AveTuple.compat_bool_freeOfReg r).
                      }
                      eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=(RegFile.eval_expr (Inst.expr_reg r') regs_src)) in H5.
                      folds Const.t.
                      rewrite <- H5.
                      trivial.
                      eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                  }
                  { 
                    inv GET_REG.
                    inv Heqai.
                    rename reg0 into reg.
                    rename tuples0 into tuples.
                    assert (r <> reg). {
                      destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                      {
                        subst. discriminate. 
                      }
                      {
                        subst. discriminate. 
                      }
                      {
                        inv H.
                        eapply W.add_3 in H0.
                        2: {
                          intro. try discriminate.
                        }
                        remember (AveLat.kill_reg (AveLat.CSet tuples) r) as _ai.
                        remember (AveTuple.AExpr reg expr) as tu.
                        eapply AveLat.mem_of_kill_reg_implies_neq with (tuples':=tuples0) (tuples:=tuples) (r:=r) in H0; eauto.
                        unfolds AveTuple.get_reg. rewrite Heqtu in H0.  
                        intro. rewrite H in H0. contradiction. 
                      }
                    }
                    inv H.
                    eapply W.add_3 in H0; eauto.
                    2: {
                      intro. discriminate.
                    }
                    pose proof H0.
                    eapply W.filter_1 in H0.
                    pose proof (MATCH_AI (AveTuple.AExpr reg expr)).
                    apply H2 in H0.
                    pose proof H1.
                    eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr (Inst.expr_reg r') regs_src)) (regs:=regs_src) in H1.
                    folds Const.t.
                    rewrite H1. 
                    assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                      eapply W.filter_2 in H.
                      unfolds AveTuple.freeOfReg.
                      intro.
                      eapply sflib__andb_split in H.
                      destruct H.
                      unfolds negb.
                      des_ifH H; try discriminate; eauto.
                      rewrite H4 in H5. discriminate.
                      eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                    eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=(RegFile.eval_expr (Inst.expr_reg r') regs_src)) in H4.
                    folds Const.t.
                    rewrite <- H4.
                    trivial.
                    eapply (AveTuple.compat_bool_freeOfReg r).
                  }
                }
                { (** proof for: (r, x) in ai' is still correct *)
                  inversion GET_REG.
                  inversion Heqai.
                  subst reg.
                  subst tuples.
                  rename reg0 into reg.
                  rename tuples0 into tuples.

                  pose proof (classic (tu = AveTuple.AVar r loc)).
                  destruct H1.
                  { (** (r, x) is newly inserted *)
                    splits; eauto.
                    { (** lo loc = non-atomic *)
                      inv LOCAL.
                      unfolds Ordering.mem_ord_match.
                      inv H1.
                      destruct (lo loc) eqn:EqLocOr; trivial. 
                    }
                    {
                      rewrite EqTu in H1. 
                      inversion H1.
                      inv LOCAL. simpls.
                      rewrite Loc_add_eq.
                      do 3 eexists; eauto. 
                    }
                  }
                  { (** (r, x) is old *)
                    rewrite EqTu in H1. 
                    assert (W.In tu tuples). {
                      (* clear - H2 Heqai'' H14. *)
                      destruct ai'.
                      {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inv H.
                          eapply W.add_3 in H0; eauto.
                          2: { intro. discriminate. }
                          unfolds AveLat.kill_reg.
                          inv EqKillReg.
                          eapply W.filter_1 in H0. trivial.
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }
                      {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inv H.
                          eapply W.add_3 in H0; eauto.
                          inv EqKillReg.
                          eapply W.filter_1 in H0. trivial.
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }
                    }
                    pose proof (MATCH_AI tu). apply H3 in H2.
                    rewrite EqTu in H2. 
                    assert (regs_src reg = RegFun.add r (RegFile.eval_expr (Inst.expr_reg r') regs_src) regs_src reg). {
                      apply eq_sym.
                      assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          destruct ai' eqn:EqAi'.
                          {
                            rename t into reg'.
                            
                            inv H.
                            eapply W.add_3 in H0; eauto.
                            intro.
                            eapply AveLat.mem_of_kill_reg_implies_neq with (tuples:=tuples) in EqKillReg; eauto.
                            unfolds AveTuple.get_reg.
                            trivial.
                            rewrite H. trivial.
                            intro.
                            discriminate.
                          }
                          {
                            inv H.
                            eapply W.add_3 in H0; eauto.
                            intro.
                            eapply AveLat.mem_of_kill_reg_implies_neq with (tuples:=tuples) in EqKillReg; eauto.
                            unfolds AveTuple.get_reg.
                            rewrite H.
                            trivial.
                          }
                        }
                      }
                      eapply regs_add_neg; eauto.
                    }
                    destruct H2.
                    splits; eauto.
                    subst.
                    rewrite <- H4.
                    trivial.
                  }
              }
            }
            { 
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H; eauto.
                folds AveAI.b.
                rewrite H.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H; eauto.
              rewrite <- H. trivial.
            }
          }
          {
            right. 
            splits; trivial.
            destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
            apply eq_inj_implies_incr; trivial.
            trivial.
          }
          {
            rewrite <- H3; rewrite <- H5.
            trivial.
          }
          {
            rewrite <- H4; rewrite <- H5. 
            trivial.
          }
          {
            rewrite <- H5.
            trivial.
          }
        }
      }
      { (** assign -opt-> assign*)
        assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
          {
            destruct ANALYSIS as [ANALYSIS | ANALYSIS].
            eapply transf_step_psrv_loc_fact_valid; eauto.
            eapply Ave_B.wf_transf_blk_step; eauto.
            pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
            apply A in ANALYSIS.
            folds AveAI.b.
            rewrite ANALYSIS. 
            eapply top_is_loc_fact_valid.
          }
        }
        rename H into LOC_FACT_VALID.
        exists {|
            State.regs := RegFun.add r (RegFile.eval_expr expr regs_src) regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_src sc_src mem_src (ThreadEvent.silent). 
        splits; eauto. 
        { (** load/assign -> assign  *)
            eapply Thread.program_step_intro; simpls.
            eapply State.step_assign; eauto.
            rewrite <- ASSIGN; trivial.
            eapply Local.step_silent; eauto.
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            rewrite <- H5. rewrite <- H4. trivial.
          }
          {
              eapply cse_match_local_state_intro; 
              try rewrite <- H3; eauto.
              eapply cse_match_rtl_state_intro; eauto.
              simpls.
              remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
              assert (e = AveLat.opt_expr_with_ave expr ai). {
                unfolds AveLat.opt_expr_with_ave.
                subst. 
                destruct expr; rewrite GET_REG; trivial.
              }
              rename H into OPT_EXPR.
              eapply cse_match_frame_intro with(i:=i+1); eauto.
              {
                assert (RegFile.eval_expr e regs_src = RegFile.eval_expr expr regs_src). {
                  rewrite OPT_EXPR.
                  eapply eq_sym.
                  eapply match_ai_implies_opt_expr_eval_eq; eauto.
                }
                rewrite H; trivial.
              }
              {
                eapply bb_from_i_plus_one with (inst:=inst); eauto.
                subst. trivial.
              }
              rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
              { 
                destruct ANALYSIS.
                2: { (** case: analysis = top; always match_ai *)
                  pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                  eapply H7 in H.
                  folds AveAI.b.
                  rewrite H.
                  eapply always_match_top.
                }
                eapply Ave_B.wf_transf_blk_step in H; eauto.
                unfolds Ave_B.transf_step.
                rewrite EqBlkSrc in H.
                rewrite ASSIGN in H.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1))) as ai'.

                pose proof MATCH_AI as MATCH_AI'.
                unfold match_abstract_interp in MATCH_AI.
                unfold match_abstract_interp.
                unfold Ave_I.transf in H.
                rewrite <- Heqai in H.
                remember (AveLat.opt_expr_with_ave expr (AveLat.kill_reg ai r)) as opt_e.
                remember (AveLat.GetRegByExpr opt_e (AveLat.kill_reg ai r)) as GetReg.
                destruct GetReg eqn:EqGetReg.
                2: { (** r \in fv(rhs) *)
                  destruct ai eqn:EqAi.
                  { 
                    unfold AveLat.kill_reg in H. rewrite <- H. trivial.
                  }
                  {
                    unfold AveLat.kill_reg in H. rewrite <- H. 
                    intros.
                    destruct (negb (RegSet.mem r (Inst.regs_of_expr opt_e))) eqn:MEM.
                    2: {
                      contradiction.
                    }
                    intros.

                    pose proof classic (tu = (AveTuple.AExpr r opt_e)).
                    destruct H8.
                    2: {
                      eapply W.add_3 in H7.
                      2: {
                        intro.
                        rewrite H9 in H8; contradiction.
                      }
                      pose proof W.empty_1. unfolds W.Empty. 
                      specialize (H9 tu). 
                      contradiction.
                    }
                    rewrite H8.
                    unfold match_abstract_fact.
                    rewrite Loc_add_eq.
                    subst opt_e.
                    unfolds AveLat.kill_reg.
                    assert (RegFile.eval_expr (AveLat.opt_expr_with_ave expr AveLat.Undef)
                    (RegFun.add r (RegFile.eval_expr expr regs_src) regs_src) = RegFile.eval_expr (AveLat.opt_expr_with_ave expr AveLat.Undef) regs_src). {
                      eapply eq_sym.
                      eapply regs_add_nonfree_var_eq_eval_expr.
                      intro.
                      rewrite H9 in MEM. 
                      unfolds negb.
                      discriminate.
                    }
                    rewrite H9.
                    eapply match_ai_implies_opt_expr_eval_eq; eauto.
                  }
                  {
                    remember (AveLat.kill_reg (AveLat.CSet tuples) r ) as Kill.
                    destruct Kill; try discriminate; eauto.
                    destruct (negb (RegSet.mem r (Inst.regs_of_expr opt_e))) eqn:MEM.
                    2: {
                      rewrite <- H.
                      intros.
                      assert (W.In tu tuples). {
                        unfold AveLat.kill_reg in HeqKill.
                        inv HeqKill.
                        eapply W.filter_1 in H7; subst; trivial.
                        eapply AveTuple.compat_bool_freeOfReg.
                      }
                      specialize (MATCH_AI tu H8). 
                      unfolds match_abstract_fact.
                      destruct tu eqn:EqTu.
                      { (** (r, e) *)
                        assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inversion HeqKill.
                          rewrite H10 in H7.
                          unfold AveLat.kill_reg in EqKillReg.
                          inversion EqKillReg.
                          rewrite <- H11 in H7.
                          eapply W.filter_2 in H7. 
                          unfolds AveTuple.freeOfReg.
                          eapply sflib__andb_split in H7.
                          destruct H7.
                          unfolds negb.
                          destruct (reg =? r)%positive eqn:RegEq.
                          try discriminate; eauto.
                          rewrite Pos.eqb_sym in RegEq.
                          eapply Pos.eqb_neq; eauto. 
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                        }
                        inversion HeqKill.
                        rewrite H11 in H7.

                        pose proof H9.
                        eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr expr regs_src)) (regs:=regs_src) in H9.
                        folds Const.t.
                        rewrite H9. 
                        assert (~RegSet.mem r (Inst.regs_of_expr expr0)). {
                          eapply W.filter_2 in H7.
                          unfold AveTuple.freeOfReg in H7.
                          intro.
                          eapply sflib__andb_split in H7.
                          destruct H7.
                          unfolds negb.
                          des_ifH H13; try discriminate; eauto.
                          eapply (AveTuple.compat_bool_freeOfReg r).
                        }
                        eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=(RegFile.eval_expr expr regs_src)) in H12.
                        folds Const.t.
                        rewrite <- H12.
                        trivial.
                      }
                      { (** (r, x) *)
                        assert (r <> reg). {
                          destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                          {
                            subst. discriminate. 
                          }
                          {
                            subst. discriminate. 
                          }
                          {
                            inversion HeqKill.
                            rewrite H10 in H7.
                            unfold AveLat.kill_reg in EqKillReg.
                            inversion EqKillReg.
                            rewrite <- H11 in H7.
                            eapply W.filter_2 in H7. 
                            unfolds AveTuple.freeOfReg.
                            unfolds negb.
                            destruct (reg =? r)%positive eqn:RegEq.
                            try discriminate; eauto.
                            rewrite Pos.eqb_sym in RegEq.
                            eapply Pos.eqb_neq; eauto. 
                            eapply AveTuple.compat_bool_freeOfReg.
                          }
                        }
                        eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr expr regs_src)) (regs:=regs_src) in H9.
                        folds Const.t.
                        rewrite H9.
                        trivial.
                      }
                    }
                    rewrite <- H.
                    intros.
                    unfolds match_abstract_fact.
                    destruct tu eqn:EqTu.
                    { (** (r, e) *)
                      pose proof (classic (tu = AveTuple.AExpr r opt_e)).
                      destruct H8.
                      { (** (r, opt_e) *)
                        rewrite EqTu in H8.
                        inversion H8. subst expr0. subst reg.
                        rewrite Loc_add_eq.
                        subst opt_e.
                        unfolds AveLat.kill_reg.
                        assert (RegFile.eval_expr (AveLat.opt_expr_with_ave expr (AveLat.CSet tuples0))
                        (RegFun.add r (RegFile.eval_expr expr regs_src) regs_src) = RegFile.eval_expr (AveLat.opt_expr_with_ave expr (AveLat.CSet tuples0)) regs_src). {
                          eapply eq_sym.
                          eapply regs_add_nonfree_var_eq_eval_expr.
                          intro.
                          rewrite H9 in MEM. 
                          unfolds negb.
                          discriminate.
                        }
                        rewrite H9.
                        eapply match_ai_implies_opt_expr_eval_eq; eauto.
                        eapply ge_prsv_match_ai; eauto.
                        inversion HeqKill.
                        {
                          unfold AveAI.ge.
                          unfold AveDS.L.ge.
                          unfold W.Subset.
                          intros.
                          eapply W.filter_1 in H10; eauto.
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }
                      { (** old (r, e) *)
                        eapply W.add_3 in H7; eauto.
                        2: {subst; eauto. }
                        clear H8.
                        assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inversion HeqKill.
                          rewrite H9 in H7.
                          unfold AveLat.kill_reg in EqKillReg.
                          inversion EqKillReg.
                          rewrite <- H10 in H7.
                          eapply W.filter_2 in H7. 
                          unfolds AveTuple.freeOfReg.
                          eapply sflib__andb_split in H7.
                          destruct H7.
                          unfolds negb.
                          destruct (reg =? r)%positive eqn:RegEq.
                          try discriminate; eauto.
                          rewrite Pos.eqb_sym in RegEq.
                          eapply Pos.eqb_neq; eauto. 
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                        }
                        inversion HeqKill.
                        rewrite H10 in H7.

                        pose proof H8.
                        eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr expr regs_src)) (regs:=regs_src) in H8.
                        folds Const.t.
                        rewrite H8. 
                        assert (~RegSet.mem r (Inst.regs_of_expr expr0)). {
                          eapply W.filter_2 in H7.
                          unfold AveTuple.freeOfReg in H7.
                          intro.
                          eapply sflib__andb_split in H7.
                          destruct H7.
                          unfolds negb.
                          des_ifH H12; try discriminate; eauto.
                          eapply (AveTuple.compat_bool_freeOfReg r).
                        }
                        eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=(RegFile.eval_expr expr regs_src)) in H11.
                        folds Const.t.
                        rewrite <- H11.
                        trivial.
                        assert (W.In tu tuples). {
                          eapply W.filter_1 in H7; subst; trivial.
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                        specialize (MATCH_AI tu H12).
                        rewrite EqTu in MATCH_AI. trivial.
                      }
                    }
                    { (** (r, x) *)
                      assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inversion HeqKill.
                          rewrite H9 in H7.
                          unfold AveLat.kill_reg in EqKillReg.
                          inversion EqKillReg.
                          rewrite <- H10 in H7.
                          eapply W.add_3 in H7.
                          2: {intro. discriminate. }
                          eapply W.filter_2 in H7. 
                          unfolds AveTuple.freeOfReg.
                          unfolds negb.
                          destruct (reg =? r)%positive eqn:RegEq.
                          try discriminate; eauto.
                          rewrite Pos.eqb_sym in RegEq.
                          eapply Pos.eqb_neq; eauto. 
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }
                      eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr expr regs_src)) (regs:=regs_src) in H8.
                      folds Const.t.
                      rewrite H8.
                      assert (W.In tu tuples). {
                        eapply W.add_3 in H7.
                        inv HeqKill.
                        eapply W.filter_1 in H7; subst; trivial.
                        eapply AveTuple.compat_bool_freeOfReg.
                        intro; discriminate.
                      }
                      specialize (MATCH_AI tu H9). subst; trivial.                    
                    }
                  }
                }
                {
                  destruct ai eqn:EqAi.
                  { 
                    unfold AveLat.kill_reg in H. rewrite <- H. trivial.
                  }
                  {
                    unfold AveLat.kill_reg in H. rewrite <- H.
                    intros.
                    rename t into r''.
                    simpls. discriminate. 
                  }
                  {
                    unfold AveLat.kill_reg in H. rewrite <- H.
                    intros.
                    rename t into r''.
                    des_ifH H.
                    2: {
                      intros.
                      assert (W.In tu tuples). {
                        eapply W.filter_1 in H7; trivial.
                        eapply AveTuple.compat_bool_freeOfReg.
                      }
                      specialize (MATCH_AI tu H8).
                      unfolds match_abstract_fact.
                      destruct tu eqn:EqTu.
                      { (** (r, e) *)
                        assert (r <> reg). {
                          destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                          {
                            subst. discriminate. 
                          }
                          {
                            subst. discriminate. 
                          }
                          {
                            inv H.
                            eapply W.filter_2 in H7. 
                            unfolds AveTuple.freeOfReg.
                            eapply sflib__andb_split in H7.
                            destruct H7.
                            unfolds negb.
                            destruct (reg =? r)%positive eqn:RegEq.
                            try discriminate; eauto.
                            rewrite Pos.eqb_sym in RegEq.
                            eapply Pos.eqb_neq; eauto. 
                            eapply AveTuple.compat_bool_freeOfReg.
                          }
                        }

                        inv H.

                        pose proof H9.
                        eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr expr regs_src)) (regs:=regs_src) in H9.
                        folds Const.t.
                        rewrite H9. 
                        assert (~RegSet.mem r (Inst.regs_of_expr expr0)). {
                          eapply W.filter_2 in H7.
                          unfolds AveTuple.freeOfReg.
                          intro.
                          eapply sflib__andb_split in H7.
                          destruct H7.
                          unfolds negb.
                          des_ifH H1; try discriminate; eauto.
                          rewrite H0 in H2. discriminate.
                          eapply (AveTuple.compat_bool_freeOfReg r).
                        }
                        eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=(RegFile.eval_expr expr regs_src)) in H0.
                          folds Const.t.
                          rewrite <- H0.
                          trivial.
                      }
                      { (** (r, x) *)
                        assert (r <> reg). {
                          destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                          {
                            subst. discriminate. 
                          }
                          {
                            subst. discriminate. 
                          }
                          {
                            inv H.
                            eapply W.filter_2 in H7. 
                            unfolds AveTuple.freeOfReg.
                            unfolds negb.
                            destruct (reg =? r)%positive eqn:RegEq.
                            try discriminate; eauto.
                            rewrite Pos.eqb_sym in RegEq.
                            eapply Pos.eqb_neq; eauto. 
                            eapply AveTuple.compat_bool_freeOfReg.
                          }
                        }
                        eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr expr regs_src)) (regs:=regs_src) in H9.
                        folds Const.t.
                        rewrite H9.
                        trivial.
                      } 
                    }
                    intros.
                    pose proof (classic (tu = AveTuple.AExpr r'' (Inst.expr_reg r))) as IS_R_R'.
                    destruct IS_R_R' as [IS_R_R' | NOT_R_R'].
                    { (** (r', r) *)
                      rewrite IS_R_R'.
                      unfolds match_abstract_fact.
                        unfolds AveLat.GetRegByExpr.
                        pose proof Heqai'.
                        remember  (RegFile.eval_expr e regs_src) as val.
                        unfold RegFile.eval_expr. rewrite RegFun.add_spec_eq.
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn: KillReg; try discriminate.
                        remember (W.choose (W.filter (AveTuple.isSameExpr opt_e) tuples0)) as Choose.
                        destruct Choose eqn:EqChoose; try discriminate.
                        inversion H2.
                        eapply eq_sym in HeqChoose.
                        eapply W.choose_1 in HeqChoose.
                        pose proof HeqChoose.
                        eapply W.filter_1 in HeqChoose.
                        eapply W.filter_2 in H10.
                        unfold AveTuple.isSameExpr in H10.
                        destruct e0 eqn:EqE; try discriminate.
                        eapply Inst.beq_expr_eq in H10.
                        unfolds AveTuple.get_reg.
                        inversion HeqGetReg.
                        subst reg. 
                        assert (r'' <> r). {
                          eapply AveLat.mem_of_kill_reg_implies_neq with (tuples:=tuples) (r:=r)in KillReg; eauto.
                          unfolds AveTuple.get_reg. trivial.
                        }
                        subst val.
                        inv STATE; try discriminate.
                        rewrite Loc_add_neq; eauto.
                        assert (regs_src r'' = RegFile.eval_expr expr regs_src). {
                          clear - MATCH_AI' MATCH_AI HeqChoose KillReg.
                          remember ((AveLat.opt_expr_with_ave expr (AveLat.CSet tuples0))) as opt_e.
                          remember (AveTuple.AExpr r'' opt_e) as tu.
                          unfolds AveLat.kill_reg. inversion KillReg.
                          rewrite <- H0 in HeqChoose.
                          eapply W.filter_1 in HeqChoose.
                          specialize (MATCH_AI tu HeqChoose).
                          rewrite Heqtu in MATCH_AI.
                          rewrite MATCH_AI.
                          eapply eq_sym.
                          subst opt_e.
                          eapply match_ai_implies_opt_expr_eval_eq; eauto.
                          eapply ge_prsv_match_ai; eauto.
                          { 
                            unfold AveAI.ge.
                            unfold AveDS.L.ge.
                            unfold W.Subset.
                            intros.
                            rewrite <- H0 in H.
                            eapply W.filter_1 in H; eauto.
                            eapply AveTuple.compat_bool_freeOfReg.
                          }
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                        trivial.
                        eapply AveTuple.compat_bool_isSameExpr.
                        eapply AveTuple.compat_bool_isSameExpr.
                    }
                    (** old tu *)
                    assert (W.In tu tuples). {
                      eapply W.add_3 in H7.
                      eapply W.filter_1 in H7; trivial.
                      eapply AveTuple.compat_bool_freeOfReg.
                      intro. rewrite H8 in NOT_R_R'. contradiction.
                    }
                    specialize (MATCH_AI tu H8).
                    unfolds match_abstract_fact.
                    destruct tu eqn:EqTu.
                    { (** (r, e) *)
                      assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inv H.
                          eapply W.add_3 in H7.
                          2: {
                            intro. 
                            rewrite H in NOT_R_R'.
                            contradiction.
                          }
                          eapply W.filter_2 in H7. 
                          unfolds AveTuple.freeOfReg.
                          eapply sflib__andb_split in H7.
                          destruct H7.
                          unfolds negb.
                          destruct (reg =? r)%positive eqn:RegEq.
                          try discriminate; eauto.
                          rewrite Pos.eqb_sym in RegEq.
                          eapply Pos.eqb_neq; eauto. 
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }
                      inv H.
                      eapply W.add_3 in H7; eauto.
                      pose proof H9.
                      eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr expr regs_src)) (regs:=regs_src) in H9.
                      folds Const.t.
                      rewrite H9. 
                      assert (~RegSet.mem r (Inst.regs_of_expr expr0)). {
                        eapply W.filter_2 in H7.
                        unfolds AveTuple.freeOfReg.
                        intro.
                        eapply sflib__andb_split in H7.
                        destruct H7.
                        unfolds negb.
                        des_ifH H1; try discriminate; eauto.
                        rewrite H0 in H2. discriminate.
                        eapply (AveTuple.compat_bool_freeOfReg r).
                      }
                      eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=(RegFile.eval_expr expr regs_src)) in H0.
                        folds Const.t.
                        rewrite <- H0.
                        trivial.
                    }
                    { (** (r, x) *)
                      assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inv H.
                          eapply W.add_3 in H7.
                          2: {
                            intro. 
                            rewrite H in NOT_R_R'.
                            contradiction.
                          }
                          eapply W.filter_2 in H7. 
                          unfolds AveTuple.freeOfReg.
                          unfolds negb.
                          destruct (reg =? r)%positive eqn:RegEq.
                          try discriminate; eauto.
                          rewrite Pos.eqb_sym in RegEq.
                          eapply Pos.eqb_neq; eauto. 
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }
                      eapply regs_add_neg with (r:=r) (v:=(RegFile.eval_expr expr regs_src)) (regs:=regs_src) in H9.
                      folds Const.t.
                      rewrite H9.
                      trivial.
                    } 
                  }
                }
              }
              { 
                eapply subblk_same_succ in EqBlkSrc.
                rewrite <- EqBlkSrc; trivial.
                destruct ANALYSIS.
                2: {
                  intros.
                  eapply (AveAI.get_head_from_eval) with (l:=lp) in H; eauto.
                  folds AveAI.b.
                  rewrite H.
                  eapply AveLat.ge_top.
                }
                eapply Ave_B.wf_transf_blk_getlast in H; eauto.
                rewrite <- H. trivial.
              }
              
          }
          {
            right. 
            splits; trivial.
            destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
            apply eq_inj_implies_incr; trivial.
            trivial.
          }
          {
            rewrite <- H3; rewrite <- H5.
            trivial.
          }
          {
            rewrite <- H4; rewrite <- H5. 
            trivial.
          }
          {
            rewrite <- H5.
            trivial.
          }
        }
      }
  - (** call *)
    (** call is init match state + jmp*)
    remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
    remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
    eapply eq_sym in Heqblk_tgt.
    rewrite BLK0 in Heqblk_tgt.
    pose proof Heqblk_tgt as TRSF.
    eapply call_transformed_by_call in Heqblk_tgt.
    pose proof STACK as STACK'.
    pose proof ENTRY_BLK as ENTRY_BLK'.
    (** code_src' ! f = Some (cdhp_src', f0) *)
    assert (exists cdhp_src', code_src ! f = Some (cdhp_src', f0)). {
      unfold cse_optimizer in OPT. inversion OPT. 
      rewrite <- H0 in FIND_FUNC.
      unfolds transform_prog.
      rewrite PTree.gmap in FIND_FUNC.
      unfolds Coqlib.option_map.

      destruct (code_src ! f) eqn:CodeSFunc; try discriminate.
      inv FIND_FUNC.

      unfold transform_func in H1.
      destruct f1 eqn:EqF1.
      destruct ((AveDS.analyze_program code_src succ AveLat.top Ave_B.transf_blk) ! f) eqn:Eq.
      { 
        inv H1. eexists; eauto.
      }
      { 
        inv H1. eexists; eauto.
      }
    }
    destruct H as (cdhp_src' & CDHP_SRC').
    pose proof CDHP_SRC' as CDHP_SRC''.
    pose proof (AveDS.wf_analyze_func code_src f cdhp_src' f0 (AveLat.top) Ave_B.transf_blk) as G.
    apply G in CDHP_SRC''.
    destruct CDHP_SRC'' as (acdhp & ACDHP).
    assert (
          transform_cdhp cdhp_src' acdhp = cdhp_tgt'
          ). 
    {
      clear G.
      unfold cse_optimizer in OPT. inversion OPT. 
      unfolds transform_prog.
      subst.
      rewrite PTree.gmap in FIND_FUNC.
      unfolds Coqlib.option_map.
      destruct (code_src ! f) eqn:CodeSFunc; try discriminate.
      inv FIND_FUNC.
      unfold transform_func in H0. inv CDHP_SRC'. rewrite ACDHP in H0. inv H0. trivial. 
    }
    rename H into TSF_CDHP'.
    pose proof ACDHP as H.
    eapply cse_wf_transform_cdhp_reverse with (cdhp_src := cdhp_src') in ENTRY_BLK; eauto.
    eapply cse_wf_transform_cdhp_reverse in STACK; eauto.
    destruct ENTRY_BLK as (b_src_entry, ENTRY_BLK).
    destruct STACK as (b_src', CDHP_SRC).
      exists {|
          State.regs := RegFile.init;
          State.blk := b_src_entry;
          State.cdhp := cdhp_src';
          State.cont := Continuation.stack regs_src b_src' cdhp_src cont_src;
          State.code := code_src
        |} lc_src sc_src mem_src (ThreadEvent.silent).
      splits; eauto.
      { (** call -> call  *)
          eapply Thread.program_step_intro; simpls; eauto.
          eapply State.step_call with (f0:=f0); eauto.
      }
      { (** match state *)
        inversion LOCAL.
        eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
        { (** invariant *)
          rewrite <- H5. rewrite <- H6. trivial.
        }
        {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            eapply cse_match_rtl_state_intro; eauto.
            simpls. 
            eapply cse_match_frame_intro with (i:=0) (l:=f0) (enode:=f0) (analysis:=acdhp);  eauto.
            { 
              pose proof TSF_CDHP'.
              unfold AveDS.analyze_program in H.
              rewrite PTree.gmap1 in H.
              unfolds Coqlib.option_map.
              rewrite CDHP_SRC' in H. simpls.
              inversion H. 
              remember (AveDS.fixpoint_blk cdhp_src' succ f0 AveLat.top
                  (fun (n : positive) (ai : AveDS.AI.t) =>
                  match cdhp_src' ! n with
                  | Some b => Ave_B.transf_blk ai b
                  | None => AveDS.AI.Atom ai
                  end)) as acdhp_partial.
              destruct acdhp_partial eqn:acdhp_partial_eq.
               - left.  trivial.
               - right. trivial.  
            }
            { (** prove transform_blk *)
              unfold AveAI.br_from_i; simpls.
              unfold transform_cdhp in TSF_CDHP'.
              rewrite <- TSF_CDHP' in ENTRY_BLK'.
              rewrite PTree.gmap in ENTRY_BLK'; unfolds Coqlib.option_map; simpls.
              rewrite ENTRY_BLK in ENTRY_BLK'. 
              inv ENTRY_BLK'. 
              unfold transform_blk'. 
              trivial. 
            }
            {
              unfolds match_abstract_interp; unfolds AveAI.br_from_i; simpls.
              assert (AveAI.ge (AveAI.getFirst (acdhp !! f0)) AveLat.top).
              {
                eapply AveDS.analyze_func_entry; eauto.
                eapply Ave_B.wf_transf_blk.
              }
              remember (AveAI.getFirst acdhp!!f0) as aentry.
              - destruct aentry; eauto. 
                simpls.
                intros.
                pose proof W.empty_1. unfolds W.Empty. unfolds W.Subset.
                eapply H0 in H8. 
                pose proof (H9 tu). contradiction.
            }
            {
              unfold AveAI.br_from_i; simpls.
              intros.
              eapply AveDS.analyze_func_solution; eauto.
              eapply Ave_B.wf_transf_blk.
              eapply Ave_B.wf_transf_blk2.
            }
            {
              {
                unfolds AveAI.br_from_i; simpls.
                assert (AveAI.ge (AveAI.getFirst (acdhp !! f0)) AveLat.top).
                {
                  eapply AveDS.analyze_func_entry; eauto.
                  eapply Ave_B.wf_transf_blk.
                }
                unfold AveAI.ge in H0. unfold AveDS.L.ge in H0.
                destruct (AveAI.getFirst acdhp !! f0) eqn:EqEntry; unfolds AveLat.top; try contradiction; eauto.
                assert (W.Empty tuples). {
                  unfolds W.Subset.
                  pose proof (classic (exists a, W.In a tuples)). destruct H8; trivial.
                  2: {
                    unfold W.Empty.
                    eapply not_ex_all_not. trivial.
                  }
                  destruct H8.
                  specialize (H0 x H8).
                  pose proof W.empty_1. unfolds W.Empty. 
                  specialize (H9 x). contradiction.
                }
                unfolds loc_fact_valid.
                intros. 
                unfolds W.Empty. 
                specialize (H8 (AveTuple.AVar r loc)). 
                contradiction.
              }
            }
            { (** match_cont *)
              simpls.
              eapply cse_match_cont_step; eauto.
              intros.
              eapply cse_match_frame_intro with (i:=0); eauto.
              {
                unfold transform_cdhp in Heqcdhp_tgt.
                rewrite Heqcdhp_tgt in STACK'.
                rewrite PTree.gmap in STACK'. unfolds option_map. rewrite CDHP_SRC in STACK'. inv STACK'; trivial.
              }
              { 
                pose proof (FIXPOINT fret).
                assert (In fret (succ blk_src)). {
                  unfold succ.
                  unfold BBlock.get_out_fids.
                  rewrite Heqblk_tgt.
                  unfold In. left; trivial.
                }
                apply H0 in H8.
                unfold AveAI.br_from_i. unfold AveAI.br_from_i_opt.
                destruct ANALYSIS. 
                2: {
                  rewrite H9.
                  unfold "!!".
                  simpls.
                  rewrite PTree.gempty.
                  unfolds AveAI.getFirst. 
                  eapply always_match_top.
                }
                pose proof H9 as TRSF_BLK.
                eapply Ave_B.wf_transf_blk_step with (blk:=blk) (i:=i) (blk_part := blk_src) in H9; eauto.
                rename Heqblk_tgt into BLK_SRC.
                rewrite BLK_SRC in H9.
                unfold Ave_B.transf_step in H9.
                (** 
                  1. getFirst from i+1 <-> getLast
                  2. MATCH_AI + AI.ge => MATCH_AI
                *)
                assert (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)) =  (AveAI.getLast (AveAI.br_from_i analysis !! l i))).
                {
                  eapply get_last_ablk; eauto.
                  intros. 
                  rewrite BLK_SRC. 
                  intro.
                  discriminate.
                }
                rewrite <- H10 in H8.
                rewrite <- H9 in H8.
                clear - MATCH_AI H8 H9 H10.
                assert (AveAI.ge (AveLat.GetExprs (AveAI.getFirst (AveAI.br_from_i analysis !! l i))) (AveAI.getFirst (AveAI.br_from_i analysis !! l i))). {
                  eapply AveLat.get_exprs_implies_ge; eauto.
                }
                assert (match_abstract_interp regs_src (Local.tview lc_src) mem_src
                  (AveAI.getFirst analysis !! fret) lo). {
                    eapply AveLat.ge_trans in H; eauto. 
                    eapply ge_prsv_match_ai; eauto.
                }
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                assert (exists tuples, ai = AveLat.CSet tuples). {
                  destruct ai eqn:EqAi.
                  eapply never_match_bot in MATCH_AI; contradiction.
                  eapply never_match_undef in MATCH_AI; contradiction.
                  eexists; eauto.
                }
                eapply generalize_no_expr_match_ai; eauto.
            }
            {
              intros.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H0; eauto.
                folds AveAI.b.
                rewrite H0.
                eapply AveLat.ge_top.
              }
              unfolds AveAI.br_from_i; simpls.
              eapply AveDS.analyze_func_solution' with (fentry_s:=enode) (eval := AveLat.top) (transf_blk := Ave_B.transf_blk); eauto.
              eapply Ave_B.wf_transf_blk.
            }
            {
              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                {
                  destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                  eapply transf_step_psrv_loc_fact_valid; eauto.
                  eapply Ave_B.wf_transf_blk_step; eauto.
                  pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                  apply A in ANALYSIS.
                  folds AveAI.b.
                  rewrite ANALYSIS. 
                  eapply top_is_loc_fact_valid.
                }
              }
              rename H0 into LOC_FACT_VALID.

              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! fret (0)))).  {
                destruct ANALYSIS.
                2: {
                  intros.
                  eapply (AveAI.get_head_from_eval) with (l:=fret) in H0; eauto.
                  folds AveAI.b.
                  unfolds AveAI.br_from_i; simpls.
                  rewrite H0.
                  eapply top_is_loc_fact_valid.
                }
                assert (AveAI.ge (AveAI.getFirst (AveAI.br_from_i analysis !! fret (0))) (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))). {
                  pose proof (FIXPOINT fret).
                  assert (In fret (succ blk_src)). {
                    unfold succ.
                    unfold BBlock.get_out_fids.
                    rewrite Heqblk_tgt.
                    unfold In. left; trivial.
                  }
                  eapply H8 in H9.
                  assert (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)) =  (AveAI.getLast (AveAI.br_from_i analysis !! l i))).
                  {
                    eapply get_last_ablk; eauto.
                    intros.
                    subst blk_src. 
                    intro.
                    discriminate.
                  }
                  rewrite <- H10 in H9.
                  trivial.
                }
                eapply ge_prsv_loc_fact_valid; eauto. 
              }
              trivial.
            }
          }
          {
            subst; trivial.
          }
          {
            subst; trivial.
          }
          {
            subst; trivial.
          }
        }
        {
          right. 
          splits; trivial.
          destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
          apply eq_inj_implies_incr; trivial.
          trivial.
        }
        {
          subst; trivial.
        }
        {
          subst; trivial.
        }
        {
          subst; trivial.
        }
      } 
  - (** ret *) 
    remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
    remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
    eapply eq_sym in Heqblk_tgt.
    rewrite BLK0 in Heqblk_tgt.
    pose proof Heqblk_tgt as TRSF.
    eapply ret_transformed_by_ret in Heqblk_tgt.

    inversion MATCH_CONT.
    {
      destruct DONE; try discriminate.
    }
      exists {|
          State.regs := regs_s;
          State.blk := blk_s;
          State.cdhp := cdhp_s;
          State.cont := cont_src';
          State.code := code_src
        |} lc_src sc_src mem_src (ThreadEvent.silent).
      splits; eauto.
      { (** ret -> ret  *)
          eapply Thread.program_step_intro; simpls; eauto.
          eapply State.step_ret; eauto.
      }
      { (** match state *)
        inversion LOCAL.
        eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
        { (** invariant *)
          rewrite <- H5. rewrite <- H4. trivial.
        }
        {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            pose proof (FRAME_MATCH (Local.tview lc_src) mem_src).
            rewrite BLK0 in STATE.
            inv STATE; try discriminate; eauto. 
            inv CONT_T.
            trivial.
            { (** match_cont *)
              simpls.
              inv CONT_T.
              trivial.
            }
        }
        {
          right. 
          splits; trivial.
          destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
          apply eq_inj_implies_incr; trivial.
          trivial.
        }
        {
          rewrite <- H3; rewrite <- H5.
          trivial.
        }
        {
          rewrite <- H4; rewrite <- H5. 
          trivial.
        }
        {
          rewrite <- H5.
          trivial.
        }
      } 
  - (** jmp *)
    remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
    remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
    eapply eq_sym in Heqblk_tgt.
    rewrite BLK0 in Heqblk_tgt.
    pose proof Heqblk_tgt as TRSF.
    eapply jmp_transformed_by_jmp in Heqblk_tgt.
    pose proof TGT as TGT'.
    eapply cse_wf_transform_cdhp_reverse in TGT; eauto.
    destruct TGT as (b_src', CDHP_SRC).
      exists {|
          State.regs := regs_tgt';
          State.blk := b_src';
          State.cdhp := cdhp_src;
          State.cont := cont_src;
          State.code := code_src
        |} lc_src sc_src mem_src (ThreadEvent.silent).
      splits; eauto.
      { (** jmp -> jmp  *)
          eapply Thread.program_step_intro; simpls; eauto.
          eapply State.step_jmp; eauto.
      }
      { (** match state *)
        inversion LOCAL.
        eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
        { (** invariant *)
          rewrite <- H5. rewrite <- H4. trivial.
        }
        {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=0); eauto.
            { 
              clear - Heqcdhp_tgt TGT' CDHP_SRC.
              unfold transform_cdhp in Heqcdhp_tgt.
              rewrite Heqcdhp_tgt in TGT'.
              rewrite PTree.gmap in TGT'. unfolds option_map. rewrite CDHP_SRC in TGT'. inv TGT'; trivial.
            }
            { 
              pose proof (FIXPOINT f).
              assert (In f (succ blk_src)). {
                unfold succ.
                unfold BBlock.get_out_fids.
                rewrite Heqblk_tgt.
                unfold In. left; trivial.
              }
              apply H in H7.
              unfold AveAI.br_from_i. unfold AveAI.br_from_i_opt.
              destruct ANALYSIS. 
              2: {
                rewrite H8.
                unfold "!!".
                simpls.
                rewrite PTree.gempty.
                unfolds AveAI.getFirst. 
                eapply always_match_top.
              }
              pose proof H8 as TRSF_BLK.
              eapply Ave_B.wf_transf_blk_step with (blk:=blk) (i:=i) (blk_part := blk_src) in H8; eauto.
              rename Heqblk_tgt into BLK_SRC.
              rewrite BLK_SRC in H8.
              unfold Ave_B.transf_step in H8.
              (** 
                1. getFirst from i+1 <-> getLast
                2. MATCH_AI + AI.ge => MATCH_AI
              *)
              assert (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)) =  (AveAI.getLast (AveAI.br_from_i analysis !! l i))).
              {
                eapply get_last_ablk; eauto.
                intros. 
                rewrite BLK_SRC. 
                intro.
                discriminate.
              }
              rewrite <- H9 in H7.
              rewrite <- H8 in H7.
              clear - MATCH_AI H7.
              eapply ge_prsv_match_ai; eauto. 
            }
            {
              intros.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H; eauto.
                folds AveAI.b.
                rewrite H.
                eapply AveLat.ge_top.
              }
              unfolds AveAI.br_from_i; simpls.
              eapply AveDS.analyze_func_solution' with (fentry_s:=enode) (eval := AveLat.top) (transf_blk := Ave_B.transf_blk); eauto.
              eapply Ave_B.wf_transf_blk.
            }
            {
              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! f (0)))).  {
                destruct ANALYSIS.
                2: {
                  intros.
                  eapply (AveAI.get_head_from_eval) with (l:=f) in H; eauto.
                  folds AveAI.b.
                  unfolds AveAI.br_from_i; simpls.
                  rewrite H.
                  eapply top_is_loc_fact_valid.
                }
                assert (AveAI.ge (AveAI.getFirst (AveAI.br_from_i analysis !! f (0))) (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))). {
                  pose proof (FIXPOINT f).
                  assert (In f (succ blk_src)). {
                    unfold succ.
                    unfold BBlock.get_out_fids.
                    rewrite Heqblk_tgt.
                    unfold In. left; trivial.
                  }
                  eapply H7 in H8.
                  assert (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)) =  (AveAI.getLast (AveAI.br_from_i analysis !! l i))).
                  {
                    eapply get_last_ablk; eauto.
                    intros.
                    subst blk_src. 
                    intro.
                    discriminate.
                  }
                  rewrite <- H9 in H8.
                  trivial.
                }
                eapply Ave_B.wf_transf_blk_step with (blk:=blk) (i:=i) (blk_part := blk_src) in H; eauto.
                rename Heqblk_tgt into BLK_SRC.
                rewrite BLK_SRC in H.
                unfold Ave_B.transf_step in H.
                rewrite <- H in H7.
                eapply ge_prsv_loc_fact_valid; eauto. 
              }
              trivial.
            }
        }
        {
          right. 
          splits; trivial.
          destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
          apply eq_inj_implies_incr; trivial.
          trivial.
        }
        {
          rewrite <- H3; rewrite <- H5.
          trivial.
        }
        {
          rewrite <- H4; rewrite <- H5. 
          trivial.
        }
        {
          rewrite <- H5.
          trivial.
        }
      } 
  - (** be *)
    remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
    remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
    eapply eq_sym in Heqblk_tgt.
    rewrite BLK0 in Heqblk_tgt.

    eapply be_transformed_by_be in Heqblk_tgt.
    destruct BRANCH as [(TGT & COND) | (TGT & COND)].
    {
      pose proof TGT as TGT'.
      eapply cse_wf_transform_cdhp_reverse in TGT; eauto.
      destruct TGT as (b_src', CDHP_SRC).
        exists {|
            State.regs := regs_tgt';
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_src sc_src mem_src (ThreadEvent.silent).
        splits; eauto.
        { (** skip -> skip  *)
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_be; eauto.
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            rewrite <- H5. rewrite <- H4. trivial.
          }
          {
              eapply cse_match_local_state_intro; 
              try rewrite <- H3; eauto.
              eapply cse_match_rtl_state_intro; eauto.
              simpls.
              eapply cse_match_frame_intro with(i:=0); eauto.
              { 
              clear - Heqcdhp_tgt TGT' CDHP_SRC.
              unfold transform_cdhp in Heqcdhp_tgt.
              rewrite Heqcdhp_tgt in TGT'.
              rewrite PTree.gmap in TGT'. unfolds option_map. rewrite CDHP_SRC in TGT'. inv TGT'; trivial.
            }
            {
              pose proof (FIXPOINT f1).
              assert (In f1 (succ blk_src)). {
                unfold succ.
                unfold BBlock.get_out_fids.
                rewrite Heqblk_tgt.
                unfold In. left; trivial.
              }
              apply H in H7.
              unfold AveAI.br_from_i. unfold AveAI.br_from_i_opt.
              destruct ANALYSIS. 
              2: {
                rewrite H8.
                unfold "!!".
                simpls.
                rewrite PTree.gempty.
                unfolds AveAI.getFirst. 
                eapply always_match_top.
              }
              pose proof H8 as TRSF_BLK.
              eapply Ave_B.wf_transf_blk_step with (blk:=blk) (i:=i) (blk_part := blk_src) in H8; eauto.
              rename Heqblk_tgt into BLK_SRC.
              rewrite BLK_SRC in H8.
              unfold Ave_B.transf_step in H8.
              (** 
                1. getFirst from i+1 <-> getLast
                2. MATCH_AI + AI.ge => MATCH_AI
              *)
              assert (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)) =  (AveAI.getLast (AveAI.br_from_i analysis !! l i))).
              {
                eapply get_last_ablk; eauto.
                intros. 
                rewrite BLK_SRC. 
                intro.
                discriminate.
              }
              rewrite <- H9 in H7.
              rewrite <- H8 in H7.
              clear - MATCH_AI H7.
              eapply ge_prsv_match_ai; eauto. 
            }
            {
              intros.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H; eauto.
                folds AveAI.b.
                rewrite H.
                eapply AveLat.ge_top.
              }
              unfolds AveAI.br_from_i; simpls.
              eapply AveDS.analyze_func_solution' with (fentry_s:=enode) (eval := AveLat.top) (transf_blk := Ave_B.transf_blk); eauto.
              eapply Ave_B.wf_transf_blk.
            }
            {
              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! f1 (0)))).  {
                destruct ANALYSIS.
                2: {
                  intros.
                  eapply (AveAI.get_head_from_eval) with (l:=f1) in H; eauto.
                  folds AveAI.b.
                  unfolds AveAI.br_from_i; simpls.
                  rewrite H.
                  eapply top_is_loc_fact_valid.
                }
                assert (AveAI.ge (AveAI.getFirst (AveAI.br_from_i analysis !! f1 (0))) (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))). {
                  pose proof (FIXPOINT f1).
                  assert (In f1 (succ blk_src)). {
                    unfold succ.
                    unfold BBlock.get_out_fids.
                    rewrite Heqblk_tgt.
                    unfold In. left; trivial.
                  }
                  eapply H7 in H8.
                  assert (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)) =  (AveAI.getLast (AveAI.br_from_i analysis !! l i))).
                  {
                    eapply get_last_ablk; eauto.
                    intros.
                    subst blk_src. 
                    intro.
                    discriminate.
                  }
                  rewrite <- H9 in H8.
                  trivial.
                }
                eapply Ave_B.wf_transf_blk_step with (blk:=blk) (i:=i) (blk_part := blk_src) in H; eauto.
                rename Heqblk_tgt into BLK_SRC.
                rewrite BLK_SRC in H.
                unfold Ave_B.transf_step in H.
                rewrite <- H in H7.
                eapply ge_prsv_loc_fact_valid; eauto. 
              }
              trivial.
            }
          }
          {
            right. 
            splits; trivial.
            destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
            apply eq_inj_implies_incr; trivial.
            trivial.
          }
          {
            rewrite <- H3; rewrite <- H5.
            trivial.
          }
          {
            rewrite <- H4; rewrite <- H5. 
            trivial.
          }
          {
            rewrite <- H5.
            trivial.
          }
        } 
    }
    { (** fixme: equal proof *)
      pose proof TGT as TGT'.
      eapply cse_wf_transform_cdhp_reverse in TGT; eauto.
      destruct TGT as (b_src', CDHP_SRC).
        exists {|
            State.regs := regs_tgt';
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_src sc_src mem_src (ThreadEvent.silent).
        splits; eauto.
        { (** skip -> skip  *)
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_be; eauto.
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            rewrite <- H5. rewrite <- H4. trivial.
          }
          {
              eapply cse_match_local_state_intro; 
              try rewrite <- H3; eauto.
              eapply cse_match_rtl_state_intro; eauto.
              simpls.
              eapply cse_match_frame_intro with(i:=0); eauto.
              { 
              clear - Heqcdhp_tgt TGT' CDHP_SRC.
              unfold transform_cdhp in Heqcdhp_tgt.
              rewrite Heqcdhp_tgt in TGT'.
              rewrite PTree.gmap in TGT'. unfolds option_map. rewrite CDHP_SRC in TGT'. inv TGT'; trivial.
            }
            {
              pose proof (FIXPOINT f2).
              assert (In f2 (succ blk_src)). {
                unfold succ.
                unfold BBlock.get_out_fids.
                rewrite Heqblk_tgt.
                unfold In. right; left; trivial.
              }
              apply H in H7.
              unfold AveAI.br_from_i. unfold AveAI.br_from_i_opt.
              destruct ANALYSIS. 
              2: {
                rewrite H8.
                unfold "!!".
                simpls.
                rewrite PTree.gempty.
                unfolds AveAI.getFirst. 
                eapply always_match_top.
              }
              pose proof H8 as TRSF_BLK.
              eapply Ave_B.wf_transf_blk_step with (blk:=blk) (i:=i) (blk_part := blk_src) in H8; eauto.
              rename Heqblk_tgt into BLK_SRC.
              rewrite BLK_SRC in H8.
              unfold Ave_B.transf_step in H8.
              (** 
                1. getFirst from i+1 <-> getLast
                2. MATCH_AI + AI.ge => MATCH_AI
              *)
              assert (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)) =  (AveAI.getLast (AveAI.br_from_i analysis !! l i))).
              {
                eapply get_last_ablk; eauto.
                intros. 
                rewrite BLK_SRC. 
                intro.
                discriminate.
              }
              rewrite <- H9 in H7.
              rewrite <- H8 in H7.
              clear - MATCH_AI H7.
              eapply ge_prsv_match_ai; eauto. 
            }
            {
              intros.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H; eauto.
                folds AveAI.b.
                rewrite H.
                eapply AveLat.ge_top.
              }
              unfolds AveAI.br_from_i; simpls.
              eapply AveDS.analyze_func_solution' with (fentry_s:=enode) (eval := AveLat.top) (transf_blk := Ave_B.transf_blk); eauto.
              eapply Ave_B.wf_transf_blk.
            }
            {
              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! f2 (0)))).  {
                destruct ANALYSIS.
                2: {
                  intros.
                  eapply (AveAI.get_head_from_eval) with (l:=f2) in H; eauto.
                  folds AveAI.b.
                  unfolds AveAI.br_from_i; simpls.
                  rewrite H.
                  eapply top_is_loc_fact_valid.
                }
                assert (AveAI.ge (AveAI.getFirst (AveAI.br_from_i analysis !! f2 (0))) (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))). {
                  pose proof (FIXPOINT f2).
                  assert (In f2 (succ blk_src)). {
                    unfold succ.
                    unfold BBlock.get_out_fids.
                    rewrite Heqblk_tgt.
                    unfold In. right; left; trivial.
                  }
                  eapply H7 in H8.
                  assert (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)) =  (AveAI.getLast (AveAI.br_from_i analysis !! l i))).
                  {
                    eapply get_last_ablk; eauto.
                    intros.
                    subst blk_src. 
                    intro.
                    discriminate.
                  }
                  rewrite <- H9 in H8.
                  trivial.
                }
                eapply Ave_B.wf_transf_blk_step with (blk:=blk) (i:=i) (blk_part := blk_src) in H; eauto.
                rename Heqblk_tgt into BLK_SRC.
                rewrite BLK_SRC in H.
                unfold Ave_B.transf_step in H.
                rewrite <- H in H7.
                eapply ge_prsv_loc_fact_valid; eauto. 
              }
              trivial.
            }
          }
          {
            right. 
            splits; trivial.
            destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
            apply eq_inj_implies_incr; trivial.
            trivial.
          }
          {
            rewrite <- H3; rewrite <- H5.
            trivial.
          }
          {
            rewrite <- H4; rewrite <- H5. 
            trivial.
          }
          {
            rewrite <- H5.
            trivial.
          }
        } 
    }
Qed.

(** Correctness of non-atomic memory access: na read & na write*)
Theorem cse_match_state_preserving_na_access:
  forall te lo inj st_tgt st_src sc_tgt lc_src lc_tgt mem_tgt sc_src mem_src b st_tgt' lc_tgt' sc_tgt' mem_tgt', 
    Thread.program_step te lo 
        (@Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) 
        (@Thread.mk rtl_lang st_tgt' lc_tgt' sc_tgt' mem_tgt') 
    -> 
    ThreadEvent.is_na_access te 
    ->   
    (cse_match_state inj lo 
      (Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) 
      (Thread.mk rtl_lang st_src lc_src sc_src mem_src) b)
    -> 
      (exists st_src' lc_src' sc_src' mem_src',
          Thread.program_step te lo (@Thread.mk rtl_lang st_src lc_src sc_src mem_src) 
                                    (@Thread.mk rtl_lang st_src' lc_src' sc_src' mem_src') 
          /\
          (cse_match_state inj lo 
          (Thread.mk rtl_lang st_tgt' lc_tgt' sc_tgt' mem_tgt') (Thread.mk rtl_lang st_src' lc_src' sc_src' mem_src') false)
      ).
Proof.
  intros.
  destruct st_tgt as (regs_tgt, blk_tgt, cdhp_tgt, cont_tgt, code_tgt) eqn:EqStTgt.
  destruct st_tgt' as (regs_tgt', blk_tgt', cdhp_tgt', cont_tgt', code_tgt') eqn:EqStTgt'.
  destruct st_src as (regs_src, blk_src, cdhp_src, cont_src, code_src) eqn:EqStSrc; simpls.
  unfold ThreadEvent.is_na_access in H0.
  destruct te; try contradiction; eauto.
  { (** read *)
    pose proof (nonatomic_or_atomic ord) as ORD; 
    destruct ORD. 
    2:{destruct ord; subst; try contradiction. }
    rewrite H2 in H0; try contradiction; eauto.
    inversion H. unfolds ThreadEvent.get_program_event.
    inv STATE.
    { (** non-atomic read: Inst.load r loc ord *)
      inversion H1; simpls.
      inversion INVARIANT. 
      inversion MATCH_LOCAL.
      inversion MATCH_RTL_STATE; simpls.
      rename H2 into SC_EQ_START.
      destruct H3 as (MEM_EQ_START & INJ_MAP_MEM_TGT).

      inversion MATCH_FRAME; simpls.

      remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
      remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
      eapply transform_blk_induction' in TRANSF_BLK; eauto.
      destruct TRANSF_BLK as (inst & b_src' & EqBlkSrc & TRSF).
      destruct TRSF as (TRSF_INST & TRSF_BLK).
      *              
          exists {|
            State.regs :=  RegFun.add r val regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_tgt' sc_tgt' mem_tgt'.
        splits; eauto.
        { (** load -> load  *)
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_load; eauto.
            eapply load_transformed_inst_by_load in TRSF_INST; eauto.
            rewrite <- TRSF_INST; trivial.
            inversion LOCAL.
            rewrite <- H12; rewrite MEM_EQ_START.  
            rewrite <- H11.
            rewrite SC_EQ_START.
            eapply Local.step_read; eauto.
            rewrite <- H12 in LOCAL0; rewrite MEM_EQ_START in LOCAL0. 
            assert (lc_tgt = lc_src). {
              eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
            }
            rewrite <- H14. 
            trivial. 
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            rewrite <- H12.
            unfold cse_invariant; simpls. splits; eauto.
          }
          {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            2: {eapply eq_refl. }
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            {
              rewrite <- TRANSL_CDHP in Heqcdhp_tgt. trivial.
            }
            { rewrite REG_EQ. trivial. }
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            {
                rewrite <- AveAI.get_tail_from_i_eq_i_plus_one; 
                rewrite AI_BLK; trivial. 
            }
            rewrite <- AI_BLK in TRSF_BLK.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { (** match ai *)
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                eapply H15 in H14.
                folds AveAI.b.
                rewrite H14.
                eapply always_match_top.
              }
              eapply Ave_B.wf_transf_blk_step in H14; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H14.
              pose proof TRSF_INST as TRSF_INST'.
              eapply load_transformed_inst_by_load in TRSF_INST; eauto.
              rewrite TRSF_INST in H14.
              unfolds Ave_I.transf.
              destruct ord eqn:EqOrd; try discriminate; eauto.
                rewrite <- H14.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.GetRegByLoc loc (AveLat.kill_reg ai r)) as ai'.
                destruct ai eqn:EqAi.
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                }
                {
                  unfolds AveLat.kill_reg.
                  unfolds AveLat.GetRegByLoc.
                  rewrite Heqai'.
                  rewrite Heqai' in H14.
                  intros.
                  assert (tu = (AveTuple.AVar r loc)). {
                    eapply W.singleton_1 in H2. subst; trivial.
                  }
                  unfold match_abstract_fact. rewrite H3. 
                  splits; eauto.
                  {
                    subst.
                    inv LOCAL0; simpls.
                    unfolds Ordering.mem_ord_match. 
                    destruct (lo loc) eqn:EqLo.
                    destruct LO as [A|[A|A]]; try discriminate.
                    trivial.
                  }
                  {
                    subst.
                    inv LOCAL0; simpls.
                    rewrite MEM_EQ_START in GET.
                    exists ts from released. 
                    splits; eauto.
                    3: {
                      pose proof RegFun.add_spec_eq.
                      unfold RegFun.find in *.
                      rewrite H3. trivial.
                    }
                    { (** pln view *)
                      inv READABLE.
                      replace (Ordering.le Ordering.acqrel Ordering.plain) with false; trivial.
                      replace (Ordering.le Ordering.relaxed Ordering.plain) with false; trivial.
                      unfold View.singleton_ur_if.
                      unfold View.bot; simpls.
                      rewrite TimeMap.join_bot.
                      rewrite TimeMap.join_bot.
                      trivial.
                    }
                    { (** pln view *)
                      inv READABLE.
                      replace (Ordering.le Ordering.acqrel Ordering.plain) with false; trivial.
                      replace (Ordering.le Ordering.relaxed Ordering.plain) with false; trivial.
                      simpls.
                      rewrite TimeMap.join_bot.
                      unfold TimeMap.singleton.
                      eapply TimeMap.time_le_TimeMap_join_r.
                      pose proof LocFun.add_spec_eq. unfold LocFun.find in *.
                      rewrite H3.
                      eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1.
                    }
                  }
                }
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1))) as ai''.
                destruct ai'' eqn:EqAi''.
                {subst. rewrite H14. 
                  destruct (AveLat.kill_reg (AveLat.CSet tuples) r ) eqn:Eq1; 
                  destruct (AveLat.GetRegByLoc loc (AveLat.kill_reg (AveLat.CSet tuples) r)) eqn:Eq2; try discriminate;  eauto.
                  destruct (AveLat.GetRegByLoc loc (AveLat.CSet tuples0)) eqn:Eq3; try  discriminate; eauto.
                  destruct (AveLat.GetRegByLoc loc (AveLat.CSet tuples0)) eqn:Eq3; try  discriminate; eauto.
                }
                {subst. rewrite H14. 
                  destruct (AveLat.kill_reg (AveLat.CSet tuples) r ) eqn:Eq1; 
                  destruct (AveLat.GetRegByLoc loc (AveLat.kill_reg (AveLat.CSet tuples) r)) eqn:Eq2; try discriminate;  eauto.
                  destruct (AveLat.GetRegByLoc loc (AveLat.CSet tuples0)) eqn:Eq3; try  discriminate; eauto.
                  destruct (AveLat.GetRegByLoc loc (AveLat.CSet tuples0)) eqn:Eq3; try  discriminate; eauto.
                }
                rewrite H14.
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  (** kill_reg r implies r' <> r /\ r not in fv(e), implies eval(e) & eval(r) not changed, still match as in ai *)
                  destruct ai' eqn:EqAi'.
                  { 
                    rename t into reg'.
                    pose proof (classic (tu = AveTuple.AExpr reg' (Inst.expr_reg r))).
                    destruct H3.
                    { (** (r', r) *)
                      rewrite H3 in EqTu.
                      inversion EqTu.
                      rewrite <- H5.
                      unfolds transform_inst.
                      pose proof Heqai'.
                      eapply AveLat.getByLoc_implies_valid_tuple in Heqai'; eauto.
                      eapply W.filter_1 in Heqai'.
                      2: {eapply AveTuple.compat_bool_freeOfReg. }
                      remember (AveLat.GetRegByLoc loc (AveLat.CSet tuples)) as tmp.
                      destruct tmp eqn:EqTmp; try discriminate; eauto.
                      eapply AveLat.getByLoc_none_implies_kill_none with (r:=r) in Heqtmp; eauto.
                      rewrite <- Heqtmp in H4.
                      try discriminate.
                    } 
                    {
                      (** similar proof *)
                      assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inv H14.
                          eapply W.add_3 in H2.
                          2: {
                            intro. rewrite H4 in H3. try contradiction. 
                          }
                          remember (AveLat.kill_reg (AveLat.CSet tuples) r) as _ai.
                          remember (AveTuple.AExpr reg expr) as tu.
                          eapply AveLat.mem_of_kill_reg_implies_neq with (tuples':=tuples1) (tuples:=tuples) (r:=r) in H2; eauto.
                          unfolds AveTuple.get_reg. rewrite Heqtu in H2.  
                          intro. rewrite H4 in H2. contradiction. 
                        }
                      }
                      inv H14.
                      eapply W.add_3 in H2; eauto.
                      
                      pose proof H2.
                      eapply W.filter_1 in H2.
                      pose proof (MATCH_AI (AveTuple.AExpr reg expr)).
                      apply H6 in H2.
                      pose proof H4.
                      eapply regs_add_neg with (r:=r) (v:=val) (regs:=regs_src) in H4.
                      rewrite H4. 
                      assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                        eapply W.filter_2 in H5.
                        unfolds AveTuple.freeOfReg.
                        intro.
                        eapply sflib__andb_split in H5.
                        destruct H5.
                        unfolds negb.
                        des_ifH H5; try discriminate; eauto.
                        rewrite H9 in H10. discriminate.
                        eapply (AveTuple.compat_bool_freeOfReg r).
                      }
                      eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=val) in H9.
                      folds Const.t.
                      rewrite <- H9.
                      trivial.
                      eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                  }
                  { 
                    assert (r <> reg). {
                      destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                      {
                        subst. discriminate. 
                      }
                      {
                        subst. discriminate. 
                      }
                      {
                        inv H14.
                        eapply W.add_3 in H2.
                        2: {
                          intro. try discriminate.
                        }
                        remember (AveLat.kill_reg (AveLat.CSet tuples) r) as _ai.
                        remember (AveTuple.AExpr reg expr) as tu.
                        eapply AveLat.mem_of_kill_reg_implies_neq with (tuples':=tuples1) (tuples:=tuples) (r:=r) in H2; eauto.
                        unfolds AveTuple.get_reg. rewrite Heqtu in H2.  
                        intro. rewrite H3 in H2. contradiction. 
                      }
                    }
                    inv H14.
                    eapply W.add_3 in H2; eauto.
                    2: {
                      intro. discriminate.
                    }
                    pose proof H2.
                    eapply W.filter_1 in H2.
                    pose proof (MATCH_AI (AveTuple.AExpr reg expr)).
                    apply H5 in H2.
                    pose proof H3.
                    eapply regs_add_neg with (r:=r) (v:=val) (regs:=regs_src) in H3.
                    rewrite H3. 
                    assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                      eapply W.filter_2 in H4.
                      unfolds AveTuple.freeOfReg.
                      intro.
                      eapply sflib__andb_split in H4.
                      destruct H4.
                      unfolds negb.
                      des_ifH H4; try discriminate; eauto.
                      rewrite H8 in H9. discriminate.
                      eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                    eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=val) in H8.
                    folds Const.t.
                    rewrite <- H8.
                    trivial.
                    eapply (AveTuple.compat_bool_freeOfReg r).
                  }
                }
                { (** proof for: (r, x) in ai' is still correct *)
                  pose proof (classic (tu = AveTuple.AVar r loc)).
                  destruct H3.
                  { (** (r, x) is newly inserted *)
                    splits; eauto.
                    { (** lo loc = non-atomic *)
                      inv LOCAL0.
                      unfolds Ordering.mem_ord_match.
                      inv H3.
                      destruct (lo loc); trivial.
                      destruct LO as [A|[A|A]]; try discriminate.
                    }
                    {
                      rewrite EqTu in H3. 
                      inversion H3.
                      inv LOCAL.
                      inv LOCAL1. simpls.
                      inv READABLE. 
                      exists ts from released.
                      replace (Ordering.le Ordering.acqrel Ordering.plain) with false; trivial.
                      replace (Ordering.le Ordering.relaxed Ordering.plain) with false; trivial.
                      unfolds View.singleton_ur_if.
                      unfolds View.singleton_rw. simpls.
                      do 3 rewrite TimeMap.join_bot.
                      unfold TimeMap.singleton.
                      splits; eauto.
                      eapply TimeMap.time_le_TimeMap_join_r.
                      pose proof LocFun.add_spec_eq. unfold LocFun.find in *.
                      rewrite H4.
                      eapply DenseOrder.DenseOrder_le_PreOrder_obligation_1.
                      assert (RegFun.add r val regs_src r = val). {
                        pose proof RegFun.add_spec_eq.
                        unfold RegFun.find in *.
                        rewrite H4. trivial.
                       }
                      rewrite H4. 
                      rewrite <- MEM_EQ_START.
                      trivial.
                    }
                  }
                  { (** (r, x) is old *)
                    rewrite EqTu in H3. 
                    assert (W.In tu tuples). {
                      destruct ai'.
                      {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inv H14.
                          eapply W.add_3 in H2; eauto.
                          2: { intro. discriminate. }
                          unfolds AveLat.kill_reg.
                          inv EqKillReg.
                          eapply W.filter_1 in H2. trivial.
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }
                      {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          inv H14.
                          eapply W.add_3 in H2; eauto.
                          inv EqKillReg.
                          eapply W.filter_1 in H2. trivial.
                          eapply AveTuple.compat_bool_freeOfReg.
                        }
                      }
                    }
                    pose proof (MATCH_AI tu). apply H5 in H4.
                    rewrite EqTu in H4. 
                    assert (regs_src reg = RegFun.add r val regs_src reg). {
                      apply eq_sym.
                      assert (r <> reg). {
                        destruct (AveLat.kill_reg (AveLat.CSet tuples) r) eqn:EqKillReg.
                        {
                          subst. discriminate. 
                        }
                        {
                          subst. discriminate. 
                        }
                        {
                          destruct ai' eqn:EqAi'.
                          {
                            rename t into reg'.
                            
                            inv H14.
                            eapply W.add_3 in H2; eauto.
                            intro.
                            rewrite <- H6 in H2.
                            eapply AveLat.mem_of_kill_reg_implies_neq with (tuples:=tuples) in EqKillReg; eauto.
                            unfolds AveTuple.get_reg.
                            trivial.
                            intro. try discriminate.
                          }
                          {
                            
                            inv H14.
                            eapply W.add_3 in H2; eauto.
                            intro.
                            rewrite <- H6 in H2.
                            eapply AveLat.mem_of_kill_reg_implies_neq with (tuples:=tuples) in EqKillReg; eauto.
                            unfolds AveTuple.get_reg.
                            trivial.
                          }
                          

                        }
                      }
                      eapply regs_add_neg; eauto.
                    }
                    rewrite <- H6.
                    destruct H4.
                    splits; eauto.
                    destruct H8 as (t & f & R & PLN & RLX & MSG).
                    exists t f R. splits; eauto. 
                    { (** plain *)
                      inv LOCAL0. simpls.
                      replace (Ordering.le Ordering.acqrel Ordering.plain) with false; trivial.
                      replace (Ordering.le Ordering.relaxed Ordering.plain) with false; trivial.
                      unfolds View.singleton_ur_if.
                      unfolds View.singleton_rw. simpls.
                      do 2 rewrite TimeMap.join_bot.
                      assert (lc_tgt = lc_src). {
                        eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                      }
                      rewrite H8. trivial.
                    }
                    { (** rlx *)
                      inv LOCAL0. simpls.
                      replace (Ordering.le Ordering.acqrel Ordering.plain) with false; trivial.
                      replace (Ordering.le Ordering.relaxed Ordering.plain) with false; trivial.
                      unfolds View.singleton_ur_if.
                      unfolds View.singleton_rw. simpls.
                      rewrite TimeMap.join_bot.
                      unfold TimeMap.singleton.
                      eapply TimeMap.time_le_TimeMap_join_l.
                      assert (lc_tgt = lc_src). {
                        eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                      }
                      rewrite H8. trivial.
                    }
                  }
              }
            }
            { (** blk-level fixpoint *)
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H14; eauto.
                folds AveAI.b.
                rewrite H14.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H14; eauto.
              rewrite <- H14. 
              rewrite <- AI_BLK in FIXPOINT. trivial.
            }
            {
              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                {
                  destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                  eapply transf_step_psrv_loc_fact_valid with (bb:=blk_src); eauto.
                  subst analysis_blk.
                  eapply Ave_B.wf_transf_blk_step; eauto.
                  pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                  apply A in ANALYSIS.
                  folds AveAI.b.
                  rewrite ANALYSIS. 
                  eapply top_is_loc_fact_valid.
                }
              }
              trivial.
            }
            { (** mem_injected inj' promises_tgt' *)
              inv LOCAL0. simpls.
              eapply incr_inj_preserve_mem_injected with (inj:=inj); eauto.
              eapply incr_inj_refl.
            }
        }
        { 
          right.
          splits; eauto. 
          destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
          apply eq_inj_implies_incr; trivial.
          trivial.
          (* unfold eq_inj; intros; tauto. *)
        }
        {
          eapply Local.program_step_future; eauto.
        }
        { 
          eapply Local.program_step_future; eauto.
        }
        {
          eapply Local.program_step_future; eauto.
        }
        }
    }
    { (** non-atomic cas is invalid *)
      contradiction.
    }
  }
  { (** na write *)
    pose proof (nonatomic_or_atomic ord) as ORD; 
    destruct ORD. 
    2:{destruct ord; subst; try contradiction. }
    rewrite H2 in H0; try contradiction; eauto.
    inversion H. unfolds ThreadEvent.get_program_event.
    inv STATE.
    { (** non-atomic read: Inst.load r loc ord *)
    inversion H1; simpls.
    inversion INVARIANT. 
    inversion MATCH_LOCAL.
    inversion MATCH_RTL_STATE; simpls.
    rename H2 into SC_EQ_START.
    destruct H3 as (MEM_EQ_START & INJ_MAP_MEM_TGT).

    inversion MATCH_FRAME; simpls.

    remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
    remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
    eapply transform_blk_induction' in TRANSF_BLK; eauto.
    destruct TRANSF_BLK as (inst & b_src' & EqBlkSrc & TRSF).
    destruct TRSF as (TRSF_INST & TRSF_BLK).
    * 
      exists {|
          State.regs :=  regs_src;
          State.blk := b_src';
          State.cdhp := cdhp_src;
          State.cont := cont_src;
          State.code := code_src
        |} lc_tgt' sc_tgt' mem_tgt'.
      splits; eauto.
      { (** load -> load  *)
          eapply Thread.program_step_intro; simpls; eauto.
          eapply State.step_store; eauto.
          eapply store_transformed_inst_by_store in TRSF_INST; eauto.
          rewrite <- TRSF_INST; trivial.
          {subst; eauto. }
          inversion LOCAL.
          inversion LOCAL0.
          eapply Local.step_write with (kind := kind); eauto.
          rewrite <- H12 in LOCAL0; rewrite MEM_EQ_START in LOCAL0. 
          assert (lc_tgt = lc_src). {
            eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
          }
          rewrite <- H12.
          rewrite <- SC_EQ_START.
          rewrite <- H15.
          trivial. 
      }
      { (** match state *)
        inversion LOCAL.
        remember (fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else (inj' loc1 to1)) as inj''. 

        eapply cse_match_state_intro with(inj':=inj''); simpls; eauto.
        { (** invariant *)
          rewrite <- H12.
          { (** invariant *)
            unfold cse_invariant; splits; simpls; eauto.
            unfolds eq_ident_mapping.
            destruct INJ_MAP_MEM_TGT.
            inversion LOCAL0. inversion WRITE.
            eapply prm_keeps_mem_inj_dom_eq with (inj' := inj'') (mem' := mem_tgt') in H15; eauto.
            2: {
              intro. discriminate.
            }
            splits; eauto.
            intros.
            rewrite Heqinj'' in H17.
            des_ifH H17; simpls.
            {
              destruct a. subst. 
              inv H17. 
              eapply eq_refl.
            }
            apply H16 in H17. trivial.
          }
        }
        {
          eapply cse_match_local_state_intro; 
          try rewrite <- H3; eauto.
          2: {eapply eq_refl. }
          eapply cse_match_rtl_state_intro; eauto.
          simpls.
          eapply cse_match_frame_intro with(i:=i+1); eauto.
          rewrite EqBlkSrc in PARTIAL_BLK.
          {
            rewrite <- TRANSL_CDHP in Heqcdhp_tgt. trivial.
          }
          rewrite EqBlkSrc in PARTIAL_BLK.
          eapply bb_from_i_plus_one; eauto.
          {
              rewrite <- AveAI.get_tail_from_i_eq_i_plus_one; 
              rewrite AI_BLK; trivial. 
          }
          rewrite <- AI_BLK in TRSF_BLK.
          rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
          { (** match ai *)
            destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                eapply H16 in H15.
                folds AveAI.b.
                rewrite H15.
                eapply always_match_top.
              }
            eapply Ave_B.wf_transf_blk_step in H15; eauto.
            unfolds Ave_B.transf_step.
            rewrite EqBlkSrc in H15.
            pose proof TRSF_INST as TRSF_INST'.
            eapply store_transformed_inst_by_store in TRSF_INST; eauto.
            rewrite TRSF_INST in H15.
            unfolds Ave_I.transf.
            destruct ord eqn:EqOrd; try discriminate; eauto.
            (* relaxed *)  
              rewrite <- H15.
              rewrite <- AI_BLK in MATCH_AI.
              subst.
              unfolds match_abstract_interp.
              remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
              remember (AveLat.kill_var ai loc) as ai'.
              destruct ai eqn:EqAi.
              {
                unfolds AveLat.kill_reg.
                rewrite Heqai'. trivial.
              }
              {
                unfolds AveLat.kill_reg.
                rewrite Heqai'. trivial.
              }
              
              destruct ai' eqn:EqAi'; trivial.
              {
                unfold AveLat.kill_var in Heqai'. 
                destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
              }
              {
                unfold AveLat.kill_var in Heqai'. 
                destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
              }
              intros.
              unfolds match_abstract_fact.
              assert (W.In tu tuples). {
                unfolds AveLat.kill_var.
                destruct (AveLat.GetExprs (AveLat.CSet tuples)) eqn:EqGetExpr.
                {
                  inv Heqai'.
                  eapply W.filter_1 in H2; trivial.
                  eapply AveTuple.compat_bool_isNotSameLoc.
                }
                {
                  inv Heqai'.
                  eapply W.filter_1 in H2; trivial.
                  eapply AveTuple.compat_bool_isNotSameLoc.
                }
                {
                  inv Heqai'.
                  eapply W.union_1 in H2.
                  destruct H2.
                  {
                    unfolds AveLat.GetExprs. inv EqGetExpr.
                    eapply W.filter_1 in H2; trivial.
                    eapply AveTuple.compat_bool_isExpr.
                  }
                  eapply W.filter_1 in H2; trivial.
                  eapply AveTuple.compat_bool_isNotSameLoc.
                }
              }
              pose proof (MATCH_AI tu).
              apply H4 in H3. 
              destruct tu eqn:EqTu.
              {
                trivial.
              }
              {
                destruct H3 as (LO & t & f & R & PLN & RLX & MSG).
                splits; eauto.
                rewrite <- MEM_EQ_START in MSG.
                assert (Memory.future mem_tgt mem_tgt'). {
                  inversion LOCAL_WF.
                  eapply Local.write_step_future; eauto.
                }
                eapply Memory.future_get1 in H3; eauto.
                destruct H3 as (from' & msg' & MSG' & _ & LE).
                inv LE.
                do 3 eexists; splits; eauto.
                { (** plain *)
                  inv LOCAL0. simpls.
                  assert (loc0 <> loc). {
                    inv Heqai'.
                    eapply W.union_1 in H2. 
                    destruct H2.
                    {
                      eapply AveLat.mem_of_getExprs_implies_non_loc_in_ai' in H2; eauto.
                      unfolds AveLat.GetExprs. auto.
                    }
                    { 
                      eapply W.filter_2 in H2.
                      unfolds AveTuple.isNotSameLoc.
                      eapply negb_true_iff in H2.
                      rewrite Pos.eqb_sym in H2.
                      eapply Pos.eqb_neq in H2. trivial.
                      eapply AveTuple.compat_bool_isNotSameLoc.
                    }
                  }
                  unfold TimeMap.join.
                  unfold TimeMap.singleton.
                  rewrite  Loc_add_neq; eauto.
                  unfold LocFun.init.
                  rewrite Time_join_bot. 
                  assert (lc_src = lc_tgt). {
                    eapply cse_match_local_state_implies_eq_local; eauto.
                  } 
                  rewrite <- H5. trivial.
                }
                { (** rlx *)
                  inv LOCAL0. simpls.
                  eapply TimeMap.time_le_TimeMap_join_l.
                  assert (lc_src = lc_tgt). {
                    eapply cse_match_local_state_implies_eq_local; eauto.
                  } 
                  rewrite <- H3. trivial.
                }
              }   
          }
          { (** blk-level fixpoint *)
            eapply subblk_same_succ in EqBlkSrc.
            rewrite <- EqBlkSrc; trivial.
            destruct ANALYSIS.
            2: {
              intros.
              eapply (AveAI.get_head_from_eval) with (l:=lp) in H15; eauto.
              folds AveAI.b.
              rewrite H15.
              eapply AveLat.ge_top.
            }
            eapply Ave_B.wf_transf_blk_getlast in H15; eauto.
            rewrite <- H15. 
            rewrite <- AI_BLK in FIXPOINT. trivial.
          }
          {
              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                {
                  destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                  eapply transf_step_psrv_loc_fact_valid with (bb:=blk_src); eauto.
                  subst analysis_blk.
                  eapply Ave_B.wf_transf_blk_step; eauto.
                  pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                  apply A in ANALYSIS.
                  folds AveAI.b.
                  rewrite ANALYSIS. 
                  eapply top_is_loc_fact_valid.
                }
              }
              trivial.
          }
          { (** mem_injected inj'' promises_tgt' *)
            inv LOCAL0; simpls.
            pose proof WRITE as WRITE'.
            inv WRITE; simpls.
            inv PROMISE.
            { (** promise-add *)
              inv PROMISES.
              inv REMOVE.
              unfolds mem_injected.
              intros.
              pose proof (classic (loc = loc0)).
              destruct H2.
              {
                unfold Memory.get in MSG.
                pose proof (classic (to = t)).
                destruct H3.
                { 
                  eapply Memory.write_get2 in WRITE'.
                  destruct WRITE'.
                  unfold Memory.get in H4.
                  rewrite H3 in H4.
                  rewrite H2 in H4.
                  rewrite H2 in MSG.
                  rewrite H4 in MSG.
                  discriminate.
                }
                {
                  rewrite <- H2 in MSG.
                  rewrite Loc_add_eq in MSG.
                  eapply Cell.add_o with (t:=t) in ADD; eauto.
                  eapply Cell.remove_o with (t:=t) in REMOVE0; eauto.
                  des_ifH ADD; try contradiction. rewrite e0 in H3. contradiction.
                  rewrite REMOVE0 in MSG.
                  rewrite Loc_add_eq in MSG.
                  rewrite ADD in MSG.
                  eapply INJ_PROMISES in MSG.
                  rewrite H2 in MSG.
                  trivial.
                }
              }
              { 
                unfold Memory.get in MSG.
                rewrite Loc_add_neq in MSG; trivial.
                rewrite Loc_add_neq in MSG; trivial.
                assert (Memory.get loc0 t (Local.promises lc_tgt) =
                Some (f, Message.concrete val R)). { 
                  unfold Memory.get. trivial.
                }
                eapply INJ_PROMISES in H3. trivial.
              }
            }
            { (** promise-split *)
              inv PROMISES.
              inv REMOVE.
              unfolds mem_injected.
              intros.
              pose proof (classic (loc = loc0)).
              destruct H2.
              {
                unfold Memory.get in MSG.
                pose proof (classic (to = t)).
                destruct H3.
                { 
                  eapply Memory.write_get2 in WRITE'.
                  destruct WRITE'.
                  unfold Memory.get in H4.
                  rewrite H3 in H4.
                  rewrite H2 in H4.
                  rewrite H2 in MSG.
                  rewrite H4 in MSG.
                  discriminate.
                }
                {
                  rewrite <- H2 in MSG.
                  rewrite Loc_add_eq in MSG.
                  eapply Cell.split_o with (t:=t) in SPLIT; eauto.
                  eapply Cell.remove_o with (t:=t) in REMOVE0; eauto.
                  des_ifH SPLIT; try contradiction. rewrite e0 in H3. contradiction.
                  rewrite REMOVE0 in MSG.
                  rewrite Loc_add_eq in MSG.
                  rewrite SPLIT in MSG.
                  pose proof (classic (ts3 = t)).
                  destruct H4.
                  { 
                    des_ifH SPLIT.
                    rewrite Loc_add_eq in REMOVE0.
                    inv MSG.
                    {
                      inv WRITE'.
                      inv PROMISE.
                      eapply Memory.split_get0 in PROMISES.
                      destruct PROMISES as (_ & MSG' & _).
                      eapply INJ_PROMISES in MSG'.
                      trivial.
                    }
                    rewrite H4 in n0. contradiction.
                  }
                  {
                    des_ifH SPLIT.
                    rewrite e0 in H4; try contradiction.
                    eapply INJ_PROMISES in MSG.
                    rewrite H2 in MSG. trivial.
                  }
                }
              }
              { 
                unfold Memory.get in MSG.
                rewrite Loc_add_neq in MSG; trivial.
                rewrite Loc_add_neq in MSG; trivial.
                assert (Memory.get loc0 t (Local.promises lc_tgt) =
                Some (f, Message.concrete val R)). { 
                  unfold Memory.get. trivial.
                }
                eapply INJ_PROMISES in H3. trivial.
              }
            }
            { (** promise-lower *)
              inv PROMISES.
              inv REMOVE.
              unfolds mem_injected.
              intros.
              pose proof (classic (loc = loc0)).
              destruct H2.
              {
                unfold Memory.get in MSG.
                pose proof (classic (to = t)).
                destruct H3.
                { 
                  eapply Memory.write_get2 in WRITE'.
                  destruct WRITE'.
                  unfold Memory.get in H4.
                  rewrite H3 in H4.
                  rewrite H2 in H4.
                  rewrite H2 in MSG.
                  rewrite H4 in MSG.
                  discriminate.
                }
                {
                  rewrite <- H2 in MSG.
                  rewrite Loc_add_eq in MSG.
                  eapply Cell.lower_o with (t:=t) in LOWER; eauto.
                  eapply Cell.remove_o with (t:=t) in REMOVE0; eauto.
                  des_ifH LOWER; try contradiction. rewrite e0 in H3. contradiction.
                  rewrite REMOVE0 in MSG.
                  rewrite Loc_add_eq in MSG.
                  rewrite LOWER in MSG.
                  eapply INJ_PROMISES in MSG.
                  rewrite H2 in MSG.
                  trivial.
                }
              }
              { 
                unfold Memory.get in MSG.
                rewrite Loc_add_neq in MSG; trivial.
                rewrite Loc_add_neq in MSG; trivial.
                assert (Memory.get loc0 t (Local.promises lc_tgt) =
                Some (f, Message.concrete val R)). { 
                  unfold Memory.get. trivial.
                }
                eapply INJ_PROMISES in H3. trivial.
              }
            }
            { (** non-cancel *)
              discriminate.
            }
          }
        }
      { 
        right.
        splits; eauto.
        assert (incr_inj inj' inj''). {
          eapply construct_incr_inj1; eauto.
        }
        destruct PREEMPT as [EQ_INJ|INCR_INJ].
        destruct EQ_INJ as (_ & EQ_INJ).
        apply eq_inj_implies_incr in EQ_INJ.
        eapply incr_inj_transitivity; eauto.
        destruct INCR_INJ as (_ & EQ_INJ).
        eapply incr_inj_transitivity; eauto. 
      }
      {
        eapply Local.program_step_future; eauto.
      }
      { 
        eapply Local.program_step_future; eauto.
      }
      {
        eapply Local.program_step_future; eauto.
      }
      }
  }
  }
Qed.

(** Correctness of atomic memory access: read/write/case/fence/print *)
Theorem cse_match_state_preserving_at:
  forall te lo inj st_tgt st_src sc_tgt lc_src lc_tgt mem_tgt sc_src mem_src b st_tgt' lc_tgt' sc_tgt' mem_tgt', 
    Thread.program_step te lo 
        (@Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) 
        (@Thread.mk rtl_lang st_tgt' lc_tgt' sc_tgt' mem_tgt') 
    -> 
    ThreadEvent.is_at_or_out_step te 
    ->   
    (cse_match_state inj lo 
      (Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) 
      (Thread.mk rtl_lang st_src lc_src sc_src mem_src) b)
    -> 
      (exists st_src' lc_src' sc_src' mem_src' inj',
          Thread.program_step te lo (@Thread.mk rtl_lang st_src lc_src sc_src mem_src) 
                                    (@Thread.mk rtl_lang st_src' lc_src' sc_src' mem_src') 
          /\
          (cse_match_state inj' lo 
          (Thread.mk rtl_lang st_tgt' lc_tgt' sc_tgt' mem_tgt') (Thread.mk rtl_lang st_src' lc_src' sc_src' mem_src') true)
          /\ 
          incr_inj inj inj'
      ).
Proof.
  intros.
  destruct st_tgt as (regs_tgt, blk_tgt, cdhp_tgt, cont_tgt, code_tgt) eqn:EqStTgt.
  destruct st_tgt' as (regs_tgt', blk_tgt', cdhp_tgt', cont_tgt', code_tgt') eqn:EqStTgt'.
  destruct st_src as (regs_src, blk_src, cdhp_src, cont_src, code_src) eqn:EqStSrc; simpls.
  unfold ThreadEvent.is_at_or_out_step in H0.
  destruct te; try contradiction; eauto.
  {
    pose proof (nonatomic_or_atomic ord) as ORD; 
    destruct ORD. rewrite H2 in H0; try contradiction; eauto.
    (** atomic read *)
    inversion H. unfolds ThreadEvent.get_program_event.
    inv STATE.
    { (** Inst.load r loc ord *)
      inversion H1; simpls.
      inversion INVARIANT. 
      inversion MATCH_LOCAL.
      inversion MATCH_RTL_STATE; simpls.
      rename H3 into SC_EQ_START.
      destruct H4 as (MEM_EQ_START & INJ_MAP_MEM_TGT).

      inversion MATCH_FRAME; simpls.

      remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
      remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
      eapply transform_blk_induction' in TRANSF_BLK; eauto.
      destruct TRANSF_BLK as (inst & b_src' & EqBlkSrc & TRSF).
      destruct TRSF as (TRSF_INST & TRSF_BLK).
      * 
        exists {|
            State.regs :=  RegFun.add r val regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_tgt' sc_src mem_tgt' inj'.
        splits; eauto.
        { (** load -> load  *)
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_load; eauto.
            eapply at_load_transformed_inst_by_at_load in TRSF_INST; eauto.
            rewrite <- TRSF_INST; trivial.
            inversion LOCAL.
            rewrite <- H13; rewrite MEM_EQ_START.  
            eapply Local.step_read; eauto.
            rewrite <- H13 in LOCAL0; rewrite MEM_EQ_START in LOCAL0. 
            assert (lc_tgt = lc_src). {
              eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
            }
            rewrite <- H15. 
            trivial. 
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            rewrite <- H12.
            rewrite SC_EQ_START.
            unfold cse_invariant; simpls. splits; eauto.
            rewrite <- H13. trivial.
          }
          {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            2: {eapply eq_refl. }
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            {
              rewrite <- TRANSL_CDHP in Heqcdhp_tgt. trivial.
            }
            { rewrite REG_EQ. trivial. }
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            {
                rewrite <- AveAI.get_tail_from_i_eq_i_plus_one; 
                rewrite AI_BLK; trivial. 
            }
            rewrite <- AI_BLK in TRSF_BLK.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { (** match ai *)
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                eapply H16 in H15.
                folds AveAI.b.
                rewrite H15.
                eapply always_match_top.
              }
              eapply Ave_B.wf_transf_blk_step in H15; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H15.
              eapply at_load_transformed_inst_by_at_load in TRSF_INST; eauto.
              rewrite TRSF_INST in H15.
              unfolds Ave_I.transf.
              destruct ord eqn:EqOrd; try contradiction; eauto.
              - (* relaxed read *)  
                rewrite <- H15.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.kill_reg (ai) r) as ai'.
                destruct ai eqn:EqAi.
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                }
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                } (** ai = CSet tuples *)
                destruct ai' eqn:EqAi'; trivial.
                {
                  unfold AveLat.kill_reg in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                {
                  unfold AveLat.kill_reg in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  (** kill_reg r implies r' <> r /\ r not in fv(e), implies eval(e) & eval(r) not changed, still match as in ai *)
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H4 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  pose proof H4.
                  eapply regs_add_neg with (r:=r) (v:=val) (regs:=regs_src) in H4.
                  simpls.
                  rewrite H4.
                  assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_nonfree_var with (r':=reg); eauto.
                    rewrite H7 in H3. 
                    (**TOOD: a little bad, coupled, seems cannot extract a lemma for `kill_reg` *)
                    trivial.
                  }
                  eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=val) in H6.
                  folds Const.t.
                  rewrite <- H6.
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H9 in H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_freeOfReg r).
                  }
                  apply H7 in H8. rewrite EqTu in H8. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)
                  intros.
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H4 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  eapply regs_add_neg with (r:=r) (v:=val) (regs:=regs_src) in H4.

                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H7 in H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_freeOfReg r).
                  }
                  pose proof H4.
                  rewrite H7.
                  apply H5 in H6.
                  rewrite EqTu in H6. destruct H6. splits; eauto.

                  assert (View.rlx (TView.cur (Local.tview lc_src)) loc0 = View.rlx (TView.cur (Local.tview lc_tgt')) loc0). {
                    assert (lc_tgt = lc_src). {
                      eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                    }
                    rewrite <- H9.
                    pose proof (classic (loc <> loc0)).
                    destruct H10.
                    2: {
                      apply NNPP in H10.
                      inv LOCAL0.
                      rewrite H6 in LO.
                      unfold Ordering.mem_ord_match in LO. discriminate.
                    }
                    eapply rlx_read_step_keep_na_cur_rlx; eauto.
                }

                  assert (View.pln (TView.cur (Local.tview lc_src)) loc0 = View.pln (TView.cur (Local.tview lc_tgt')) loc0). {
                    assert (lc_tgt = lc_src). {
                      eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                    }
                    rewrite <- H10.
                    pose proof (classic (loc <> loc0)).
                    destruct H11.
                    2: {
                      apply NNPP in H11.
                      inv LOCAL0.
                      rewrite H6 in LO.
                      unfold Ordering.mem_ord_match in LO. discriminate.
                    }
                    eapply rlx_read_step_keep_na_cur_pln; eauto.
                }
                rewrite <- H9.
                rewrite <- H10.
                trivial.
                }
              - (** strong relaxed, same as relaxed *)
                rewrite <- H15.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.kill_reg (ai) r) as ai'.
                destruct ai eqn:EqAi.
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                }
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                } (** ai = CSet tuples *)
                destruct ai' eqn:EqAi'; trivial.
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  (** kill_reg r implies r' <> r /\ r not in fv(e), implies eval(e) & eval(r) not changed, still match as in ai *)
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H4 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  pose proof H4.
                  eapply regs_add_neg with (r:=r) (v:=val) (regs:=regs_src) in H4.
                  simpls.
                  rewrite H4.
                  assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_nonfree_var with (r':=reg); eauto.
                    rewrite H7 in H3. (**TOOD: a little bad, coupled, seems cannot extract a lemma for `kill_reg` *)
                    trivial.
                  }
                  eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=val) in H6.
                  folds Const.t.
                  rewrite <- H6.
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H9 in H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_freeOfReg r).
                  }
                  apply H7 in H8. rewrite EqTu in H8. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)
                  intros.
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H4 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  eapply regs_add_neg with (r:=r) (v:=val) (regs:=regs_src) in H4.

                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H7 in H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_freeOfReg r).
                  }
                  pose proof H4.
                  rewrite H7.
                  apply H5 in H6.
                  rewrite EqTu in H6. destruct H6. splits; eauto.

                  assert (View.rlx (TView.cur (Local.tview lc_src)) loc0 = View.rlx (TView.cur (Local.tview lc_tgt')) loc0). {
                    assert (lc_tgt = lc_src). {
                      eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                    }
                    rewrite <- H9.
                    pose proof (classic (loc <> loc0)).
                    destruct H10.
                    2: {
                      apply NNPP in H10.
                      inv LOCAL0.
                      rewrite H6 in LO.
                      unfold Ordering.mem_ord_match in LO. discriminate.
                    }
                    eapply rlx_read_step_keep_na_cur_rlx; eauto.
                }
                    assert (View.pln (TView.cur (Local.tview lc_src)) loc0 = View.pln (TView.cur (Local.tview lc_tgt')) loc0). {
                      assert (lc_tgt = lc_src). {
                        eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                      }
                      rewrite <- H10.
                      pose proof (classic (loc <> loc0)).
                      destruct H11.
                      2: {
                        apply NNPP in H11.
                        inv LOCAL0.
                        rewrite H6 in LO.
                        unfold Ordering.mem_ord_match in LO. discriminate.
                      }
                      eapply rlx_read_step_keep_na_cur_pln; eauto.
                  }
                  rewrite <- H9.
                  rewrite <- H10.
                  trivial.
                }
              - (** acq case, a little difference *)
                rewrite <- H15.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.kill_reg (AveLat.GetExprs ai) r) as ai'.
                destruct ai eqn:EqAi.
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                }
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                } (** ai = CSet tuples *)
                destruct ai' eqn:EqAi'; trivial.
                intros.
                unfolds match_abstract_fact.
                {
                  unfold AveLat.GetExprs in Heqai'.
                  unfold AveLat.kill_reg in Heqai'. 
                  discriminate.
                }
                {
                  unfold AveLat.GetExprs in Heqai'.
                  unfold AveLat.kill_reg in Heqai'. 
                  discriminate.
                }
                intros.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  (** kill_reg r implies r' <> r /\ r not in fv(e), implies eval(e) & eval(r) not changed, still match as in ai *)
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H4 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  pose proof H4.
                  eapply regs_add_neg with (r:=r) (v:=val) (regs:=regs_src) in H4.
                  simpls.
                  rewrite H4.
                  assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_nonfree_var with (r':=reg); eauto.
                    rewrite H7 in H3.
                    trivial.
                  }
                  eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=val) in H6.
                  folds Const.t.
                  rewrite <- H6.
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H9 in H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply (AveTuple.compat_bool_freeOfReg r).
                  }
                  apply H7 in H8. rewrite EqTu in H8. trivial.
                }
                { (** no more (r, x) in ai' *)
                  intros.
                  rewrite <- EqTu in H3. 
                  eapply AveLat.mem_of_getExprs_implies_non_loc_in_ai 
                    with (r:=r) in EqTu; try contradiction; eauto.
                }
              - (** sc, invalid case *)
                rewrite <- H15.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                unfolds match_abstract_interp. simpls. intros.
                pose proof W.empty_1. unfolds W.Empty. 
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember ( AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1))) as ai'.
                destruct ai; trivial.
                unfolds AveLat.top.
                intros.
                pose proof (H3 tu). 
                contradiction.
                unfolds AveLat.top.
                intros.
                pose proof (H3 tu). 
                contradiction.
            }
            { (** blk-level fixpoint *)
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H15; eauto.
                folds AveAI.b.
                rewrite H15.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H15; eauto.
              rewrite <- H15. 
              rewrite <- AI_BLK in FIXPOINT. trivial.
            }
            {
              {
                assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                  {
                    destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                    eapply transf_step_psrv_loc_fact_valid with (bb:=blk_src); eauto.
                    subst analysis_blk.
                    eapply Ave_B.wf_transf_blk_step; eauto.
                    pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                    apply A in ANALYSIS.
                    folds AveAI.b.
                    rewrite ANALYSIS. 
                    eapply top_is_loc_fact_valid.
                  }
                }
                trivial.
            }
  
            }
            { (** mem_injected inj' promises_tgt' *)
              inv LOCAL0. simpls.
              eapply incr_inj_preserve_mem_injected with (inj:=inj); eauto.
              destruct PREEMPT as [(_&EQ_INJ)|(_&INCR_INJ)].
              eapply eq_inj_implies_incr in EQ_INJ; trivial.
              trivial.
            }
        }
        { 
          left.
          splits; eauto.
          unfold eq_inj; intros; tauto.
        }
        {
          rewrite <- H13 in LOCAL0.
          rewrite <- H13.
          eapply Local.read_step_future; eauto.
        }
        { rewrite <- H12.
          rewrite <- H13.
          trivial.
        }
        {
          rewrite <- H13. trivial.
        } 
        }
        { 
          destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
          apply eq_inj_implies_incr; trivial.
          trivial.
        }
    }
    { (** Inst.cas r loc er ew ord ow *)
      inversion H1; simpls.
      inversion INVARIANT. 
      inversion MATCH_LOCAL.
      inversion MATCH_RTL_STATE; simpls.
      rename H3 into SC_EQ_START.
      destruct H4 as (MEM_EQ_START & INJ_MAP_MEM_TGT).

      inversion MATCH_FRAME; simpls.

      remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
      remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
      eapply transform_blk_induction' in TRANSF_BLK; eauto.
      destruct TRANSF_BLK as (inst & b_src' & EqBlkSrc & TRSF).
      destruct TRSF as (TRSF_INST & TRSF_BLK).
      * 
        exists {|
            State.regs :=  RegFun.add r Integers.Int.zero regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_tgt' sc_src mem_tgt' inj'.
        splits; eauto.
        { (** cas -> cas  *)
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_cas_flip; eauto.
            eapply at_cas_transformed_inst_by_at_cas in TRSF_INST; eauto.
            rewrite <- TRSF_INST; trivial.
            2: {
                inversion LOCAL.
                rewrite <- H13; 
              rewrite MEM_EQ_START.  
              eapply Local.step_read; eauto.
              rewrite <- H13 in LOCAL0; rewrite MEM_EQ_START in LOCAL0. 
              assert (lc_tgt = lc_src). {
                eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
              }
              rewrite <- H15. 
              trivial. 
            }
            subst; trivial.
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            rewrite <- H12.
            rewrite SC_EQ_START.
            unfold cse_invariant; simpls. splits; eauto.
            rewrite <- H13. trivial.
          }
          {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            2: {eapply eq_refl. }
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            {
              rewrite <- TRANSL_CDHP in Heqcdhp_tgt. trivial.
            }
            { rewrite REG_EQ. trivial. }
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            {
                rewrite <- AveAI.get_tail_from_i_eq_i_plus_one; 
                rewrite AI_BLK; trivial. 
            }
            rewrite <- AI_BLK in TRSF_BLK.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { (** match ai *)
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                eapply H16 in H15.
                folds AveAI.b.
                rewrite H15.
                eapply always_match_top.
              }
              eapply Ave_B.wf_transf_blk_step in H15; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H15.
              eapply at_cas_transformed_inst_by_at_cas in TRSF_INST; eauto.
              rewrite TRSF_INST in H15.
              unfolds Ave_I.transf.
              destruct ord eqn:EqOrd; try contradiction; eauto.
              - (* relaxed laod *)  
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                pose proof (classic (ow = Ordering.seqcst)). 
                destruct H3.
                {
                  rewrite H3 in H15.
                  rewrite <- H15.
                  destruct (AveAI.getFirst (AveAI.br_from_i analysis !! l i)); 
                  try eapply always_match_top; try rewrite always_match_bot; trivial.
                }
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.kill_reg (AveLat.kill_var ai loc) r) as ai'.
                assert (ai' = AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1))).
                {
                  destruct ow; try contradiction; trivial.
                }
                rewrite <- H4.
                clear H15.
                rename H4 into H15.
                destruct ai eqn:EqAi.
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                }
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                } (** ai = CSet tuples *)
                clear H3.
                destruct ai' eqn:EqAi'; trivial.
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  (** kill_reg r implies r' <> r /\ r not in fv(e), implies eval(e) & eval(r) not changed, still match as in ai *)
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H4 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  pose proof H4.
                  eapply regs_add_neg with (r:=r) (v:=Integers.Int.zero) (regs:=regs_src) in H4.
                  simpls.
                  folds Const.t.
                  rewrite H4.
                  assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_nonfree_var with (r':=reg); eauto.
                    rewrite H7 in H3. (**TOOD: a little bad, coupled, seems cannot extract a lemma for `kill_reg` *)
                    trivial.
                  }
                  eapply regs_add_nonfree_var_eq_eval_expr with (regs:=(regs_src)) (val:=Integers.Int.zero) in H6.
                  folds Const.t.
                  rewrite <- H6.
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H9 in H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply W.union_1 in H3; trivial.
                    2: {
                    eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                    destruct H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isNotSameLoc).
                  }
                  apply H7 in H8. rewrite EqTu in H8. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)
                  intros.
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H4 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  eapply regs_add_neg with (r:=r) (v:=Integers.Int.zero) (regs:=regs_src) in H4.

                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H7 in H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply W.union_1 in H3; trivial.
                    2: {
                    eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                    destruct H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isNotSameLoc).
                  }
                  pose proof H4.
                  apply H5 in H6.  
                  rewrite EqTu in H6. destruct H6. splits; eauto.
                  folds Const.t.
                  rewrite H7.

                  assert (View.rlx (TView.cur (Local.tview lc_src)) loc0 = View.rlx (TView.cur (Local.tview lc_tgt')) loc0). {
                    assert (lc_tgt = lc_src). {
                      eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                    }
                    rewrite <- H9.
                    pose proof (classic (loc <> loc0)).
                    destruct H10.
                    2: {
                      apply NNPP in H10.
                      inv LOCAL0.
                      rewrite H6 in LO.
                      unfold Ordering.mem_ord_match in LO. discriminate.
                    }
                    eapply rlx_read_step_keep_na_cur_rlx; eauto.
                  }
                  assert (View.pln (TView.cur (Local.tview lc_src)) loc0 = View.pln (TView.cur (Local.tview lc_tgt')) loc0). {
                      assert (lc_tgt = lc_src). {
                        eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                      }
                      rewrite <- H10.
                      pose proof (classic (loc <> loc0)).
                      destruct H11.
                      2: {
                        apply NNPP in H11.
                        inv LOCAL0.
                        rewrite H6 in LO.
                        unfold Ordering.mem_ord_match in LO. discriminate.
                      }
                      eapply rlx_read_step_keep_na_cur_pln; eauto.
                  }
                  rewrite <- H9.
                  rewrite <- H10.
                  trivial.
                }
              - (** strong relaxed, same as relaxed *)
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                pose proof (classic (ow = Ordering.seqcst)). 
                destruct H3.
                {
                  rewrite H3 in H15.
                  rewrite <- H15.
                  destruct (AveAI.getFirst (AveAI.br_from_i analysis !! l i)); try 
                  eapply always_match_top; try rewrite always_match_bot; eauto.
                }
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.kill_reg (AveLat.kill_var ai loc) r) as ai'.
                assert (ai' = AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1))).
                {
                  destruct ow; try contradiction; trivial.
                }
                rewrite <- H4.
                clear H15.
                rename H4 into H15.
                destruct ai eqn:EqAi.
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                }
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                } (** ai = CSet tuples *)
                clear H3.
                destruct ai' eqn:EqAi'; trivial.
                intros.
                unfolds match_abstract_fact.
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                intros.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  (** kill_reg r implies r' <> r /\ r not in fv(e), implies eval(e) & eval(r) not changed, still match as in ai *)
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H4 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  pose proof H4.
                  eapply regs_add_neg with (r:=r) (v:=Integers.Int.zero) (regs:=regs_src) in H4.
                  simpls.
                  folds Const.t.
                  rewrite H4.
                  assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_nonfree_var with (r':=reg); eauto.
                    rewrite H7 in H3. (**TOOD: a little bad, coupled, seems cannot extract a lemma for `kill_reg` *)
                    trivial.
                  }
                  eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=Integers.Int.zero) in H6.
                  folds Const.t.
                  rewrite <- H6.
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H9 in H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply W.union_1 in H3; trivial.
                    2: {
                    eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                    destruct H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isNotSameLoc).
                  }
                  apply H7 in H8. rewrite EqTu in H8. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)
                  intros.
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H4 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  eapply regs_add_neg with (r:=r) (v:=Integers.Int.zero) (regs:=regs_src) in H4.

                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H7 in H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply W.union_1 in H3; trivial.
                    2: {
                    eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                    destruct H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isNotSameLoc).
                  }
                  pose proof H4.
                  apply H5 in H6.
                  rewrite EqTu in H6. destruct H6. splits; eauto.
                  folds Const.t.
                  rewrite H7.

                  assert (View.rlx (TView.cur (Local.tview lc_src)) loc0 = View.rlx (TView.cur (Local.tview lc_tgt')) loc0). {
                    assert (lc_tgt = lc_src). {
                      eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                    }
                    rewrite <- H9.
                    pose proof (classic (loc <> loc0)).
                    destruct H10.
                    2: {
                      apply NNPP in H10.
                      inv LOCAL0.
                      rewrite H6 in LO.
                      unfold Ordering.mem_ord_match in LO. discriminate.
                    }
                    eapply rlx_read_step_keep_na_cur_rlx; eauto.
                  }
                    assert (View.pln (TView.cur (Local.tview lc_src)) loc0 = View.pln (TView.cur (Local.tview lc_tgt')) loc0). {
                      assert (lc_tgt = lc_src). {
                        eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                      }
                      rewrite <- H10.
                      pose proof (classic (loc <> loc0)).
                      destruct H11.
                      2: {
                        apply NNPP in H11.
                        inv LOCAL0.
                        rewrite H6 in LO.
                        unfold Ordering.mem_ord_match in LO. discriminate.
                      }
                      eapply rlx_read_step_keep_na_cur_pln; eauto.
                  }
                    rewrite <- H9.
                    rewrite <- H10.
                    trivial.
                  }
              - (** acq case, a little difference *)
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                pose proof (classic (ow = Ordering.seqcst)). 
                destruct H3.
                {
                  rewrite H3 in H15.
                  rewrite <- H15.
                  destruct (AveAI.getFirst (AveAI.br_from_i analysis !! l i)); trivial; 
                  eapply always_match_top.
                }
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.kill_reg (AveLat.GetExprs ai) r) as ai'.
                assert (ai' = AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1))).
                {
                  destruct ow; try contradiction; trivial.
                }
                rewrite <- H4.
                clear H15.
                rename H4 into H15.
                destruct ai eqn:EqAi.
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                }
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                } (** ai = CSet tuples *)
                clear H3.
                destruct ai' eqn:EqAi'; trivial.
                intros.
                unfolds match_abstract_fact.
                {
                  unfold AveLat.GetExprs in Heqai'.
                  unfold AveLat.kill_reg in Heqai'. 
                  discriminate.
                }
                {
                  unfold AveLat.GetExprs in Heqai'.
                  unfold AveLat.kill_reg in Heqai'. 
                  discriminate.
                }
                intros.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  (** kill_reg r implies r' <> r /\ r not in fv(e), implies eval(e) & eval(r) not changed, still match as in ai *)
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H4 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  pose proof H4.
                  eapply regs_add_neg with (r:=r) (v:=Integers.Int.zero) (regs:=regs_src) in H4.
                  simpls.
                  folds Const.t.
                  rewrite H4.
                  assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_nonfree_var with (r':=reg); eauto.
                    rewrite H7 in H3.
                    trivial.
                  }
                  eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=Integers.Int.zero) in H6.
                  folds Const.t.
                  rewrite <- H6.
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H9 in H3.
                    eapply W.filter_1 in H3; trivial.
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply (AveTuple.compat_bool_freeOfReg r).
                  }
                  apply H7 in H8. rewrite EqTu in H8. trivial.
                }
                { (** no more (r, x) in ai' *)
                  intros.
                  rewrite <- EqTu in H3. 
                  eapply AveLat.mem_of_getExprs_implies_non_loc_in_ai 
                    with (r:=r) in EqTu; try contradiction; eauto.
                }
              - (** sc, invalid case *)
                remember ( AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                destruct ow; destruct ai; rewrite <- H15; try rewrite always_match_bot; try eapply always_match_top; trivial; subst; rewrite <- Heqai in MATCH_AI; try eapply never_match_bot in MATCH_AI; contradiction.
            }
            { (** blk-level fixpoint *)
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H15; eauto.
                folds AveAI.b.
                rewrite H15.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H15; eauto.
              rewrite <- H15. 
              rewrite <- AI_BLK in FIXPOINT. trivial.
            }
            {
              {
                assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                  {
                    destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                    eapply transf_step_psrv_loc_fact_valid with (bb:=blk_src); eauto.
                    subst analysis_blk.
                    eapply Ave_B.wf_transf_blk_step; eauto.
                    pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                    apply A in ANALYSIS.
                    folds AveAI.b.
                    rewrite ANALYSIS. 
                    eapply top_is_loc_fact_valid.
                  }
                }
                trivial.
            }
  
            }
            { (** mem_injected inj' promises_tgt' *)
              inv LOCAL0. simpls.
              eapply incr_inj_preserve_mem_injected with (inj:=inj); eauto.
              destruct PREEMPT as [(_&EQ_INJ)|(_&INCR_INJ)].
              eapply eq_inj_implies_incr in EQ_INJ; trivial.
              trivial.
            }
        }
        { 
          left.
          splits; eauto.
          unfold eq_inj; intros; tauto.
        }
        {
          rewrite <- H13 in LOCAL0.
          rewrite <- H13.
          eapply Local.read_step_future; eauto.
        }
        { rewrite <- H12.
          rewrite <- H13.
          trivial.
        }
        {
          rewrite <- H13. trivial.
        } 
        }
        { 
          destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
          apply eq_inj_implies_incr; trivial.
          trivial.
        }
  }
  }
  { (**atomic write *)
    pose proof (nonatomic_or_atomic ord) as ORD; 
    destruct ORD. rewrite H2 in H0; try contradiction; eauto.
    inversion H. 
    inv STATE.
    { (** Inst.store r loc ord *)
      inversion H1; simpls.
      inversion INVARIANT. 
      inversion MATCH_LOCAL.
      inversion MATCH_RTL_STATE; simpls.
      rename H3 into SC_EQ_START.
      destruct H4 as (MEM_EQ_START & INJ_MAP_MEM_TGT).

      inversion MATCH_FRAME; simpls.

      remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
      remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
      eapply transform_blk_induction' in TRANSF_BLK; eauto.
      destruct TRANSF_BLK as (inst & b_src' & EqBlkSrc & TRSF).
      destruct TRSF as (TRSF_INST & TRSF_BLK).
      * 
      inversion LOCAL.
      pose proof (classic (exists msg3 ts3, kind = Memory.op_kind_split ts3 msg3)).
      destruct H16.
      { (** promise split *) (** FIXME: 感觉split不需要单独分一个case *)
        remember (fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else (inj' loc1 to1)) as inj''. 
        exists {|
            State.regs := regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_tgt' sc_tgt' mem_tgt' inj''.
        splits; eauto.
        { (** store -> store  *)
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_store; eauto.
            eapply at_store_transformed_inst_by_at_store in TRSF_INST; eauto.
            rewrite <- TRSF_INST; trivial.
            inversion LOCAL. subst; eauto.
            (* rewrite <- MEM_EQ_START.   *)
            inv H.
            rewrite MEM_EQ_START in LOCAL0. 
            eapply Local.step_write with (kind:=kind); eauto. 
            assert (lc_src = lc_tgt). {eapply cse_match_local_state_implies_eq_local; eauto. }
            rewrite H. 
            rewrite <- SC_EQ_START. trivial.
        }
        { (** match state *)
          eapply cse_match_state_intro with(inj':=inj''); simpls; eauto.
          { (** invariant *)
            rewrite <- H14.
            unfold cse_invariant; splits; simpls; eauto.
            unfolds eq_ident_mapping.
            destruct INJ_MAP_MEM_TGT.
            split.
            2: {
              intros.
              rewrite Heqinj'' in H19.
              des_ifH H19; simpls.
              { 
                destruct a. subst. 
                inv H19. 
                eapply eq_refl.
              }
            apply H18 in H19. trivial.
          }
          { (** dom equal*)
            rewrite H14.
            inversion LOCAL0.
            inversion WRITE.
            destruct H16 as (msg3 & ts3 & SPLIT).
            eapply prm_split_incr_mem_with_inj; eauto.
            intro. try discriminate.
          }

          }
          {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            2: {eapply eq_refl. }
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            {
              rewrite <- TRANSL_CDHP in Heqcdhp_tgt. trivial.
            }
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            {
                rewrite <- AveAI.get_tail_from_i_eq_i_plus_one; 
                rewrite AI_BLK; trivial. 
            }
            rewrite <- AI_BLK in TRSF_BLK.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { (** match ai *)
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                eapply H18 in H17.
                folds AveAI.b.
                rewrite H17.
                eapply always_match_top.
            }
              eapply Ave_B.wf_transf_blk_step in H17; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H17.
              eapply at_store_transformed_inst_by_at_store in TRSF_INST; eauto.
              rewrite TRSF_INST in H17.
              unfolds Ave_I.transf.
              pose proof (classic (ord = Ordering.seqcst)).
              destruct H18. 
              { (** sc case *)
                rewrite <- H15.
                rewrite <- H17.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                unfolds match_abstract_interp. simpls. intros.
                pose proof W.empty_1. unfolds W.Empty. 
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember ( AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1))) as ai'.
                destruct ai; trivial.
                unfolds AveLat.top.
                intros.
                pose proof (H3 tu). 
                contradiction.
                unfolds AveLat.top.
                intros.
                pose proof (H3 tu). 
                contradiction.
              }
              assert (ord <> Ordering.plain). {
                destruct ord eqn:EqOrd; try contradiction; eauto.
              }
                rewrite <- H17.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                (* rewrite MEM_EQ_START. *)
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.kill_var ai loc) as ai'.
                replace ( match ord with
                    | Ordering.seqcst => 
                      match ai with
                      | AveLat.Bot => AveLat.Bot
                      | _ => AveLat.top
                      end
                    | _ => ai'
                    end) with ai'.
                2: {
                  destruct ord; try contradiction; trivial.
                }
                destruct ai eqn:EqAi.
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                }
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                } (** ai = CSet tuples *)
                destruct ai' eqn:EqAi'; trivial.
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H6 in H3.
                    eapply W.union_1 in H3; trivial.
                    destruct H3; 
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply (AveTuple.compat_bool_isNotSameLoc loc).
                  }
                  apply H4 in H5. rewrite EqTu in H5. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)               
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H6 in H3.
                    eapply W.union_1 in H3; trivial.
                    destruct H3; 
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply (AveTuple.compat_bool_isNotSameLoc loc).
                  }
                  pose proof H4.
                  apply H4 in H5.
                  rewrite EqTu in H5. destruct H5; splits; eauto.

                  assert (View.rlx (TView.cur (Local.tview lc_src)) loc0 = View.rlx (TView.cur (Local.tview lc_tgt')) loc0). {
                    assert (lc_tgt = lc_src). {
                      eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                    }
                    rewrite <- H8.
                    pose proof (classic (loc <> loc0)).
                    destruct H9.
                    2: {
                      apply NNPP in H9.
                      inv LOCAL0.
                      rewrite H5 in LO.
                      unfold Ordering.mem_ord_match in LO. rewrite LO in H19; try contradiction.
                    }
                    eapply atomic_write_step_keep_na_cur_rlx; eauto.
                    destruct ord; try contradiction; try splits; eauto.
                }
                assert (View.pln (TView.cur (Local.tview lc_src)) loc0 = View.pln (TView.cur (Local.tview lc_tgt')) loc0). {
                  assert (lc_tgt = lc_src). {
                    eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                  }
                  rewrite <- H9.
                  pose proof (classic (loc <> loc0)).
                  destruct H10.
                  2: {
                    apply NNPP in H10.
                    inv LOCAL0.
                    rewrite H5 in LO.
                    unfold Ordering.mem_ord_match in LO. rewrite LO in H19; try contradiction.
                  }
                  eapply atomic_write_step_keep_na_cur_pln; eauto.
                  destruct ord; try contradiction; try splits; eauto.
                }
                rewrite <- H9.
                rewrite <- H8.
                trivial.
                destruct H7 as (t & f & R & PLN & RLX & MSG).
                rewrite <- MEM_EQ_START in MSG.
                assert (Memory.future mem_tgt mem_tgt'). {
                  inversion LOCAL_WF.
                  eapply Local.write_step_future; eauto.
                }
                eapply Memory.future_get1 in H7; eauto.
                destruct H7 as (from' & msg' & MSG' & _ & LE).
                inv LE.
                do 3 eexists; splits; eauto.
                }
            }
            { (** blk-level fixpoint *)
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H17; eauto.
                folds AveAI.b.
                rewrite H17.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H17; eauto.
              rewrite <- H17. 
              rewrite <- AI_BLK in FIXPOINT. trivial.
            }
            {
              {
                assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                  {
                    destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                    eapply transf_step_psrv_loc_fact_valid with (bb:=blk_src); eauto.
                    subst analysis_blk.
                    eapply Ave_B.wf_transf_blk_step; eauto.
                    pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                    apply A in ANALYSIS.
                    folds AveAI.b.
                    rewrite ANALYSIS. 
                    eapply top_is_loc_fact_valid.
                  }
                }
                trivial.
            }
  
            }
            { (** mem_injected inj'' promises_tgt' *)
              assert (incr_inj inj inj'). {
                destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
                eapply eq_inj_implies_incr; trivial.
                trivial.
              }
              eapply incr_inj_preserve_mem_injected in H17; eauto.
              inv LOCAL0. simpls.
              inversion WRITE. 
              eapply remove_keeps_promises_injected; eauto.
              destruct H16 as (msg3 & ts3 & H16).
              eapply prm_split_keeps_promises_injected; eauto. 
            }
        }
        {
          left.
          splits; eauto.
          unfold eq_inj; intros; tauto.
        }
        {
          rewrite <- H13 in LOCAL0.
          (* rewrite <- H13. *)
          eapply Local.write_step_future; eauto.
        }
        {
          inversion LOCAL0. inv WRITE. simpls.
          eapply Memory.promise_closed_timemap; eauto. 
        }
        {
          assert (Memory.future mem_tgt mem_tgt'). {
            inversion LOCAL_WF.
            eapply Local.write_step_future; eauto.
          }
          eapply Memory.future_closed; eauto.
        } 
        }
        { 
          assert (incr_inj inj' inj''). {
            eapply construct_incr_inj1; eauto.

          }
          destruct PREEMPT as [EQ_INJ|INCR_INJ].
          destruct EQ_INJ as (_ & EQ_INJ).
          apply eq_inj_implies_incr in EQ_INJ.
          eapply incr_inj_transitivity; eauto.
          destruct INCR_INJ as (_ & EQ_INJ).
          eapply incr_inj_transitivity; eauto.
        }
      }
      (*non split case*)
        remember (fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else (inj' loc1 to1)) as inj''. 

        exists {|
            State.regs := regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_tgt' sc_tgt' mem_tgt' inj''.
        splits; eauto.
        { (** store -> store  *)
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_store; eauto.
            eapply at_store_transformed_inst_by_at_store in TRSF_INST; eauto.
            rewrite <- TRSF_INST; trivial.
            inversion LOCAL. subst; eauto.
            (* rewrite <- MEM_EQ_START.   *)
            inv H.
            rewrite MEM_EQ_START in LOCAL0. 
            eapply Local.step_write with (kind:=kind); eauto. 
            assert (lc_src = lc_tgt). {eapply cse_match_local_state_implies_eq_local; eauto. }
            rewrite H. 
            rewrite <- SC_EQ_START. trivial.
        }
        { (** match state *)
          (* inversion LOCAL. *)
          (* remember (fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else (inj' loc1 to1)) as inj''.  *)
          eapply cse_match_state_intro with(inj':=inj''); simpls; eauto.
          { (** invariant *)
            unfold cse_invariant; simpls. splits; eauto.
            econs; eauto.
            {
              econs. 
              {
                intros. exists t.
                rewrite Heqinj''.
                inv INVARIANT; simpls. destruct H18. inv H4.
                inv H5.

                des_if; simpls; try destruct a; subst; eauto.
                eapply non_split_write_o with (l:=loc1) (t:=t) in LOCAL0; eauto. 
                des_ifH LOCAL0; simpls. 
                - destruct a. rewrite H4 in o; rewrite H5 in o. destruct o; try contradiction. 
                - rewrite LOCAL0 in MSG. eapply SOUND in MSG.
                destruct MSG.  
                  exploit H6; eauto. intro. rewrite <- x0 in H4; trivial.
              }
              {
                intros.  
                pose proof INJ.
                rewrite Heqinj'' in INJ.
                inv INVARIANT; simpls. destruct H19.
                inv H4. inv H5.
                eapply non_split_write_o with (l:=loc1) (t:=t) in LOCAL0; eauto. 

                des_ifH INJ; simpls. 
                {
                  destruct a.
                  destruct INJ.
                  do 3 eexists; eauto.
                  rewrite H5 in LOCAL0; rewrite H4 in LOCAL0. 
                  des_ifH LOCAL0; simpls.
                  2: { destruct o; try contradiction. }
                  rewrite LOCAL0. eauto.
                }
                {
                  des_ifH LOCAL0; simpls. destruct a. rewrite H4 in o; rewrite H5 in o.
                  destruct o; try contradiction.
                  rewrite LOCAL0.
                  apply COMPLETE in INJ.
                  trivial.
                }
              }
            }
            {
              rewrite Heqinj''. 
              intros.
              des_ifH H17; simpls; eauto.
              destruct a. rewrite H19 in H17; inv H17; eapply eq_refl.
              inv INJ_MAP_MEM_TGT.
              apply H19 in H17; trivial.
            }
          }
          {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            2: {eapply eq_refl. }
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            {
              rewrite <- TRANSL_CDHP in Heqcdhp_tgt. trivial.
            }
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            {
                rewrite <- AveAI.get_tail_from_i_eq_i_plus_one; 
                rewrite AI_BLK; trivial. 
            }
            rewrite <- AI_BLK in TRSF_BLK.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { (** match ai *)
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
              pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
              eapply H18 in H17.
              folds AveAI.b.
              rewrite H17.
              eapply always_match_top.
          }
              eapply Ave_B.wf_transf_blk_step in H17; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H17.
              eapply at_store_transformed_inst_by_at_store in TRSF_INST; eauto.
              rewrite TRSF_INST in H17.
              unfolds Ave_I.transf.
              pose proof (classic (ord = Ordering.seqcst)).
              destruct H18. 
              { (** sc case *)
                rewrite <- H15.
                rewrite <- H17.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                unfolds match_abstract_interp. simpls. intros.
                pose proof W.empty_1. unfolds W.Empty.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember ( AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1))) as ai'.
                destruct ai; trivial.
                unfolds AveLat.top.
                intros.
                pose proof (H3 tu). 
                contradiction.
                unfolds AveLat.top.
                intros.
                pose proof (H3 tu). 
                contradiction.
              }
              assert (ord <> Ordering.plain). {
                destruct ord eqn:EqOrd; try contradiction; eauto.
              }
                rewrite <- H17.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                (* rewrite MEM_EQ_START. *)
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.kill_var ai loc) as ai'.
                replace ( match ord with
                    | Ordering.seqcst =>
                      match ai with
                      | AveLat.Bot => AveLat.Bot
                      | _ => AveLat.top
                      end
                    | _ => ai'
                    end) with ai'.
                2: {
                  destruct ord; try contradiction; trivial.
                }
                destruct ai eqn:EqAi.
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                }
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                } (** ai = CSet tuples *)
                destruct ai' eqn:EqAi'; trivial.
                intros.
                unfolds match_abstract_fact.
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                intros.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H6 in H3.
                    eapply W.union_1 in H3; trivial.
                    destruct H3; 
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply (AveTuple.compat_bool_isNotSameLoc loc).
                  }
                  apply H4 in H5. rewrite EqTu in H5. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)               
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H3.
                    inversion Heqai'.
                    rewrite H6 in H3.
                    eapply W.union_1 in H3; trivial.
                    destruct H3; 
                    eapply W.filter_1 in H3; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply (AveTuple.compat_bool_isNotSameLoc loc).
                  }
                  pose proof H4.
                  apply H4 in H5.
                  rewrite EqTu in H5. destruct H5; splits; eauto.

                  assert (View.rlx (TView.cur (Local.tview lc_src)) loc0 = View.rlx (TView.cur (Local.tview lc_tgt')) loc0). {
                    assert (lc_tgt = lc_src). {
                      eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                    }
                    rewrite <- H8.
                    pose proof (classic (loc <> loc0)).
                    destruct H9.
                    2: {
                      apply NNPP in H9.
                      inv LOCAL0.
                      rewrite H5 in LO.
                      unfold Ordering.mem_ord_match in LO. rewrite LO in H19; try contradiction.
                    }
                    eapply atomic_write_step_keep_na_cur_rlx; eauto.
                    destruct ord; try contradiction; try splits; eauto.
                }
                assert (View.pln (TView.cur (Local.tview lc_src)) loc0 = View.pln (TView.cur (Local.tview lc_tgt')) loc0). {
                  assert (lc_tgt = lc_src). {
                    eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                  }
                  rewrite <- H9.
                  pose proof (classic (loc <> loc0)).
                  destruct H10.
                  2: {
                    apply NNPP in H10.
                    inv LOCAL0.
                    rewrite H5 in LO.
                    unfold Ordering.mem_ord_match in LO. rewrite LO in H19; try contradiction.
                  }
                  eapply atomic_write_step_keep_na_cur_pln; eauto.
                  destruct ord; try contradiction; try splits; eauto.
                }
                rewrite <- H9.
                rewrite <- H8.
                trivial.
                destruct H7 as (t & f & R & PLN & RLX & MSG).
                rewrite <- MEM_EQ_START in MSG.
                assert (Memory.future mem_tgt mem_tgt'). {
                  inversion LOCAL_WF.
                  eapply Local.write_step_future; eauto.
                }
                eapply Memory.future_get1 in H7; eauto.
                destruct H7 as (from' & msg' & MSG' & _ & LE).
                inv LE.
                do 3 eexists; splits; eauto.
                }
            }
            { (** blk-level fixpoint *)
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H17; eauto.
                folds AveAI.b.
                rewrite H17.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H17; eauto.
              rewrite <- H17. 
              rewrite <- AI_BLK in FIXPOINT. trivial.
            }
            {
              {
                assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                  {
                    destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                    eapply transf_step_psrv_loc_fact_valid with (bb:=blk_src); eauto.
                    subst analysis_blk.
                    eapply Ave_B.wf_transf_blk_step; eauto.
                    pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                    apply A in ANALYSIS.
                    folds AveAI.b.
                    rewrite ANALYSIS. 
                    eapply top_is_loc_fact_valid.
                  }
                }
                trivial.
            }
  
            }
            { (** mem_injected inj'' promises_tgt' *)
              assert (incr_inj inj inj'). {
                destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
                eapply eq_inj_implies_incr; trivial.
                trivial.
              }
              eapply incr_inj_preserve_mem_injected in H17; eauto.
              inv LOCAL0. simpls.
              inversion WRITE. 
              eapply remove_keeps_promises_injected; eauto.
              eapply prm_concrete_keeps_promises_injected; eauto.
            }
        }
        {
          left.
          splits; eauto.
          unfold eq_inj; intros; tauto.
        }
        {
          rewrite <- H13 in LOCAL0.
          (* rewrite <- H13. *)
          eapply Local.write_step_future; eauto.
        }
        {
          inversion LOCAL0. inv WRITE. simpls.
          eapply Memory.promise_closed_timemap; eauto. 
        }
        {
          assert (Memory.future mem_tgt mem_tgt'). {
            inversion LOCAL_WF.
            eapply Local.write_step_future; eauto.
          }
          eapply Memory.future_closed; eauto.
        } 
        }
        { 
          assert (incr_inj inj' inj''). {
            eapply construct_incr_inj1; eauto.

          }
          destruct PREEMPT as [EQ_INJ|INCR_INJ].
          destruct EQ_INJ as (_ & EQ_INJ).
          apply eq_inj_implies_incr in EQ_INJ.
          eapply incr_inj_transitivity; eauto.
          destruct INCR_INJ as (_ & EQ_INJ).
          eapply incr_inj_transitivity; eauto.
        }
    }
  } 
  { (** atomic cas, upd *)
    assert (ORDR: ordr <> Ordering.plain). {
      remember (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw) as e.
      inv H.
      eapply Local.update_step_ord_not_pln in LOCAL; eauto. tauto. 
    }
    assert (ORDW: ordw <> Ordering.plain). {
      inv H.
      eapply Local.update_step_ord_not_pln in LOCAL; eauto. tauto. 
    }
    (* rewrite H2 in H; try contradiction; eauto. *)
    inversion H. 
    unfolds ThreadEvent.get_program_event.
    inv STATE.

    (** Inst.cas r loc er ew ord ow *)
      inversion H1; simpls.
      inversion INVARIANT. 
      inversion MATCH_LOCAL.
      inversion MATCH_RTL_STATE; simpls.
      rename H2 into SC_EQ_START.
      destruct H3 as (MEM_EQ_START & INJ_MAP_MEM_TGT).
      remember (fun loc1 to1 => if loc_ts_eq_dec (loc, tsw) (loc1, to1) then Some tsw else (inj' loc1 to1)) as inj''. 

      inversion MATCH_FRAME; simpls.

      remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
      remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
      eapply transform_blk_induction' in TRANSF_BLK; eauto.
      destruct TRANSF_BLK as (inst & b_src' & EqBlkSrc & TRSF).
      destruct TRSF as (TRSF_INST & TRSF_BLK).
      * 
        exists {|
            State.regs :=  RegFun.add r Integers.Int.one regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_tgt' sc_tgt' mem_tgt' inj''.
        splits; eauto.
        { (** cas -> cas  *)
            rewrite REG_EQ.
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_cas_same; eauto.
            eapply at_cas_transformed_inst_by_at_cas in TRSF_INST; eauto.
            rewrite <- TRSF_INST; trivial.
              inversion LOCAL.
              trivial.
              assert (lc_tgt = lc_src). {
                eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
              }
              rewrite <- H15. 
              rewrite REG_EQ in LOCAL1. rewrite REG_EQ in LOCAL2.
              eapply Local.step_update with (lc2:=lc2) (kind:=kind); eauto.
              rewrite MEM_EQ_START in LOCAL1. rewrite H18 in LOCAL1. trivial.
              rewrite SC_EQ_START in LOCAL2. rewrite MEM_EQ_START in LOCAL2.
              subst.
              trivial.
        }
        { (** match state *)
          inversion LOCAL. pose proof LOCAL as LOCAL'.
          eapply cse_match_state_intro with(inj':=inj''); simpls; eauto.
          { (** invariant *)
            unfold cse_invariant; splits; simpls; eauto.
            unfolds eq_ident_mapping.
            destruct INJ_MAP_MEM_TGT.
            split.
            2: {
              intros.
              rewrite Heqinj'' in H20.
              des_ifH H20; simpls.
              { 
                destruct a. subst. 
                inv H20. 
                eapply eq_refl.
              }
            apply H19 in H20. trivial. 
            }
            { (** dom eq *)
              inversion H18.
              inversion LOCAL2.
              inversion WRITE.
              eapply prm_keeps_mem_inj_dom_eq with (inj:=inj') (inj':=inj'') in PROMISE; eauto.
              intro. discriminate.
            }
          }
          {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            2: {eapply eq_refl. }
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            {
              rewrite <- TRANSL_CDHP in Heqcdhp_tgt. trivial.
            }
            { rewrite REG_EQ. trivial. }
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            {
                rewrite <- AveAI.get_tail_from_i_eq_i_plus_one; 
                rewrite AI_BLK; trivial. 
            }
            rewrite <- AI_BLK in TRSF_BLK.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { (** match ai *)
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                eapply H19 in H18.
                folds AveAI.b.
                rewrite H18.
                eapply always_match_top.
            }
              eapply Ave_B.wf_transf_blk_step in H18; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H18.
              eapply at_cas_transformed_inst_by_at_cas in TRSF_INST; eauto.
              rewrite TRSF_INST in H18.
              unfolds Ave_I.transf.
              pose proof (classic (ordw = Ordering.seqcst)) as G.
              destruct G. 
              {
                rewrite H19 in H18. rewrite <- H18. 
                destruct (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) eqn:Eq; try 
                eapply always_match_top; eauto.
                {
                  subst. rewrite Eq in MATCH_AI. eapply never_match_bot in MATCH_AI.
                  contradiction.
                }

              }
              assert (ordw = Ordering.relaxed \/ ordw = Ordering.strong_relaxed \/ ordw = Ordering.acqrel). {
                destruct ordw; tauto.
              }

              (* Set Printing All. *)
              (* destruct ordw; try contradiction. *)
              assert ( (match ordr with
                | Ordering.relaxed | Ordering.strong_relaxed =>
                    AveLat.kill_reg
                      (AveLat.kill_var
                        (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) loc) r
                | Ordering.acqrel =>
                    AveLat.kill_reg
                      (AveLat.GetExprs
                        (AveAI.getFirst (AveAI.br_from_i analysis !! l i))) r
                | _ =>
                    match AveAI.getFirst (AveAI.br_from_i analysis !! l i) with
                    | AveLat.Bot => AveLat.Bot
                    | _ => AveLat.top
                    end
                end)= ( AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))). {
                  destruct H20 as [G|[G|G]]; rewrite G in H18; eauto.
                }
                clear H18. rename H21 into H18.

              destruct ordr eqn:EqOrdR; try contradiction; eauto.
              - (** relaxed *)
                rewrite <- H18.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                (* rewrite MEM_EQ_START. *)
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.kill_reg (AveLat.kill_var ai loc) r) as ai'.
                destruct ai eqn:EqAi.
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                }
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                } (** ai = CSet tuples *)
                destruct ai' eqn:EqAi'; trivial.
                {
                  unfold AveLat.kill_var in Heqai'. 
                  unfold AveLat.kill_reg in Heqai'. 

                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                {
                  unfold AveLat.kill_var in Heqai'. 
                  unfold AveLat.kill_reg in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  (** kill_reg r implies r' <> r /\ r not in fv(e), implies eval(e) & eval(r) not changed, still match as in ai *)
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H3 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  pose proof H3.
                  eapply regs_add_neg with (r:=r) (v:=Integers.Int.one) (regs:=regs_src) in H3.
                  simpls.
                  folds Const.t.
                  rewrite H3.
                  assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_nonfree_var with (r':=reg); eauto.
                    rewrite H6 in H2. (**TOOD: a little bad, coupled, seems cannot extract a lemma for `kill_reg` *)
                    trivial.
                  }
                  eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=Integers.Int.one) in H5.
                  folds Const.t.
                  rewrite <- H5.
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H2.
                    inversion Heqai'.
                    rewrite H8 in H2.
                    eapply W.filter_1 in H2; trivial.
                    eapply W.union_1 in H2; trivial.
                    2: {
                    eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                    destruct H2.
                    eapply W.filter_1 in H2; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply W.filter_1 in H2; trivial.
                    eapply (AveTuple.compat_bool_isNotSameLoc).
                  }
                  apply H6 in H7. rewrite EqTu in H7. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)
                    intros.
                    assert (r <> reg). {
                      unfolds AveLat.kill_reg. inversion Heqai'.
                      rewrite <- EqAi' in Heqai'.
                      eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                      rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                      intro. rewrite H3 in Heqai'. contradiction. 
                      subst; trivial.
                    }
                    eapply regs_add_neg with (r:=r) (v:=Integers.Int.one) (regs:=regs_src) in H3.

                    pose proof (MATCH_AI tu).
                    assert (W.In tu tuples). {
                      rewrite <- EqTu in H2.
                      inversion Heqai'.
                      rewrite H6 in H2.
                      eapply W.filter_1 in H2; trivial.
                      eapply W.union_1 in H2; trivial.
                      2: {
                      eapply (AveTuple.compat_bool_freeOfReg r).
                      }
                      destruct H2.
                      eapply W.filter_1 in H2; trivial.
                      eapply (AveTuple.compat_bool_isExpr).
                      eapply W.filter_1 in H2; trivial.
                      eapply (AveTuple.compat_bool_isNotSameLoc).
                    }
                    pose proof H3.
                    apply H4 in H5.
                    rewrite EqTu in H5. destruct H5. splits; eauto.
                    folds Const.t.
                    rewrite H6.
                    assert (View.rlx (TView.cur (Local.tview lc2)) loc0 = View.rlx (TView.cur (Local.tview lc_tgt')) loc0). {
                      pose proof (classic (loc <> loc0)).
                      destruct H8.
                      2: {
                        apply NNPP in H8.
                        inv LOCAL2.
                        rewrite H5 in LO.
                        unfold Ordering.mem_ord_match in LO. 
                        rewrite LO in H20. destruct H20 as [G|[G|G]]; try discriminate. 
                      }
                      eapply atomic_write_step_keep_na_cur_rlx; eauto.
                    }

                    assert (View.rlx (TView.cur (Local.tview lc_src)) loc0 = View.rlx (TView.cur (Local.tview lc2)) loc0). {
                      assert (lc_tgt = lc_src). {
                        eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                      }
                      rewrite <- H9. clear H9.
                      pose proof (classic (loc <> loc0)).
                      destruct H9.
                      2: {
                        apply NNPP in H9.
                        inv LOCAL1.
                        rewrite H5 in LO.
                        unfold Ordering.mem_ord_match in LO. 
                        discriminate.
                      }
                      eapply rlx_read_step_keep_na_cur_rlx; eauto.
                    }
                    rewrite H8 in H9.
                    rewrite <- H9.

                    assert (View.pln (TView.cur (Local.tview lc2)) loc0 = View.pln (TView.cur (Local.tview lc_tgt')) loc0). {
                        pose proof (classic (loc <> loc0)).
                        destruct H10.
                        2: {
                          apply NNPP in H10.
                          inv LOCAL2.
                          rewrite H5 in LO.
                          unfold Ordering.mem_ord_match in LO. 
                        rewrite LO in H20. destruct H20 as [G|[G|G]]; try discriminate. 

                        }
                        eapply atomic_write_step_keep_na_cur_pln; eauto.
                    }

                    assert (View.pln (TView.cur (Local.tview lc_src)) loc0 = View.pln (TView.cur (Local.tview lc2)) loc0). {
                      assert (lc_tgt = lc_src). {
                        eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                      }
                      rewrite <- H11. clear H11.
                      pose proof (classic (loc <> loc0)).
                      destruct H11.
                      2: {
                        apply NNPP in H11.
                        inv LOCAL1.
                        rewrite H5 in LO.
                        unfold Ordering.mem_ord_match in LO. 
                        discriminate.
                      }
                        eapply rlx_read_step_keep_na_cur_pln; eauto.
                    }
                    rewrite H10 in H11.
                    rewrite <- H11.
                    destruct H7 as (t & f & R & PLN & RLX & MSG).
                    rewrite <- MEM_EQ_START in MSG.
                    assert (Memory.future mem_tgt mem_tgt'). {
                      inversion LOCAL_WF.
                      eapply Local.program_step_future; eauto.
                    }
                    eapply Memory.future_get1 in H7; eauto.
                    destruct H7 as (from' & msg' & MSG' & _ & LE).
                    inv LE.
                    do 3 eexists; splits; eauto.
                }
              - (** strong relaxed *)
                rewrite <- H18.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                (* rewrite MEM_EQ_START. *)
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.kill_reg (AveLat.kill_var ai loc) r) as ai'.
                destruct ai eqn:EqAi.
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                }
                {
                  unfolds AveLat.kill_reg.
                  rewrite Heqai'. trivial.
                } (** ai = CSet tuples *)
                destruct ai' eqn:EqAi'; trivial.
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                {
                  unfold AveLat.kill_var in Heqai'. 
                  destruct (AveLat.GetExprs (AveLat.CSet tuples)); try discriminate;  eauto.
                }
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { (** proof for: any (r', e) in ai' is still correct *)
                  (** kill_reg r implies r' <> r /\ r not in fv(e), implies eval(e) & eval(r) not changed, still match as in ai *)
                  assert (r <> reg). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    rewrite <- EqAi' in Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                    rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                    intro. rewrite H3 in Heqai'. contradiction. 
                    subst; trivial.
                  }
                  pose proof H3.
                  eapply regs_add_neg with (r:=r) (v:=Integers.Int.one) (regs:=regs_src) in H3.
                  simpls.
                  folds Const.t.
                  rewrite H3.
                  assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                    unfolds AveLat.kill_reg. inversion Heqai'.
                    eapply AveLat.mem_of_kill_reg_implies_nonfree_var with (r':=reg); eauto.
                    rewrite H6 in H2. (**TOOD: a little bad, coupled, seems cannot extract a lemma for `kill_reg` *)
                    trivial.
                  }
                  eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=Integers.Int.one) in H5.
                  folds Const.t.
                  rewrite <- H5.
                  pose proof (MATCH_AI tu).
                  assert (W.In tu tuples). {
                    rewrite <- EqTu in H2.
                    inversion Heqai'.
                    rewrite H8 in H2.
                    eapply W.filter_1 in H2; trivial.
                    eapply W.union_1 in H2; trivial.
                    2: {
                    eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                    destruct H2.
                    eapply W.filter_1 in H2; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                    eapply W.filter_1 in H2; trivial.
                    eapply (AveTuple.compat_bool_isNotSameLoc).
                  }
                  apply H6 in H7. rewrite EqTu in H7. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)
                    intros.
                    assert (r <> reg). {
                      unfolds AveLat.kill_reg. inversion Heqai'.
                      rewrite <- EqAi' in Heqai'.
                      eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                      rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                      intro. rewrite H3 in Heqai'. contradiction. 
                      subst; trivial.
                    }
                    eapply regs_add_neg with (r:=r) (v:=Integers.Int.one) (regs:=regs_src) in H3.

                    pose proof (MATCH_AI tu).
                    assert (W.In tu tuples). {
                      rewrite <- EqTu in H2.
                      inversion Heqai'.
                      rewrite H6 in H2.
                      eapply W.filter_1 in H2; trivial.
                      eapply W.union_1 in H2; trivial.
                      2: {
                      eapply (AveTuple.compat_bool_freeOfReg r).
                      }
                      destruct H2.
                      eapply W.filter_1 in H2; trivial.
                      eapply (AveTuple.compat_bool_isExpr).
                      eapply W.filter_1 in H2; trivial.
                      eapply (AveTuple.compat_bool_isNotSameLoc).
                    }
                    pose proof H3.
                    apply H4 in H5.
                    rewrite EqTu in H5. destruct H5. splits; eauto.
                    folds Const.t.
                    rewrite H6.
                    assert (View.rlx (TView.cur (Local.tview lc2)) loc0 = View.rlx (TView.cur (Local.tview lc_tgt')) loc0). {
                      pose proof (classic (loc <> loc0)).
                      destruct H8.
                      2: {
                        apply NNPP in H8.
                        inv LOCAL2.
                        rewrite H5 in LO.
                        unfold Ordering.mem_ord_match in LO.
                        rewrite LO in ORDW.
                        contradiction.
                      }
                      eapply atomic_write_step_keep_na_cur_rlx; eauto.
                    }

                    assert (View.rlx (TView.cur (Local.tview lc_src)) loc0 = View.rlx (TView.cur (Local.tview lc2)) loc0). {
                      assert (lc_tgt = lc_src). {
                        eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                      }
                      rewrite <- H9. clear H9.
                      pose proof (classic (loc <> loc0)).
                      destruct H9.
                      2: {
                        apply NNPP in H9.
                        inv LOCAL1.
                        rewrite H5 in LO.
                        unfold Ordering.mem_ord_match in LO. 
                        discriminate.
                      }
                      eapply rlx_read_step_keep_na_cur_rlx; eauto.
                    }
                    rewrite H8 in H9.
                    rewrite <- H9.

                    assert (View.pln (TView.cur (Local.tview lc2)) loc0 = View.pln (TView.cur (Local.tview lc_tgt')) loc0). {
                        pose proof (classic (loc <> loc0)).
                        destruct H10.
                        2: {
                          apply NNPP in H10.
                          inv LOCAL2.
                          rewrite H5 in LO.
                          unfold Ordering.mem_ord_match in LO. 
                          rewrite LO in ORDW.
                          contradiction.
                        }
                        eapply atomic_write_step_keep_na_cur_pln; eauto.
                    }

                    assert (View.pln (TView.cur (Local.tview lc_src)) loc0 = View.pln (TView.cur (Local.tview lc2)) loc0). {
                      assert (lc_tgt = lc_src). {
                        eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                      }
                      rewrite <- H11. clear H11.
                      pose proof (classic (loc <> loc0)).
                      destruct H11.
                      2: {
                        apply NNPP in H11.
                        inv LOCAL1.
                        rewrite H5 in LO.
                        unfold Ordering.mem_ord_match in LO. 
                        discriminate.
                      }
                        eapply rlx_read_step_keep_na_cur_pln; eauto.
                    }
                    rewrite H10 in H11.
                    rewrite <- H11.
                    destruct H7 as (t & f & R & PLN & RLX & MSG).
                    rewrite <- MEM_EQ_START in MSG.
                    assert (Memory.future mem_tgt mem_tgt'). {
                      inversion LOCAL_WF.
                      eapply Local.program_step_future; eauto.
                    }
                    eapply Memory.future_get1 in H7; eauto.
                    destruct H7 as (from' & msg' & MSG' & _ & LE).
                    inv LE.
                    do 3 eexists; splits; eauto.
                }
                - (** acq case, a little difference *)
                  rewrite <- H18.
                  rewrite <- AI_BLK in MATCH_AI.
                  subst.
                  (* rewrite MEM_EQ_START. *)
                  unfolds match_abstract_interp.
                  remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                  remember (AveLat.kill_reg (AveLat.GetExprs ai) r) as ai'.
                  destruct ai eqn:EqAi.
                  {
                    unfolds AveLat.kill_reg.
                    rewrite Heqai'. trivial.
                  }
                  {
                    unfolds AveLat.kill_reg.
                    rewrite Heqai'. trivial.
                  } (** ai = CSet tuples *)
                  destruct ai' eqn:EqAi'; trivial.
                  {
                    unfold AveLat.GetExprs in Heqai'.
                    unfold AveLat.kill_reg in Heqai'. 
                    discriminate.
                  }
                  {
                    unfold AveLat.GetExprs in Heqai'.
                    unfold AveLat.kill_reg in Heqai'. 
                    discriminate.
                  }
                  intros.
                  unfolds match_abstract_fact.
                  destruct tu eqn:EqTu.
                  { (** proof for: any (r', e) in ai' is still correct *)
                    (** kill_reg r implies r' <> r /\ r not in fv(e), implies eval(e) & eval(r) not changed, still match as in ai *)
                    assert (r <> reg). {
                      unfolds AveLat.kill_reg. inversion Heqai'.
                      rewrite <- EqAi' in Heqai'.
                      eapply AveLat.mem_of_kill_reg_implies_neq with (tu := tu) in Heqai'; eauto.
                      rewrite EqTu in Heqai'. unfold AveTuple.get_reg in Heqai'. 
                      intro. rewrite H3 in Heqai'. contradiction. 
                      subst; trivial.
                    }
                    rename H3 into H4.
                    pose proof H4.
                    eapply regs_add_neg with (r:=r) (v:=Integers.Int.one) (regs:=regs_src) in H4.
                    simpls.
                    folds Const.t.
                    rewrite H4.
                    assert (~RegSet.mem r (Inst.regs_of_expr expr)). {
                      unfolds AveLat.kill_reg. inversion Heqai'.
                      eapply AveLat.mem_of_kill_reg_implies_nonfree_var with (r':=reg); eauto.
                      rewrite H6 in H2.
                      trivial.
                    }
                    eapply regs_add_nonfree_var_eq_eval_expr with (regs:=regs_src) (val:=Integers.Int.one) in H5.
                    folds Const.t.
                    rewrite <- H5.
                    pose proof (MATCH_AI tu).
                    assert (W.In tu tuples). {
                      rewrite <- EqTu in H2.
                      inversion Heqai'.
                      rewrite H8 in H2.
                      eapply W.filter_1 in H2; trivial.
                      eapply W.filter_1 in H2; trivial.
                      eapply (AveTuple.compat_bool_isExpr).
                      eapply (AveTuple.compat_bool_freeOfReg r).
                    }
                    apply H6 in H7. rewrite EqTu in H7. trivial.
                  }
                  { (** no more (r, x) in ai' *)
                    rewrite <- EqTu in H2. 
                    eapply AveLat.mem_of_getExprs_implies_non_loc_in_ai 
                      with (r:=r) in EqTu; try contradiction; eauto.
                  }
                - (** sc, invalid case *)
                  remember ( AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                  destruct ai eqn:Eq; rewrite <- H18.
                  rewrite <- AI_BLK in MATCH_AI.
                  rewrite <- Heqai in MATCH_AI. eapply never_match_bot in MATCH_AI. contradiction.
                  eapply always_match_top.
                  eapply always_match_top.
            }
            { (** blk-level fixpoint *)
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H18; eauto.
                folds AveAI.b.
                rewrite H18.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H18; eauto.
              rewrite <- H18. 
              rewrite <- AI_BLK in FIXPOINT. trivial.
            }
            {
              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                {
                  destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                  eapply transf_step_psrv_loc_fact_valid with (bb:=blk_src); eauto.
                  subst analysis_blk.
                  eapply Ave_B.wf_transf_blk_step; eauto.
                  pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                  apply A in ANALYSIS.
                  folds AveAI.b.
                  rewrite ANALYSIS. 
                  eapply top_is_loc_fact_valid.
                }
              }
              trivial.
          }

            { (** mem_injected inj;' promises_tgt' *)
              assert (mem_inj_dom_eq inj'' mem_tgt'). {
                unfolds eq_ident_mapping.
                destruct INJ_MAP_MEM_TGT.
                inversion LOCAL2.
                inversion WRITE.
                eapply prm_keeps_mem_inj_dom_eq with (inj:=inj') (inj':=inj'') in PROMISE; eauto.
                intro. discriminate.
              }
              eapply Local.program_step_future in LOCAL'; eauto.
              destruct LOCAL'. 
              inversion H19.
              unfolds Memory.le.
              inversion H18.
              unfolds mem_injected.
              intros.
              apply PROMISES in MSG.
              apply SOUND in MSG. trivial.
            }
        }
        { 
          left.
          splits; eauto.
          unfold eq_inj; intros; tauto.
        }
        {
          eapply Local.program_step_future; eauto.
        }
        {
          eapply Local.program_step_future; eauto. 
        }
        {
          eapply Local.program_step_future; eauto. 
        } 
        }
        {
          assert (incr_inj inj' inj''). {
            eapply construct_incr_inj1; eauto.

          }
          destruct PREEMPT as [EQ_INJ|INCR_INJ].
          destruct EQ_INJ as (_ & EQ_INJ).
          apply eq_inj_implies_incr in EQ_INJ.
          eapply incr_inj_transitivity; eauto.
          destruct INCR_INJ as (_ & EQ_INJ).
          eapply incr_inj_transitivity; eauto.
        }
  } 
  { (** fence *)
    inversion H. 
    inv STATE.
    { (** fence_rel *)
      inversion H1; simpls.
      inversion INVARIANT. 
      inversion MATCH_LOCAL.
      inversion MATCH_RTL_STATE; simpls.
      rename H2 into SC_EQ_START.
      destruct H3 as (MEM_EQ_START & INJ_MAP_MEM_TGT).

      inversion MATCH_FRAME; simpls.

      remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
      remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
      eapply transform_blk_induction' in TRANSF_BLK; eauto.
      destruct TRANSF_BLK as (inst & b_src' & EqBlkSrc & TRSF).
      destruct TRSF as (TRSF_INST & TRSF_BLK).
      * 
        exists {|
            State.regs :=  regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_tgt' sc_tgt' mem_tgt' inj'.
        splits; eauto.
        { (** fence -> fence  *)
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_fence_rel; eauto.
            eapply fence_rel_transformed_inst_by_fence_rel in TRSF_INST; eauto.
            rewrite <- TRSF_INST; trivial.
            inversion LOCAL.
            rewrite <- H9.
            rewrite MEM_EQ_START.  
            eapply Local.step_fence; eauto.
            (* rewrite <- H9 in LOCAL0; rewrite MEM_EQ_START in LOCAL0.  *)
            assert (lc_tgt = lc_src). {
              eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
            }
            rewrite <- H11. 
            rewrite SC_EQ_START in LOCAL0.
            trivial. 
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            subst.
            unfold cse_invariant; simpls. splits; eauto.
          }
          {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            2: {eapply eq_refl. }
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            {
              rewrite <- TRANSL_CDHP in Heqcdhp_tgt. trivial.
            }
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            {
                rewrite <- AveAI.get_tail_from_i_eq_i_plus_one; 
                rewrite AI_BLK; trivial. 
            }
            rewrite <- AI_BLK in TRSF_BLK.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { (** match ai *)
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                eapply H12 in H11.
                folds AveAI.b.
                rewrite H11.
                eapply always_match_top.
            }
              eapply Ave_B.wf_transf_blk_step in H11; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H11.
              eapply fence_rel_transformed_inst_by_fence_rel in TRSF_INST; eauto.
              rewrite TRSF_INST in H11.
              unfolds Ave_I.transf.
                rewrite <- H11.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                unfolds match_abstract_interp.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                (* remember (AveLat.kill_reg (ai) r) as ai'. *)
                destruct ai eqn:EqAi; trivial.
                (** ai = CSet tuples *)
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { 
                  pose proof (MATCH_AI tu).
                  rewrite <- EqTu in H2.
                  apply H3 in H2. rewrite EqTu in H2. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)
                
                  pose proof (MATCH_AI tu).
                  rewrite <- EqTu in H2.
                  apply H3 in H2.
                  rewrite EqTu in H2. destruct H2. splits; eauto.
                  assert (lc_tgt = lc_src). {
                    eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                  }
                  rewrite <- H5 in H4.
                  (** TODO: fence preserve pln/rlx*)
                  assert ((View.pln (TView.cur (Local.tview lc_tgt)) loc) = (View.pln (TView.cur (Local.tview lc_tgt')) loc)). {
                    eapply fence_rel_step_keep_na_cur_pln; eauto. 
                  }
                  assert ((View.rlx (TView.cur (Local.tview lc_tgt)) loc) = (View.rlx (TView.cur (Local.tview lc_tgt')) loc)). {
                    eapply fence_rel_step_keep_na_cur_rlx; eauto. 
                  }
                  rewrite <- H6. rewrite <- H7. trivial.
                }
            }
            { (** blk-level fixpoint *)
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H11; eauto.
                folds AveAI.b.
                rewrite H11.
                eapply AveLat.ge_top.
              }
            
              eapply Ave_B.wf_transf_blk_getlast in H11; eauto.
              rewrite <- H11. 
              rewrite <- AI_BLK in FIXPOINT. trivial.
            }
            {
              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                {
                  destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                  eapply transf_step_psrv_loc_fact_valid with (bb:=blk_src); eauto.
                  subst analysis_blk.
                  eapply Ave_B.wf_transf_blk_step; eauto.
                  pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                  apply A in ANALYSIS.
                  folds AveAI.b.
                  rewrite ANALYSIS. 
                  eapply top_is_loc_fact_valid.
                }
              }
              trivial.
          }

            { (** mem_injected inj' promises_tgt' *)
              inv LOCAL0. simpls.
              eapply incr_inj_preserve_mem_injected with (inj:=inj); eauto.
              destruct PREEMPT as [(_&EQ_INJ)|(_&INCR_INJ)].
              eapply eq_inj_implies_incr in EQ_INJ; trivial.
              trivial.
            }
        }
        { 
          left.
          splits; eauto.
          unfold eq_inj; intros; tauto.
        }
        {
          eapply Local.program_step_future; eauto.
        }
        { 
          eapply Local.program_step_future; eauto.
        }
        {
          eapply Local.program_step_future; eauto.
        } 
        }
        { 
          destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
          apply eq_inj_implies_incr; trivial.
          trivial.
        }
    }
    { (** fence_acq *)
      inversion H1; simpls.
      inversion INVARIANT. 
      inversion MATCH_LOCAL.
      inversion MATCH_RTL_STATE; simpls.
      rename H2 into SC_EQ_START.
      destruct H3 as (MEM_EQ_START & INJ_MAP_MEM_TGT).

      inversion MATCH_FRAME; simpls.

      remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
      remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
      eapply transform_blk_induction' in TRANSF_BLK; eauto.
      destruct TRANSF_BLK as (inst & b_src' & EqBlkSrc & TRSF).

      destruct TRSF as (TRSF_INST & TRSF_BLK).
      * 
        exists {|
            State.regs :=  regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_tgt' sc_tgt' mem_tgt' inj'.
        splits; eauto.
        { (** fence -> fence  *)
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_fence_acq; eauto.
            eapply fence_acq_transformed_inst_by_fence_acq in TRSF_INST; eauto.
            rewrite <- TRSF_INST; trivial.
            inversion LOCAL.
            rewrite <- H9.
            rewrite MEM_EQ_START.  
            eapply Local.step_fence; eauto.
            (* rewrite <- H9 in LOCAL0; rewrite MEM_EQ_START in LOCAL0.  *)
            assert (lc_tgt = lc_src). {
              eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
            }
            rewrite <- H11. 
            rewrite SC_EQ_START in LOCAL0.
            trivial. 
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            subst.
            unfold cse_invariant; simpls. splits; eauto.
          }
          {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            2: {eapply eq_refl. }
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            {
              rewrite <- TRANSL_CDHP in Heqcdhp_tgt. trivial.
            }
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            {
                rewrite <- AveAI.get_tail_from_i_eq_i_plus_one; 
                rewrite AI_BLK; trivial. 
            }
            rewrite <- AI_BLK in TRSF_BLK.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { (** match ai *)
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                eapply H12 in H11.
                folds AveAI.b.
                rewrite H11.
                eapply always_match_top.
              }
              eapply Ave_B.wf_transf_blk_step in H11; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H11.
              eapply fence_acq_transformed_inst_by_fence_acq in TRSF_INST; eauto.
              rewrite TRSF_INST in H11.
              unfolds Ave_I.transf.
                rewrite <- H11.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.GetExprs (ai)) as ai'.
                destruct ai eqn:EqAi; trivial.
                {
                  subst. 
                  eapply never_match_bot; trivial. 
                }
                {
                  subst. unfolds AveLat.GetExprs. 
                  unfold match_abstract_interp. trivial.
                }
                (** ai = CSet tuples *)
                unfolds match_abstract_interp.
                rewrite Heqai'. unfold AveLat.GetExprs.
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { 
                  pose proof (MATCH_AI tu).
                  rewrite <- EqTu in H2.
                  assert (W.In tu tuples). {
                    eapply W.filter_1 in H2; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                  }
                  apply H3 in H4. rewrite EqTu in H4. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)
                  eapply W.filter_2 in H2. unfolds AveTuple.isExpr. discriminate.
                  eapply (AveTuple.compat_bool_isExpr).
                }
            }
            { (** blk-level fixpoint *)
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H11; eauto.
                folds AveAI.b.
                rewrite H11.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H11; eauto.
              rewrite <- H11. 
              rewrite <- AI_BLK in FIXPOINT. trivial.
            }
            {
              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                {
                  destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                  eapply transf_step_psrv_loc_fact_valid with (bb:=blk_src); eauto.
                  subst analysis_blk.
                  eapply Ave_B.wf_transf_blk_step; eauto.
                  pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                  apply A in ANALYSIS.
                  folds AveAI.b.
                  rewrite ANALYSIS. 
                  eapply top_is_loc_fact_valid.
                }
              }
              trivial.
          }

            { (** mem_injected inj' promises_tgt' *)
              inv LOCAL0. simpls.
              eapply incr_inj_preserve_mem_injected with (inj:=inj); eauto.
              destruct PREEMPT as [(_&EQ_INJ)|(_&INCR_INJ)].
              eapply eq_inj_implies_incr in EQ_INJ; trivial.
              trivial.
            }
        }
        { 
          left.
          splits; eauto.
          unfold eq_inj; intros; tauto.
        }
        {
          eapply Local.program_step_future; eauto.
        }
        { 
          eapply Local.program_step_future; eauto.
        }
        {
          eapply Local.program_step_future; eauto.
        } 
        }
        { 
          destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
          apply eq_inj_implies_incr; trivial.
          trivial.
        }
    }
    { (** fence_sc *)
      inversion H1; simpls.
      inversion INVARIANT. 
      inversion MATCH_LOCAL.
      inversion MATCH_RTL_STATE; simpls.
      rename H2 into SC_EQ_START.
      destruct H3 as (MEM_EQ_START & INJ_MAP_MEM_TGT).

      inversion MATCH_FRAME; simpls.

      remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
      remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
      eapply transform_blk_induction' in TRANSF_BLK; eauto.
      destruct TRANSF_BLK as (inst & b_src' & EqBlkSrc & TRSF).

      destruct TRSF as (TRSF_INST & TRSF_BLK).
      * 
        exists {|
            State.regs :=  regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_tgt' sc_tgt' mem_tgt' inj'.
        splits; eauto.
        { (** fence -> fence  *)
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_fence_sc; eauto.
            eapply fence_sc_transformed_inst_by_fence_sc in TRSF_INST; eauto.
            rewrite <- TRSF_INST; trivial.
            inversion LOCAL.
            rewrite <- H9.
            rewrite MEM_EQ_START.  
            eapply Local.step_fence; eauto.
            (* rewrite <- H9 in LOCAL0; rewrite MEM_EQ_START in LOCAL0.  *)
            assert (lc_tgt = lc_src). {
              eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
            }
            rewrite <- H11. 
            rewrite SC_EQ_START in LOCAL0.
            trivial. 
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            subst.
            unfold cse_invariant; simpls. splits; eauto.
          }
          {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            2: {eapply eq_refl. }
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            {
              rewrite <- TRANSL_CDHP in Heqcdhp_tgt. trivial.
            }
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            {
                rewrite <- AveAI.get_tail_from_i_eq_i_plus_one; 
                rewrite AI_BLK; trivial. 
            }
            rewrite <- AI_BLK in TRSF_BLK.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { (** match ai *)
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                  pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                  eapply H12 in H11.
                  folds AveAI.b.
                  rewrite H11.
                  eapply always_match_top.
              }
              eapply Ave_B.wf_transf_blk_step in H11; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H11.
              eapply fence_sc_transformed_inst_by_fence_sc in TRSF_INST; eauto.
              rewrite TRSF_INST in H11.
              unfolds Ave_I.transf.
                rewrite <- H11.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.GetExprs (ai)) as ai'.
                destruct ai eqn:EqAi; trivial.
                {
                  subst. 
                  eapply never_match_bot; trivial. 
                }
                {
                  subst. unfolds AveLat.GetExprs. 
                  unfold match_abstract_interp. trivial.
                }
                (** ai = CSet tuples *)
                unfolds match_abstract_interp.
                rewrite Heqai'. unfold AveLat.GetExprs.
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { 
                  pose proof (MATCH_AI tu).
                  rewrite <- EqTu in H2.
                  assert (W.In tu tuples). {
                    eapply W.filter_1 in H2; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                  }
                  apply H3 in H4. rewrite EqTu in H4. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)
                  eapply W.filter_2 in H2. unfolds AveTuple.isExpr. discriminate.
                  eapply (AveTuple.compat_bool_isExpr).
                }
            }
            { (** blk-level fixpoint *)
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H11; eauto.
                folds AveAI.b.
                rewrite H11.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H11; eauto.
              rewrite <- H11. 
              rewrite <- AI_BLK in FIXPOINT. trivial.
            }
            {
              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                {
                  destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                  eapply transf_step_psrv_loc_fact_valid with (bb:=blk_src); eauto.
                  subst analysis_blk.
                  eapply Ave_B.wf_transf_blk_step; eauto.
                  pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                  apply A in ANALYSIS.
                  folds AveAI.b.
                  rewrite ANALYSIS. 
                  eapply top_is_loc_fact_valid.
                }
              }
              trivial.
          }

            { (** mem_injected inj' promises_tgt' *)
              inv LOCAL0. simpls.
              eapply incr_inj_preserve_mem_injected with (inj:=inj); eauto.
              destruct PREEMPT as [(_&EQ_INJ)|(_&INCR_INJ)].
              eapply eq_inj_implies_incr in EQ_INJ; trivial.
              trivial.
            }
        }
        { 
          left.
          splits; eauto.
          unfold eq_inj; intros; tauto.
        }
        {
          eapply Local.program_step_future; eauto.
        }
        { 
          eapply Local.program_step_future; eauto.
        }
        {
          eapply Local.program_step_future; eauto.
        } 
        }
        { 
          destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
          apply eq_inj_implies_incr; trivial.
          trivial.
        }
    }
  }
  { (** syscall *)
    inversion H. 
    inv STATE.
    {
      inversion H1; simpls.
      inversion INVARIANT. 
      inversion MATCH_LOCAL.
      inversion MATCH_RTL_STATE; simpls.
      rename H2 into SC_EQ_START.
      destruct H3 as (MEM_EQ_START & INJ_MAP_MEM_TGT).

      inversion MATCH_FRAME; simpls.

      remember (transform_cdhp cdhp_src analysis) as cdhp_tgt.
      remember (transform_blk blk_src (AveAI.br_from_i analysis !! l i)) as blk_tgt.
      eapply transform_blk_induction' in TRANSF_BLK; eauto.
      destruct TRANSF_BLK as (inst & b_src' & EqBlkSrc & TRSF).

      destruct TRSF as (TRSF_INST & TRSF_BLK).
      * 
        exists {|
            State.regs :=  regs_src;
            State.blk := b_src';
            State.cdhp := cdhp_src;
            State.cont := cont_src;
            State.code := code_src
          |} lc_tgt' sc_tgt' mem_tgt' inj'.
        splits; eauto.
        { (** fence -> fence  *)
            eapply Thread.program_step_intro; simpls; eauto.
            eapply State.step_out; eauto.
            eapply out_transformed_inst_by_out in TRSF_INST; eauto.
            rewrite <- TRSF_INST; trivial.
            {
              subst; trivial.
            }
            inversion LOCAL.
            rewrite <- H8.
            rewrite MEM_EQ_START.  
            eapply Local.step_syscall; eauto.
            assert (lc_tgt = lc_src). {
              eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
            }
            rewrite <- H10. 
            rewrite SC_EQ_START in LOCAL0.
            trivial. 
        }
        { (** match state *)
          inversion LOCAL.
          eapply cse_match_state_intro with(inj':=inj'); simpls; eauto.
          { (** invariant *)
            subst.
            unfold cse_invariant; simpls. splits; eauto.
          }
          {
            eapply cse_match_local_state_intro; 
            try rewrite <- H3; eauto.
            2: {eapply eq_refl. }
            eapply cse_match_rtl_state_intro; eauto.
            simpls.
            eapply cse_match_frame_intro with(i:=i+1); eauto.
            rewrite EqBlkSrc in PARTIAL_BLK.
            {
              rewrite <- TRANSL_CDHP in Heqcdhp_tgt. trivial.
            }
            rewrite EqBlkSrc in PARTIAL_BLK.
            eapply bb_from_i_plus_one; eauto.
            {
                rewrite <- AveAI.get_tail_from_i_eq_i_plus_one; 
                rewrite AI_BLK; trivial. 
            }
            rewrite <- AI_BLK in TRSF_BLK.
            rewrite AveAI.get_tail_from_i_eq_i_plus_one in TRSF_BLK; eauto. 
            { (** match ai *)
              destruct ANALYSIS.
              2: { (** case: analysis = top; always match_ai *)
                  pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top). 
                  eapply H11 in H10.
                  folds AveAI.b.
                  rewrite H10.
                  eapply always_match_top.
              }
              rename H10 into H11.
              eapply Ave_B.wf_transf_blk_step in H11; eauto.
              unfolds Ave_B.transf_step.
              rewrite EqBlkSrc in H11.
              eapply out_transformed_inst_by_out in TRSF_INST; eauto.
              rewrite TRSF_INST in H11.
              unfolds Ave_I.transf.
                rewrite <- H11.
                rewrite <- AI_BLK in MATCH_AI.
                subst.
                rewrite MEM_EQ_START.
                remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
                remember (AveLat.GetExprs (ai)) as ai'.
                destruct ai eqn:EqAi; trivial.
                {
                  subst. 
                  eapply never_match_bot; eauto. 
                }
                {
                  subst. unfolds AveLat.GetExprs. 
                  unfold match_abstract_interp. trivial.
                }
                (** ai = CSet tuples *)
                unfolds match_abstract_interp.
                rewrite Heqai'. unfold AveLat.GetExprs.
                intros.
                unfolds match_abstract_fact.
                destruct tu eqn:EqTu.
                { 
                  pose proof (MATCH_AI tu).
                  rewrite <- EqTu in H2.
                  assert (W.In tu tuples). {
                    eapply W.filter_1 in H2; trivial.
                    eapply (AveTuple.compat_bool_isExpr).
                  }
                  apply H3 in H4. rewrite EqTu in H4. trivial.
                }
                { (** proof for: (r, x) in ai' is still correct *)
                  eapply W.filter_2 in H2. unfolds AveTuple.isExpr. discriminate.
                  eapply (AveTuple.compat_bool_isExpr).
                }
            }
            { (** blk-level fixpoint *)
              eapply subblk_same_succ in EqBlkSrc.
              rewrite <- EqBlkSrc; trivial.
              destruct ANALYSIS.
              2: {
                intros.
                eapply (AveAI.get_head_from_eval) with (l:=lp) in H10; eauto.
                folds AveAI.b.
                rewrite H10.
                eapply AveLat.ge_top.
              }
              eapply Ave_B.wf_transf_blk_getlast in H10; eauto.
              rewrite <- H10. 
              rewrite <- AI_BLK in FIXPOINT. trivial.
            }
            {
              assert (loc_fact_valid (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))).  {
                {
                  destruct ANALYSIS as [ANALYSIS | ANALYSIS].
                  eapply transf_step_psrv_loc_fact_valid with (bb:=blk_src); eauto.
                  subst analysis_blk.
                  eapply Ave_B.wf_transf_blk_step; eauto.
                  pose proof (AveAI.get_first_from_eval analysis l (i+1) AveLat.top) as A.
                  apply A in ANALYSIS.
                  folds AveAI.b.
                  rewrite ANALYSIS. 
                  eapply top_is_loc_fact_valid.
                }
              }
              trivial.
          }

            { (** mem_injected inj' promises_tgt' *)
              inv LOCAL0. simpls.
              eapply incr_inj_preserve_mem_injected with (inj:=inj); eauto.
              destruct PREEMPT as [(_&EQ_INJ)|(_&INCR_INJ)].
              eapply eq_inj_implies_incr in EQ_INJ; trivial.
              trivial.
            }
        }
        { 
          left.
          splits; eauto.
          unfold eq_inj; intros; tauto.
        }
        {
          eapply Local.program_step_future; eauto.
        }
        { 
          eapply Local.program_step_future; eauto.
        }
        {
          eapply Local.program_step_future; eauto.
        } 
        }
        { 
          destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
          apply eq_inj_implies_incr; trivial.
          trivial.
        }
   }
  }
  Unshelve. eauto. 
  exact TView.bot.
  trivial.
  trivial.
  trivial.
  exact TView.bot.
  trivial.
  trivial.
  trivial.
  exact TView.bot.
  trivial.
  trivial.
Qed.

(** Correctness of promise transition *)
Theorem cse_match_state_preserving_prm:
  forall te lo inj st_tgt st_src sc_tgt lc_src lc_tgt mem_tgt sc_src mem_src b st_tgt' lc_tgt' sc_tgt' mem_tgt', 
    Thread.promise_step false te 
        (@Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) 
        (@Thread.mk rtl_lang st_tgt' lc_tgt' sc_tgt' mem_tgt') 
    ->   
    (cse_match_state inj lo 
      (Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) 
      (Thread.mk rtl_lang st_src lc_src sc_src mem_src) b)
    -> 
      (exists st_src' lc_src' sc_src' mem_src' inj',
          Thread.promise_step false te (@Thread.mk rtl_lang st_src lc_src sc_src mem_src) 
                                    (@Thread.mk rtl_lang st_src' lc_src' sc_src' mem_src') 
          /\
          (cse_match_state inj' lo 
          (Thread.mk rtl_lang st_tgt' lc_tgt' sc_tgt' mem_tgt') (Thread.mk rtl_lang st_src' lc_src' sc_src' mem_src') true)
          /\ 
          incr_inj inj inj'
      ).
Proof.
  intros.
  destruct st_tgt as (regs_tgt, blk_tgt, cdhp_tgt, cont_tgt, code_tgt) eqn:EqStTgt.
  destruct st_tgt' as (regs_tgt', blk_tgt', cdhp_tgt', cont_tgt', code_tgt') eqn:EqStTgt'.
  destruct st_src as (regs_src, blk_src, cdhp_src, cont_src, code_src) eqn:EqStSrc; simpls.
  inversion H0.
  inversion MATCH_LOCAL.
  simpls.
  inversion H.
  inversion LOCAL.
  inversion PROMISE.
  { (** add *)
    exists st_src lc_tgt'.
    do 2 eexists.
    pose proof (classic (msg = Message.reserve)). 
    destruct H16 as [RSV_MSG | NOT_RSV].
    { 
    (** MSG is RSV *) 
      exists inj'; eauto.
      (** FIXME: may equal proof *)
      splits; eauto.
      { (** tgt promise step -> src promise step *)
        inversion H.
        inversion LOCAL.
        inversion INVARIANT. simpls. destruct H16.
        subst.
        eapply Thread.promise_step_intro; eauto.
        eapply Local.promise_step_intro with (promises2:=promises2); eauto.
        rewrite <- PROMISES_EQ. destruct H31. rewrite <- H1; trivial.
        rewrite <- TVIEW_EQ; trivial.
      }
       (** match state preserve *)
       inversion H.
       inversion LOCAL.
       inversion INVARIANT. simpls. 
       destruct H31.
       rewrite EqStSrc.
       rewrite <- H18. rewrite H14.
       eapply cse_match_state_intro with (inj':=inj'); simpls; eauto.
       {
         rewrite <- H14.
         unfold cse_invariant; splits; simpls; eauto.
         unfolds eq_ident_mapping.
         destruct H32.
         split.
         2: {
           intros.
           apply H33 in H34. trivial.
         }
         { (** dom equal: no new reserve msg *)
            eapply promise_resv_preserve_mem_inj_dom_eq; eauto.
         }
       }
       {
         inv MATCH_RTL_STATE; simpls.
         inv MATCH_FRAME; simpls.
         eapply cse_match_local_state_intro; simpls; eauto.
         eapply cse_match_rtl_state_intro; simpls; eauto.
         eapply cse_match_frame_intro; simpls; eauto.
         { 
           remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
           unfolds match_abstract_interp.
           destruct ai eqn:EqAi; eauto.
           intros.
           unfolds match_abstract_fact.
           destruct tu eqn:EqTu; eauto.
           - pose proof (MATCH_AI tu).
             rewrite EqTu in H2. apply H2 in H1; trivial.
           - 
             pose proof (MATCH_AI tu).
             rewrite EqTu in H2. 
             apply H2 in H1; trivial. destruct H1; splits; eauto.
             
             destruct H3 as (t & f & R & PLN & RLX & MSG).
             assert (lc_tgt = lc_src). {
              eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
              }
              rewrite H3.
 
               assert (Memory.future mem_tgt mem_tgt'). {
                 inversion LOCAL_WF.
                 eapply Memory.promise_future; eauto.
               }
               clear H3; rename H4 into H3.
               rewrite H31 in H3.
               eapply Memory.future_get1 in H3; eauto. 
               destruct H3 as (f' &  m' & MSG' & TLE & MLE); eauto.
               inversion MLE.
               rewrite <- H3 in MSG'.
               do 3 eexists. splits; eauto.
               (* rewrite TVIEW_EQ. *)
               rewrite MSG'.
               eapply f_equal.

               rewrite H5.
               subst.
               econs.
         } 
         { 
           eapply eq_refl.
         }
         { (** still mem_injected *)
           assert (incr_inj inj inj'). {
             destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
             eapply eq_inj_implies_incr; trivial.
             trivial.
           }
           eapply incr_inj_preserve_mem_injected in H1; eauto.
           assert (promises2 = promises0). {inv LC0. trivial. }
           rewrite H2.
           eapply promise_resv_keeps_promises_injected; eauto.
         }
       }
       {
         left.
         splits; trivial.
         eapply eq_inj_refl.
       }
       {
         eapply Local.promise_step_future; eauto.
       }
       {
         eapply Memory.promise_closed_timemap; eauto. 
         rewrite <- H14. trivial.
       }
       {
         assert (Memory.future mem_tgt mem_tgt'). {
           inversion LOCAL_WF.
           eapply Memory.promise_future; eauto.
         }
         eapply Memory.future_closed; eauto.
       }
       {
         destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
         eapply eq_inj_implies_incr; trivial.
         trivial.
       }
     }
    (** msg is not RSV *)
    {
      remember (fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else (inj' loc1 to1)) as inj''. 
      exists (inj''); eauto.
      splits; eauto.
      { (** tgt promise step -> src promise step *)
        inversion H.
        inversion LOCAL.
        inversion INVARIANT. simpls. destruct H16.
        subst.
        eapply Thread.promise_step_intro; eauto.
        eapply Local.promise_step_intro with (promises2:=promises2); eauto.
        rewrite <- PROMISES_EQ. destruct H31. rewrite <- H1; trivial.
        rewrite <- TVIEW_EQ; trivial.
      }
      { (** match state preserve *)
        inversion H.
        inversion LOCAL.
        inversion INVARIANT. simpls. 
        destruct H31.
        rewrite EqStSrc.
        rewrite <- H18. rewrite H14.
        eapply cse_match_state_intro with (inj':=inj''); simpls; eauto.
        {
          rewrite <- H14.
          unfold cse_invariant; splits; simpls; eauto.
          unfolds eq_ident_mapping.
          destruct H32.
          split.
          2: {
            intros.
            rewrite Heqinj'' in H34.
            (* remember (loc_ts_eq_dec (loc, to) (loc1, t)) as LOC_TS_EQ. *)
            des_ifH H34; simpls.
            2: {
              destruct o.
              apply H33 in H34. trivial.
              apply H33 in H34. trivial.
            }
            { 
              destruct a.
              inv H34. apply eq_refl.
            }
          }
          { (** dom equal *)
            eapply prm_add_incr_mem_with_inj; eauto.
          }
        }
        {
          inv MATCH_RTL_STATE; simpls.
          inv MATCH_FRAME; simpls.
          eapply cse_match_local_state_intro; simpls; eauto.
          eapply cse_match_rtl_state_intro; simpls; eauto.
          eapply cse_match_frame_intro; simpls; eauto.
          { 
            remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
            unfolds match_abstract_interp.
            destruct ai eqn:EqAi; eauto.
            intros.
            unfolds match_abstract_fact.
            destruct tu eqn:EqTu; eauto.
            - pose proof (MATCH_AI tu).
              rewrite EqTu in H2. apply H2 in H1; trivial.
            -   
              pose proof (MATCH_AI tu).
              rewrite EqTu in H2. 
              apply H2 in H1; trivial. destruct H1; splits; eauto.
              
              destruct H3 as (t & f & R & PLN & RLX & MSG).
              assert (lc_tgt = lc_src). {
                eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                }
                rewrite H3.
   
                 assert (Memory.future mem_tgt mem_tgt'). {
                   inversion LOCAL_WF.
                   eapply Memory.promise_future; eauto.
                 }
                 clear H3; rename H4 into H3.
                 rewrite H31 in H3.
                 eapply Memory.future_get1 in H3; eauto. 
                 destruct H3 as (f' &  m' & MSG' & TLE & MLE); eauto.
                 inversion MLE.
                 rewrite <- H3 in MSG'.
                 do 3 eexists. splits; eauto.
                 (* rewrite TVIEW_EQ. *)
                 rewrite MSG'.
                 eapply f_equal.
  
                 rewrite H5.
                 subst.
                 econs.
          } 
          { 
            eapply eq_refl.
          }
          { (** still mem_injected *)
            assert (incr_inj inj inj'). {
              destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
              eapply eq_inj_implies_incr; trivial.
              trivial.
            }
            eapply incr_inj_preserve_mem_injected in H1; eauto.
            assert (promises2 = promises0). {inv LC0. trivial. }
            rewrite H2.
            eapply prm_add_keeps_promises_injected; eauto.
          }
        }
        {
          left.
          splits; trivial.
          eapply eq_inj_refl.
        }
        {
          eapply Local.promise_step_future; eauto.
        }
        {
          eapply Memory.promise_closed_timemap; eauto. 
          rewrite <- H14. trivial.
        }
        {
          assert (Memory.future mem_tgt mem_tgt'). {
            inversion LOCAL_WF.
            eapply Memory.promise_future; eauto.
          }
          eapply Memory.future_closed; eauto.
        }
      }
      {
        assert (incr_inj inj' inj''). {
          unfolds incr_inj.
          intros.
          rewrite Heqinj''.
          des_ifs. destruct a. simpls.
          rewrite <- H2 in H16.
          inv INVARIANT.
          destruct H4.
          unfolds eq_ident_mapping; simpls. destruct H2.
          apply H4 in H16. apply f_equal. trivial.
        }
        destruct PREEMPT as [EQ_INJ|INCR_INJ].
        destruct EQ_INJ as (_ & EQ_INJ).
        apply eq_inj_implies_incr in EQ_INJ.
        eapply incr_inj_transitivity; eauto.
        destruct INCR_INJ as (_ & EQ_INJ).
        eapply incr_inj_transitivity; eauto.
      }
    }
  }
  { (** split *)
    exists st_src lc_tgt'.
    do 2 eexists.
    pose proof (classic (msg = Message.reserve)). 
    destruct H16 as [RSV_MSG | NOT_RSV].
    { (** msg cannot be RSV *)
      inv PROMISES. destruct RESERVE as (val' & R' & G).
      try discriminate.
    }
    (** split concrete msg: add one, change another's [from] *)
    { 
        remember (fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else (inj' loc1 to1)) as inj''. 
        exists (inj''); eauto.
        splits; eauto.
        { (** tgt promise step -> src promise step *)
          inversion H.
          inversion LOCAL.
          inversion INVARIANT. simpls. destruct H16.
          subst.
          eapply Thread.promise_step_intro; eauto.
          eapply Local.promise_step_intro with (promises2:=promises2); eauto.
          rewrite <- PROMISES_EQ. destruct H31. rewrite <- H1; trivial.
          rewrite <- TVIEW_EQ; trivial.
        }
        (** match state preserve *)
         inversion H.
         inversion LOCAL.
         inversion INVARIANT. simpls. 
         destruct H31.
         rewrite EqStSrc.
         rewrite <- H18. rewrite H14.
         eapply cse_match_state_intro with (inj':=inj''); simpls; eauto.
         {
           rewrite <- H14.
           unfold cse_invariant; splits; simpls; eauto.
           unfolds eq_ident_mapping.
           destruct H32.
           split.
           2: {
             intros.
             rewrite Heqinj'' in H34.
             des_ifH H34; simpls.
             { 
               destruct a. subst. 
                inv H34. 
                eapply eq_refl.
             }
             apply H33 in H34. trivial.
           }
           { (** dom equal*)
              eapply prm_split_incr_mem_with_inj; eauto.
           }
         }
         {
           inv MATCH_RTL_STATE; simpls.
           inv MATCH_FRAME; simpls.
           eapply cse_match_local_state_intro; simpls; eauto.
           eapply cse_match_rtl_state_intro; simpls; eauto.
           eapply cse_match_frame_intro; simpls; eauto.
           { 
             remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
             unfolds match_abstract_interp.
             destruct ai eqn:EqAi; eauto.
             intros.
             unfolds match_abstract_fact.
             destruct tu eqn:EqTu; eauto.
             - pose proof (MATCH_AI tu).
               rewrite EqTu in H2. apply H2 in H1; trivial.
             - 
               pose proof (MATCH_AI tu).
               rewrite EqTu in H2. 
               apply H2 in H1; trivial. destruct H1; splits; eauto. clear H1. rename H3 into H1.
               rename H1 into H3.

               destruct H3 as (t & f & R & PLN & RLX & MSG).
               assert (lc_tgt = lc_src). {
                 eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                 }
                 rewrite H1.
    
                  assert (Memory.future mem_tgt mem_tgt'). {
                    inversion LOCAL_WF.
                    eapply Memory.promise_future; eauto.
                  }
                  rewrite H31 in H3.
                  eapply Memory.future_get1 in H3; eauto. 
                  destruct H3 as (f' &  m' & MSG' & TLE & MLE); eauto.
                  inversion MLE.
                  rewrite <- H3 in MSG'.
                  do 3 eexists. splits; eauto.
                  rewrite MSG'.
                  eapply f_equal.
   
                  rewrite H5.
                  subst.
                  econs.
           } 
           { 
             eapply eq_refl.
           }
           { (** still promises injected *)
             assert (incr_inj inj inj'). {
               destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
               eapply eq_inj_implies_incr; trivial.
               trivial.
             }
             eapply incr_inj_preserve_mem_injected in H1; eauto.
             assert (promises2 = promises0). {inv LC0. trivial. }
             rewrite H2.
              eapply prm_split_keeps_promises_injected; eauto.
           }
         }
         {
           left.
           splits; trivial.
           eapply eq_inj_refl.
         }
         {
           eapply Local.promise_step_future; eauto.
         }
         {
           eapply Memory.promise_closed_timemap; eauto. 
           rewrite <- H14. trivial.
         }
         {
           assert (Memory.future mem_tgt mem_tgt'). {
             inversion LOCAL_WF.
             eapply Memory.promise_future; eauto.
           }
           eapply Memory.future_closed; eauto.
         }
         {
            assert (incr_inj inj' inj''). {
              unfolds incr_inj.
              intros.
              rewrite Heqinj''.
              des_ifs. destruct a. simpls.
              rewrite <- H2 in H16.
              inv INVARIANT.
              destruct H4.
              unfolds eq_ident_mapping; simpls. destruct H2.
              apply H4 in H16. apply f_equal. trivial.
            }
            destruct PREEMPT as [EQ_INJ|INCR_INJ].
            destruct EQ_INJ as (_ & EQ_INJ).
            apply eq_inj_implies_incr in EQ_INJ.
            eapply incr_inj_transitivity; eauto.
            destruct INCR_INJ as (_ & EQ_INJ).
            eapply incr_inj_transitivity; eauto.
         }
    }
  }
  { (** lower *)
    exists st_src lc_tgt'.
    do 2 eexists.
    pose proof (classic (msg = Message.reserve)). 
    destruct H16 as [RSV_MSG | NOT_RSV].
    { (** msg cannot be RSV *)
      inv PROMISES. destruct RESERVE as (val' & R' & G).
      inversion LOWER.
      rewrite G in MSG_LE.
      inversion MSG_LE.
    }
    (** concrete msg: need not change inj, msg's timestamp not changed *)
    {
      exists inj'; eauto.
      (** FIXME: may equal proof *)
      splits; eauto.
      { (** tgt promise step -> src promise step *)
        inversion H.
        inversion LOCAL.
        inversion INVARIANT. simpls. destruct H16.
        subst.
        eapply Thread.promise_step_intro; eauto.
        eapply Local.promise_step_intro with (promises2:=promises2); eauto.
        rewrite <- PROMISES_EQ. destruct H31. rewrite <- H1; trivial.
        rewrite <- TVIEW_EQ; trivial.
      }
      (** match state preserve *)
       inversion H.
       inversion LOCAL.
       inversion INVARIANT. simpls. 
       destruct H31.
       rewrite EqStSrc.
       rewrite <- H18. rewrite H14.
       eapply cse_match_state_intro with (inj':=inj'); simpls; eauto.
       {
         rewrite <- H14.
         unfold cse_invariant; splits; simpls; eauto.
         unfolds eq_ident_mapping.
         destruct H32.
         split.
         2: {
           intros.
           apply H33 in H34. trivial.
         }
         { (** dom equal: no new reserve msg *)
            (* eapply promise_resv_preserve_mem_inj_dom_eq; eauto. *)
            eapply prm_lower_keeps_mem_inj_dom_eq; eauto.
         }
       }
       {
         inv MATCH_RTL_STATE; simpls.
         inv MATCH_FRAME; simpls.
         eapply cse_match_local_state_intro; simpls; eauto.
         eapply cse_match_rtl_state_intro; simpls; eauto.
         eapply cse_match_frame_intro; simpls; eauto.
         { 
           remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
           unfolds match_abstract_interp.
           destruct ai eqn:EqAi; eauto.
           intros.
           unfolds match_abstract_fact.
           destruct tu eqn:EqTu; eauto.
           - pose proof (MATCH_AI tu).
             rewrite EqTu in H2. apply H2 in H1; trivial.
           - 
             pose proof (MATCH_AI tu).
             rewrite EqTu in H2. 
             apply H2 in H1; trivial. destruct H1; splits; eauto. clear H1; rename H3 into H1.
             rename H1 into H3.

             destruct H3 as (t & f & R & PLN & RLX & MSG).
             assert (lc_tgt = lc_src). {
               eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
               }
               rewrite H1.
  
                assert (Memory.future mem_tgt mem_tgt'). {
                  inversion LOCAL_WF.
                  eapply Memory.promise_future; eauto.
                }
                rewrite H31 in H3.
                eapply Memory.future_get1 in H3; eauto. 
                destruct H3 as (f' &  m' & MSG' & TLE & MLE); eauto.
                inversion MLE.
                rewrite <- H3 in MSG'.
                do 3 eexists. splits; eauto.
                rewrite MSG'.
                eapply f_equal.
 
                rewrite H5.
                subst.
                econs.
         } 
         { 
           eapply eq_refl.
         }
         { (** still promises injected *)
           assert (incr_inj inj inj'). {
             destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
             eapply eq_inj_implies_incr; trivial.
             trivial.
           }
           eapply incr_inj_preserve_mem_injected in H1; eauto.
           assert (promises2 = promises0). {inv LC0. trivial. }
           rewrite H2.
           eapply prm_lower_keeps_promises_injected; eauto.
         }
       }
       {
         left.
         splits; trivial.
         eapply eq_inj_refl.
       }
       {
         eapply Local.promise_step_future; eauto.
       }
       {
         eapply Memory.promise_closed_timemap; eauto. 
         rewrite <- H14. trivial.
       }
       {
         assert (Memory.future mem_tgt mem_tgt'). {
           inversion LOCAL_WF.
           eapply Memory.promise_future; eauto.
         }
         eapply Memory.future_closed; eauto.
       }
       {
         destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
         eapply eq_inj_implies_incr; trivial.
         trivial.
       }
    }
  }
  { (** remove *)
    exists st_src lc_tgt'.
    do 2 eexists.
    pose proof (classic (msg = Message.reserve)). 
    destruct H16 as [RSV_MSG | NOT_RSV].
    2: { (** msg cannot to concrete *)
      rewrite RESERVE in NOT_RSV. try contradiction.
    }
    { (** remove a reserve msg, no need to change inj *)
      exists inj'; eauto.
      (** FIXME: may equal proof *)
      splits; eauto.
      { (** tgt promise step -> src promise step *)
        inversion H.
        inversion LOCAL.
        inversion INVARIANT. simpls. destruct H16.
        subst.
        eapply Thread.promise_step_intro; eauto.
        eapply Local.promise_step_intro with (promises2:=promises2); eauto.
        rewrite <- PROMISES_EQ. destruct H31. rewrite <- H1; trivial.
        rewrite <- TVIEW_EQ; trivial.
      }
      (** match state preserve *)
       inversion H.
       inversion LOCAL.
       inversion INVARIANT. simpls. 
       destruct H31.
       rewrite EqStSrc.
       rewrite <- H18. rewrite H14.
       eapply cse_match_state_intro with (inj':=inj'); simpls; eauto.
       {
         rewrite <- H14.
         unfold cse_invariant; splits; simpls; eauto.
         unfolds eq_ident_mapping.
         destruct H32.
         split.
         2: {
           intros.
           apply H33 in H34. trivial.
         }
         { (** dom equal: no new reserve msg *)
            eapply promise_resv_preserve_mem_inj_dom_eq; eauto.
         }
       }
       {
         inv MATCH_RTL_STATE; simpls.
         inv MATCH_FRAME; simpls.
         eapply cse_match_local_state_intro; simpls; eauto.
         eapply cse_match_rtl_state_intro; simpls; eauto.
         eapply cse_match_frame_intro; simpls; eauto.
         { 
           remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
           unfolds match_abstract_interp.
           destruct ai eqn:EqAi; eauto.
           intros.
           unfolds match_abstract_fact.
           destruct tu eqn:EqTu; eauto.
           - pose proof (MATCH_AI tu).
             rewrite EqTu in H2. apply H2 in H1; trivial.
           - 
             pose proof (MATCH_AI tu).
             rewrite EqTu in H2. 
             apply H2 in H1; trivial. destruct H1; splits; eauto. clear H1; rename H3 into H1. 
             rename H1 into H3.

             destruct H3 as (t & f & R & PLN & RLX & MSG).
             assert (lc_tgt = lc_src). {
               eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
               }
               rewrite H1.
  
                assert (Memory.future mem_tgt mem_tgt'). {
                  inversion LOCAL_WF.
                  eapply Memory.promise_future; eauto.
                }
                rewrite H31 in H3.
                eapply Memory.future_get1 in H3; eauto. 
                destruct H3 as (f' &  m' & MSG' & TLE & MLE); eauto.
                inversion MLE.
                rewrite <- H3 in MSG'.
                do 3 eexists. splits; eauto.
                rewrite MSG'.
                eapply f_equal.
 
                rewrite H5.
                subst.
                econs.
         } 
         { 
           eapply eq_refl.
         }
         { (** still mem_injected *)
           assert (incr_inj inj inj'). {
             destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
             eapply eq_inj_implies_incr; trivial.
             trivial.
           }
           eapply incr_inj_preserve_mem_injected in H1; eauto.
           assert (promises2 = promises0). {inv LC0. trivial. }
           rewrite H2.

           eapply promise_ccl_keeps_promises_injected; eauto.
         }
       }
       {
         left.
         splits; trivial.
         eapply eq_inj_refl.
       }
       {
         eapply Local.promise_step_future; eauto.
       }
       {
         eapply Memory.promise_closed_timemap; eauto. 
         rewrite <- H14. trivial.
       }
       {
         assert (Memory.future mem_tgt mem_tgt'). {
           inversion LOCAL_WF.
           eapply Memory.promise_future; eauto.
         }
         eapply Memory.future_closed; eauto.
       }
       {
         destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
         eapply eq_inj_implies_incr; trivial.
         trivial.
       }
    }
  }
Qed.

Theorem cse_match_state_preserving_pf_prm:
  forall lo inj st_tgt st_src sc_tgt lc_src lc_tgt mem_tgt sc_src mem_src b st_tgt' lc_tgt' sc_tgt' mem_tgt', 
    Thread.pf_promise_step 
        (@Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) 
        (@Thread.mk rtl_lang st_tgt' lc_tgt' sc_tgt' mem_tgt') 
    ->   
    (cse_match_state inj lo 
      (Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) 
      (Thread.mk rtl_lang st_src lc_src sc_src mem_src) b)
    -> 
      (exists st_src' lc_src' sc_src' mem_src',
          Thread.pf_promise_step (@Thread.mk rtl_lang st_src lc_src sc_src mem_src) 
                                    (@Thread.mk rtl_lang st_src' lc_src' sc_src' mem_src') 
          /\
          (cse_match_state inj lo 
          (Thread.mk rtl_lang st_tgt' lc_tgt' sc_tgt' mem_tgt') (Thread.mk rtl_lang st_src' lc_src' sc_src' mem_src') b)
      ).
Proof.
  intros.
  destruct st_tgt as (regs_tgt, blk_tgt, cdhp_tgt, cont_tgt, code_tgt) eqn:EqStTgt.
  destruct st_tgt' as (regs_tgt', blk_tgt', cdhp_tgt', cont_tgt', code_tgt') eqn:EqStTgt'.
  destruct st_src as (regs_src, blk_src, cdhp_src, cont_src, code_src) eqn:EqStSrc; simpls.
  inversion H0.
  inversion MATCH_LOCAL.
  simpls.
  inversion H.
  inversion PF_STEP.
  inversion LOCAL.
  inversion PROMISE.
  { (** not add *)
    rewrite <- H3 in PF. simpls. discriminate.
  }
  { (** split *)
    rewrite <- H3 in PF. simpls. discriminate.  
  }
  { (** lower *)
    exists st_src lc_tgt' sc_src mem_tgt'.
    pose proof (classic (msg = Message.reserve)). 
    destruct H16 as [RSV_MSG | NOT_RSV].
    { (** msg cannot be RSV *)
      inv PROMISES. destruct RESERVE as (val' & R' & G).
      inversion LOWER.
      rewrite G in MSG_LE.
      inversion MSG_LE.
    }
    (** concrete msg: need not change inj, msg's timestamp not changed *)
    {
      (** FIXME: may equal proof *)
      splits; eauto.
      { (** tgt promise step -> src promise step *) 
        inversion H.
        inversion PF_STEP0.
        inversion LOCAL.
        inversion INVARIANT. simpls. destruct H31.
        subst.
        eapply Thread.pf_promise_step_intro; eauto.
        eapply Thread.promise_step_intro with (loc:=loc) (from:=from) (to:=to) (kind:= Memory.op_kind_lower msg0); eauto.
        assert (lc_tgt = lc_src). {
          eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
        }
        rewrite <- H31.
        rewrite <- H1. 
        eapply Local.promise_step_intro with (promises2:=promises0); eauto.    
    }
      (** match state preserve *)
       inversion H.
       inversion LOCAL.
       inversion INVARIANT. simpls. 
       destruct H17.
       rewrite EqStSrc.
       (* rewrite <- H18.  *)
       (* rewrite H14. *)
       eapply cse_match_state_intro with (inj':=inj'); simpls; eauto.
       {
         rewrite <- H14.
         unfold cse_invariant; splits; simpls; eauto.
         unfolds eq_ident_mapping.
         destruct H18.
         split.
         2: {
           intros.
           apply H19 in H20. trivial.
         }
         { (** dom equal: no new reserve msg *)
            (* eapply promise_resv_preserve_mem_inj_dom_eq; eauto. *)
            eapply prm_lower_keeps_mem_inj_dom_eq; eauto.
         }
       }
       {
         inv MATCH_RTL_STATE; simpls.
         inv MATCH_FRAME; simpls.
         eapply cse_match_local_state_intro; simpls; eauto.
         eapply cse_match_rtl_state_intro; simpls; eauto.
         eapply cse_match_frame_intro; simpls; eauto.
         { 
           remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
           unfolds match_abstract_interp.
           destruct ai eqn:EqAi; eauto.
           intros.
           unfolds match_abstract_fact.
           destruct tu eqn:EqTu; eauto.
           - pose proof (MATCH_AI tu).
             rewrite EqTu in H2. apply H2 in H1; trivial.
           - 
             pose proof (MATCH_AI tu).
             rewrite EqTu in H2. 
             apply H2 in H1; trivial. destruct H1; splits; eauto. clear H1; rename H3 into H1.
             rename H1 into H3.

             destruct H3 as (t & f & R & PLN & RLX & MSG).
             assert (lc_tgt = lc_src). {
               eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
               }
               rewrite H1.
  
                assert (Memory.future mem_tgt mem_tgt'). {
                  inversion LOCAL_WF.
                  eapply Memory.promise_future; eauto.
                }
                rewrite H17 in H3.
                eapply Memory.future_get1 in H3; eauto. 
                destruct H3 as (f' &  m' & MSG' & TLE & MLE); eauto.
                inversion MLE.
                rewrite <- H3 in MSG'.
                do 3 eexists. splits; eauto.
                rewrite MSG'.
                eapply f_equal.
 
                rewrite H5.
                subst.
                econs.
         } 
         { 
           eapply eq_refl.
         }
         { (** still promises injected *)
           assert (incr_inj inj inj'). {
             destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
             eapply eq_inj_implies_incr; trivial.
             trivial.
           }
           eapply incr_inj_preserve_mem_injected in H1; eauto.
           assert (promises2 = promises0). {inv LC0. trivial. }
           rewrite H2.
           eapply prm_lower_keeps_promises_injected; eauto.
         }
       }
       {
         eapply Local.promise_step_future; eauto.
       }
       {
         eapply Memory.promise_closed_timemap; eauto. 
         rewrite <- H14. trivial.
       }
       {
         assert (Memory.future mem_tgt mem_tgt'). {
           inversion LOCAL_WF.
           eapply Memory.promise_future; eauto.
         }
         eapply Memory.future_closed; eauto.
       }
    }
  }
  { (** cancel *)
      exists st_src lc_tgt' sc_src mem_tgt'.
      pose proof (classic (msg = Message.reserve)). 
      destruct H16 as [RSV_MSG | NOT_RSV].
      2: { (** msg cannot to concrete *)
        rewrite RESERVE in NOT_RSV. try contradiction.
      }
      { (** remove a reserve msg, no need to change inj *)
        splits; eauto.
        { (** tgt promise step -> src promise step *) 
          inversion H.
          inversion PF_STEP0.
          inversion LOCAL.
          inversion INVARIANT. simpls. destruct H16.
          subst.
          eapply Thread.pf_promise_step_intro; eauto.
          eapply Thread.promise_step_intro with (kind:= Memory.op_kind_cancel); eauto.
          (* inv PF0. *)
          destruct H31. rewrite <- n; trivial.
          assert (lc_tgt = lc_src). {
            eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
          }
          rewrite <- H1. 
          eapply Local.promise_step_intro with (promises2:=promises0); eauto.
        }
        (** match state preserve *)
        inversion H.
        inversion PF_STEP0.

        inversion LOCAL.
        inversion INVARIANT. simpls. 
        destruct H31.
        rewrite EqStSrc.
        rewrite <- H18. rewrite H14.
        eapply cse_match_state_intro with (inj':=inj'); simpls; eauto.
        {
          rewrite <- H14.
          unfold cse_invariant; splits; simpls; eauto.
          unfolds eq_ident_mapping.
          destruct H32.
          split.
          2: {
            intros.
            apply H33 in H34. trivial.
          }
          { (** dom equal: no new reserve msg *)
              eapply promise_resv_preserve_mem_inj_dom_eq; eauto.
          }
        }
        {
          inv MATCH_RTL_STATE; simpls.
          inv MATCH_FRAME; simpls.
          eapply cse_match_local_state_intro; simpls; eauto.
          eapply cse_match_rtl_state_intro; simpls; eauto.
          eapply cse_match_frame_intro; simpls; eauto.
          { 
            remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
            unfolds match_abstract_interp.
            destruct ai eqn:EqAi; eauto.
            intros.
            unfolds match_abstract_fact.
            destruct tu eqn:EqTu; eauto.
            - pose proof (MATCH_AI tu).
              rewrite EqTu in H2. apply H2 in H1; trivial.
            - 
              pose proof (MATCH_AI tu).
              rewrite EqTu in H2. 
              apply H2 in H1; trivial. destruct H1; split; eauto. clear H1; rename H3 into H1.
              rename H1 into H3.

              destruct H3 as (t & f & R & PLN & RLX & MSG).
              assert (lc_tgt = lc_src). {
                eapply cse_match_local_state_implies_eq_local in MATCH_LOCAL; eauto.
                }
                rewrite H1.
   
                 assert (Memory.future mem_tgt mem_tgt'). {
                   inversion LOCAL_WF.
                   eapply Memory.promise_future; eauto.
                 }
                 rewrite H31 in H3.
                 eapply Memory.future_get1 in H3; eauto. 
                 destruct H3 as (f' &  m' & MSG' & TLE & MLE); eauto.
                 inversion MLE.
                 rewrite <- H3 in MSG'.
                 do 3 eexists. splits; eauto.
                 rewrite MSG'.
                 eapply f_equal.
  
                 rewrite H5.
                 subst.
                 econs.
          } 
          { 
            eapply eq_refl.
          }
          { (** still mem_injected *)
            assert (incr_inj inj inj'). {
              destruct PREEMPT as [(_&EQ_INJ) | (_&INCR_INJ)].
              eapply eq_inj_implies_incr; trivial.
              trivial.
            }
            eapply incr_inj_preserve_mem_injected in H1; eauto.
            assert (promises2 = promises0). {inv LC0. trivial. }
            rewrite H2.

            eapply promise_ccl_keeps_promises_injected; eauto.
          }
        }
        {
          eapply Local.promise_step_future; eauto.
        }
        {
          eapply Memory.promise_closed_timemap; eauto. 
          rewrite <- H14. trivial.
        }
        {
          assert (Memory.future mem_tgt mem_tgt'). {
            inversion LOCAL_WF.
            eapply Memory.promise_future; eauto.
          }
          eapply Memory.future_closed; eauto.
        }
      }
    }
Qed.

Theorem incr_mem_preserve_match_ai:
forall regs tview mem ai lo mem',
    match_abstract_interp regs tview mem ai lo
    -> 
    concrete_mem_incr mem mem'
    -> 
    match_abstract_interp regs tview mem' ai lo.
Proof.
    intros.
    unfolds match_abstract_interp.
    destruct ai eqn:EqAi; eauto.
    intros.
    apply H in H1.
    clear H.
    unfolds match_abstract_fact.
    destruct tu eqn:EqTu; eauto. destruct H1; splits; eauto.
    unfolds concrete_mem_incr. clear H. rename H1 into H.
    destruct H as (t & f & R & PLN & RLX & MSG).

    pose proof (H0 loc f t (regs reg) R).
    apply H in MSG.
    destruct MSG as (f' & R' & _ & _ & MSG' & _).
    exists t f' R'. 
    splits; eauto.
Qed.

(** proof for rely transition *)
Theorem cse_match_state_preserving_rely:
  forall lo inj inj' st_tgt st_src sc_tgt lc_src lc_tgt mem_tgt sc_src mem_src 
         sc_tgt' mem_tgt' sc_src' mem_src', 
    (cse_match_state inj lo 
      (Thread.mk rtl_lang st_tgt lc_tgt sc_tgt mem_tgt) (Thread.mk rtl_lang st_src lc_src sc_src mem_src) true)
    ->
      (Rely inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)
            inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src')
            (Local.promises lc_tgt) (Local.promises lc_src) lo)
    ->
      (cse_invariant lo inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src'))
     -> 
    (cse_match_state inj' lo 
      (Thread.mk rtl_lang st_tgt lc_tgt sc_tgt' mem_tgt') (Thread.mk rtl_lang st_src lc_src sc_src' mem_src') true).
Proof.
  intros.
  destruct st_tgt as (regs_tgt, blk_tgt, cdhp_tgt, cont_tgt, code_tgt) eqn:EqStTgt.
  destruct st_src as (regs_src, blk_src, cdhp_src, cont_src, code_src) eqn:EqStSrc; simpls.
  inv H; simpls. rename inj'0 into inj1.

  inversion INVARIANT. 
  inversion MATCH_LOCAL.
  inversion MATCH_RTL_STATE; simpls.
  rename H into SC_EQ_START.
  destruct H2 as (MEM_EQ_START & INJ_MAP_MEM_TGT).
  inversion MATCH_FRAME; simpls.
  inv H0.
  inv ENV_STEPS.
  simpls.
  eapply cse_match_state_intro; simpls; eauto.
  eapply cse_match_local_state_intro; simpls; eauto.
  eapply cse_match_rtl_state_intro; simpls; eauto.
  eapply cse_match_frame_intro; simpls; eauto.
  eapply incr_mem_preserve_match_ai; eauto. 
  eapply incr_inj_preserve_mem_injected; eauto.
  left. splits; trivial. eapply eq_inj_refl.
  eapply incr_mem_preserve_local_wf; eauto.
Qed.
