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
Require Import DCEProofLemmas.

Lemma match_state_dce_implies_promise_consistent
      inj lo b
      state_tgt lc_tgt sc_tgt mem_tgt
      state_src lc_src sc_src mem_src
      (MATCH_STATE: match_state_dce inj lo b
                                    (Thread.mk rtl_lang state_tgt lc_tgt sc_tgt mem_tgt)
                                    (Thread.mk rtl_lang state_src lc_src sc_src mem_src))
      (PROMS_CONS: Local.promise_consistent lc_tgt):
  Local.promise_consistent lc_src.
Proof.
  unfold Local.promise_consistent in *; ss. ii.
  inv MATCH_STATE. simpl in INV. destruct INV as (_ & MSG_INJ & _).
  assert (INJ_INCR: forall to to', inj loc to = Some to' -> inj' loc to = Some to').
  {
    ii; des; subst; eauto.
  }
  clear ATM_BIT.
  ss.
  clear LOCAL_WF_TGT CLOSED_SC_TGT MEM_CLOSED_TGT.
  clear LOCAL_WF_SRC CLOSED_SC_SRC.
  clear CUR_ACQ MATCH_THRD_LOCAL ATOM_MEM_EQ.
  inv VIEW_MATCH. inv MSG_INJ. unfold promises_relation in PROM_INJ.
  des; ss. inv PROM_INJ.
  exploit COMPLETE0; eauto. ii; des.
  rewrite dset_gempty in x0. ss.
  exploit PROMS_CONS; eauto. introv LT.
  eapply INJ_INCR in x.
  destruct (lo loc) eqn:Heqe.
  {
    clear - x LT MONOTONIC ATM_LOC_CUR_RLX Heqe.
    eauto.
  }
  {
    clear - x LT MONOTONIC NA_LOC_CUR_RLX Heqe.
    eapply NA_LOC_CUR_RLX in Heqe. inv Heqe. des. eauto.
  }
Qed.
  
Lemma silent_step_case:
  forall inj lo b
    state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
    state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
    state_src tview_src prm_src sc_src mem_src 
    (MATCH: match_state_dce inj lo b
                            (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                            (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
    (TGT_STEP: Thread.program_step ThreadEvent.silent lo
                                   (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                                   (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt'))
    (PROM_CONS: Local.promise_consistent (Local.mk tview_src prm_src)),
    (exists state_src' tview_src' prm_src' sc_src' mem_src',
        Thread.na_step lo 
                       (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
                       (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
        match_state_dce inj lo false
                        (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                        (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src')) \/
    Thread.is_abort (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src) lo.
Proof.
  ii.
  inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
  destruct BB_src.
  - (* jmp *)
    simpl in AI_FOR_CBLK. inv AI_FOR_CBLK.
    simpl in TGT_STEP.
    inv TGT_STEP. inv STATE; tryfalse. inv LOCAL. symmetry in BLK. inv BLK.
    exploit transf_cdhp_prop; eauto. renames b' to BB_tgt'.
    introv NXT_BB.
    destruct NXT_BB as (BB_src' & ai' & ai_pblk' & NXT_BB_src & ANALY_BLK & TRANS_BB & NXT').
    exploit LINK; eauto. simpl. eauto.
    introv GE_L. rewrite ANALY_BLK in GE_L. simpl in GE_L.
    left.
    do 5 eexists.
    split.
    {
      (* source step *)
      eapply Thread.na_tau_step_intro; eauto.
      econs. ss. 
      eapply State.step_jmp; eauto.
      eapply Local.step_silent; eauto.
    }
    {
      (* match state *)
      econs; eauto.
      econs; eauto. econs; eauto. eapply ge_ai_interp_prsv; eauto.
      des; subst; eauto.
    }
  - (* call *)
    left.
    simpl in AI_FOR_CBLK. inv AI_FOR_CBLK.
    destruct ai_tail. inv H0. simpl in TGT_STEP. simpl in LINK.
    inv TGT_STEP. inv STATE; tryfalse. inv LOCAL. symmetry in BLK. inv BLK.
    renames b' to BB_tgt', ch0 to C_tgt', b2 to BB_tgt1.
    exploit transf_cdhp_prop; eauto.
    introv NXT_BB.
    destruct NXT_BB as (BB_src' & ai' & ai_pblk' & NXT_BB_src & ANALY_BLK & TRANS_BB & NXT').
    destruct (Prog_src ! f) eqn: PROG_SRC_F.
    {
      destruct f0 as (C_src', f1').
      exploit transform_prog_proper; eauto. i. do 2 des1.
      rewrite FIND_FUNC in x0. inv x0.
      exploit transform_func_init; eauto.
      introv TGT_FUN_ENTRY.
      destruct TGT_FUN_ENTRY as (BB_src1 & afunc' & SRC_FUNC_ENTRY & FUNC_ANALYSIS' & TRANS_CDHP' & FID).
      subst f1'.

      do 5 eexists.
      splits.
      {
        (* source step *)
        eapply Thread.na_tau_step_intro; eauto.
        econs. ss. 
        eapply State.step_call; eauto.
        eapply Local.step_silent; eauto.
      }
      {
        (* match state *)
        econs; eauto.
        {
          econs. eauto.
          
          exploit transf_cdhp_prop; eauto. i. do 6 des1.
          rewrite SRC_FUNC_ENTRY in x0. symmetry in x0. inv x0.
          econs; eauto.
          unfold ai_interp in AI_INTERP. des1.
          unfold ai_interp. destruct ai. split.
          ii. unfold RegFile.init. rewrite RegFun.init_spec. eauto.
          eapply ge_sem_live_loc; eauto.
          unfold nmem_ge. destruct n2; ss. ii. eapply LocSet.Facts.empty_iff in H. ss.
          
          econs; eauto. ii.
          exploit LINK; eauto. i.
          econs; eauto.
          rewrite ANALY_BLK in x. simpl in x.
          eapply ge_ai_interp_prsv; eauto.
          unfold ai_interp in AI_INTERP. des1.
          unfold ai_interp. split; eauto.
          eapply ge_sem_live_loc; eauto.
          unfold nmem_ge. destruct n0; ss. ii. eapply LocSet.Facts.empty_iff in H0. ss.
        }
        {
          clear - ATM_BIT.
          des; subst; eauto.
        }
      }
    }
    {
      exploit transform_prog_proper_none; eauto.
      ii. rewrite FIND_FUNC in x0; ss.
    }
  - (* be *)
    simpl in AI_FOR_CBLK. inv AI_FOR_CBLK.
    destruct ai_tail. inv H0. simpl in TGT_STEP.
    inv TGT_STEP. inv STATE; tryfalse. inv LOCAL. symmetry in BLK. inv BLK.
    assert (EXPR_EQ: RegFile.eval_expr e R_tgt = RegFile.eval_expr e R_src).
    {
      eapply sem_live_reg_regs_eq; eauto.
      unfold ai_interp in *. des1; eauto.
    }
    des1; left.
    {
      des1.
      exploit transf_cdhp_prop; eauto. renames b' to BB_tgt'.
      introv NXT_BB.
      destruct NXT_BB as (BB_src' & ai' & ai_pblk' & NXT_BB_src & ANALY_BLK & TRANS_BB & NXT').
      exploit LINK; eauto. simpl. eauto.
      introv GE_L. rewrite ANALY_BLK in GE_L. simpl in GE_L.
      do 5 eexists.
      split.
      {
        (* source step *)
        eapply Thread.na_tau_step_intro; eauto.
        econs. ss. 
        eapply State.step_be; eauto. left. rewrite <- EXPR_EQ; eauto.
        eapply Local.step_silent; eauto.
      }
      {
        (* match state *)
        econs; eauto. 
        econs; eauto. econs; eauto.
        eapply ai_interp_set_expr_live in AI_INTERP.
        eapply ge_ai_interp_prsv; eauto.

        clear - ATM_BIT. des; subst; eauto.
      }
    }
    {
      des1.
      exploit transf_cdhp_prop; eauto. renames b' to BB_tgt'.
      introv NXT_BB.
      destruct NXT_BB as (BB_src' & ai' & ai_pblk' & NXT_BB_src & ANALY_BLK & TRANS_BB & NXT').
      exploit LINK; eauto. simpl. eauto.
      introv GE_L. rewrite ANALY_BLK in GE_L. simpl in GE_L.
      do 5 eexists.
      split.
      {
        (* source step *)
        eapply Thread.na_tau_step_intro; eauto.
        econs. ss. 
        eapply State.step_be; eauto. right. rewrite <- EXPR_EQ; eauto.
        eapply Local.step_silent; eauto.
      }
      {
        (* match state *)
        econs; eauto. 
        econs; eauto. econs; eauto.
        eapply ai_interp_set_expr_live in AI_INTERP.
        eapply ge_ai_interp_prsv; eauto.

        clear - ATM_BIT. des; subst; eauto.
      }
    }
  - (* ret *)
    simpl in AI_FOR_CBLK. inv AI_FOR_CBLK.
    simpl in TGT_STEP.
    inv TGT_STEP. inv STATE; tryfalse. inv LOCAL. clear BLK.
    left. inv STK_FRAMES.
    do 5 eexists.
    split.
    {
      (* source step *)
      eapply Thread.na_tau_step_intro; eauto.
      econs. ss. 
      eapply State.step_ret; eauto.
      eapply Local.step_silent; eauto.
    }
    {
      (* match state *)
      exploit CUR_MATCH. unfold ai_interp in AI_INTERP. des1; eauto.
      introv MATCH_STATE_CUR_STK.
      econs; eauto. econs; eauto.
      clear - ATM_BIT. des; subst; eauto.
    }
  - (* instr *)
    destruct c.
    + (* skip *) 
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      inv TGT_STEP. inv STATE; tryfalse. inv LOCAL. inv BLK.
      left.
      do 5 eexists.
      split.
      {
        (* source step *)
        eapply Thread.na_tau_step_intro; eauto.
        econs. ss. 
        eapply State.step_skip; eauto.
        eapply Local.step_silent; eauto.
      }
      {
        (* match state *)
        econs; eauto. econs; eauto. destruct ai'.
        unfold transf_instr in AI_INTERP. econs; eauto.
        clear - ATM_BIT. des; subst; eauto.
      }
    + (* assign *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP. destruct ai'.
      destruct (is_dead_reg lhs n) eqn:IS_DEAD_REG; left.
      {
        inv TGT_STEP. inv STATE; tryfalse. inv LOCAL. inv BLK.
        do 5 eexists.
        splits.
        {
          eapply Thread.na_tau_step_intro; eauto.
          econs; eauto. simpl. 
          eapply State.step_assign; eauto.
        }
        {
          econs; eauto. econs; eauto. econs; eauto.
          unfold transf_instr in AI_INTERP. rewrite IS_DEAD_REG in AI_INTERP.
          unfold ai_interp in AI_INTERP. des1.
          unfold ai_interp. split; eauto.
          clear - AI_INTERP IS_DEAD_REG. unfold sem_live_reg in *. ii.
          exploit AI_INTERP; eauto. ii.
          unfold is_dead_reg in *. 
          destruct (Pos.eq_dec lhs r); subst.
          rewrite H in IS_DEAD_REG. ss.
          rewrite RegFun.add_spec_neq; eauto.
          clear - ATM_BIT. des; subst; ss; eauto.
        }
      }
      {
        inv TGT_STEP. inv STATE; tryfalse. inv LOCAL. inv BLK.
        do 5 eexists.
        splits.
        {
          eapply Thread.na_tau_step_intro; eauto.
          econs; eauto. simpl. 
          eapply State.step_assign; eauto.
        }
        {
          unfold transf_instr in AI_INTERP. rewrite IS_DEAD_REG in AI_INTERP.
          econs; eauto. econs; eauto. econs; eauto.
          unfold ai_interp in AI_INTERP. des1.
          unfold ai_interp. split; eauto.
          exploit sem_live_reg_regs_eq; eauto. i. rewrite x0.
          eapply sem_live_reg_less in AI_INTERP.
          clear - AI_INTERP. unfold sem_live_reg in *; ss. ii.
          specialize (AI_INTERP r0). unfold set_reg_dead in AI_INTERP.
          destruct (Pos.eq_dec r0 r); subst; eauto.
          do 2 (rewrite RegFun.add_spec_eq).  eauto.
          exploit AI_INTERP; eauto.
          rewrite NREG.gsspec. des_if; eauto. i.
          do 2 (rewrite RegFun.add_spec_neq; eauto).
          clear - ATM_BIT. des; subst; eauto.
        }
      }
    + (* load -> skip *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      pose proof (nonatomic_or_atomic or) as ORD.
      destruct ORD as [ORD_NA | ORD_AT]; subst.
      {
        (* non-atomic location *)
        destruct ai'; simpl in TGT_STEP.
        destruct (lo loc) eqn:LOC_TYPE.
        (* for atomic location, we imply the contradiction *)
        right. eapply na_load_atomic_loc_abort; eauto. ss. 
        (* for non-atomic location, we let the redundant read to read the message in its current view *)
        left. 
        exploit read_na_cur_msg_local_stable; eauto.
        introv SRC_READ. destruct SRC_READ as (val & R & SRC_READ); simpl in SRC_READ.
        do 5 eexists.
        split.
        {
          (* source step *)
          eapply Thread.na_plain_read_step_intro; eauto.
          econs. ss. eapply State.step_load; eauto.
          eapply Local.step_read; eauto.
        } 
        {
          (* match state preservation *) 
          destruct (is_dead_reg lhs n) eqn:IS_DEAD_REG; eauto.

          (* is dead reg *)
          inv TGT_STEP. inv LOCAL.
          econs; eauto. inv STATE; tryfalse. inv BLK.
          econs; eauto.
          econs.
          eapply FUNC_ANALYSIS. eauto. eapply CONS_ANALYSIS. eauto.
          unfold ai_interp in *.
          destruct (transf_instr (Inst.load lhs loc Ordering.plain) (n, n0)) eqn:TRANS_INSTR.
          simpl in TRANS_INSTR. rewrite IS_DEAD_REG in TRANS_INSTR. inv TRANS_INSTR.
          clear ATM_BIT. des. split; eauto.
          clear - AI_INTERP IS_DEAD_REG.
          unfold sem_live_reg in *. ii.
          exploit AI_INTERP; eauto. introv REG_EQ.
          destruct (Reg.eq_dec lhs r); subst.
          unfold is_dead_reg in IS_DEAD_REG. rewrite H in IS_DEAD_REG. ss.
          rewrite RegFun.add_spec_neq; eauto. 
          simpl in LINK. eauto.
          clear - ATM_BIT. des; subst; eauto.

          (* not dead reg: contradiction *)
          inv TGT_STEP; ss. inv STATE; ss.
        }
      }
      {
        (* atomic location: contradiction *)
        assert (LOAD: match or with
                       | Ordering.plain =>
                           let (nr, _) := ai' in if is_dead_reg lhs nr then Inst.skip else Inst.load lhs loc or
                       | _ => Inst.load lhs loc or
                      end ## transform_blk' ai_b' BB_src =
                      Inst.load lhs loc or ## transform_blk' ai_b' BB_src).
        {
          destruct or; tryfalse; eauto.
        }
        rewrite LOAD in TGT_STEP.
        inv TGT_STEP. inv STATE; tryfalse.
      }
    + (* store -> skip *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      pose proof (nonatomic_or_atomic ow) as ORD.
      destruct ORD as [ORD_NA | ORD_AT]; subst.
      {
        (* non-atomic location *)
        destruct ai'; simpl in TGT_STEP.
        destruct (lo lhs) eqn:LOC_TYPE.
        (* for atomic location, we imply the contradiction *)
        right. eapply na_store_atomic_loc_abort; eauto. ss.
        (* for non-atomic location *)
        destruct (is_dead_loc lhs n0) eqn:IS_DEAD_LOC.

        (* is dead location *)
        simpl in AI_INTERP. rewrite IS_DEAD_LOC in AI_INTERP.
        left.
        exploit InvView_dce_na_loc; eauto. introv TM_H.
        destruct TM_H as (NA_CUR_RLX & NA_ACQ_RLX).
        exploit TM_I_dce_cur_acq_to_write; [eapply NA_CUR_RLX | eapply NA_ACQ_RLX  | eauto..].
        {
          inv LOCAL_WF_TGT; eauto.
        }
        {
          inv LOCAL_WF_SRC; eauto.
        }
        {
          inv LOCAL_WF_SRC; eauto.
        } 

        instantiate (1 := RegFile.eval_expr rhs R_src). ii. do 9 des1.
        assert (TGT_STATE: tview_tgt = tview_tgt' /\ prm_tgt = prm_tgt' /\ sc_tgt = sc_tgt' /\ mem_tgt = mem_tgt').
        {
          clear - TGT_STEP. inv TGT_STEP; ss. inv LOCAL; ss.
        }
        do 4 des1; subst. simpl in LOCAL_WRITE.
        do 5 eexists. splits.
        {
          (* na write step *)
          eapply Thread.na_plain_write_step_intro; eauto.
          econs. simpl. eapply State.step_store; eauto.
          econs. eauto.
        }
        {
          (* match state preservation *)
          econs; eauto.
          {
            (* Memory at eq *)
            eapply Mem_at_eq_reflexive.
            eapply Mem_at_eq_na_step_prsv_aux.
            eapply Thread.na_plain_write_step_intro with (lang := rtl_lang); eauto.
            econs. simpl. eapply State.step_store; eauto.
            econs. eauto.
            ss. eapply Mem_at_eq_reflexive; eauto.
            ss.
          } 
          {
            (* match state tlocal *)
            inv TGT_STEP; tryfalse. inv STATE; tryfalse. inv BLK.
            econs; eauto.
            econs; eauto.
            clear - IS_DEAD_LOC AI_INTERP. unfold ai_interp in *; des. split; eauto.
            unfold sem_live_loc in *. ii.
            destruct (Loc.eq_dec loc lhs); subst.
            {
              rewrite IS_DEAD_LOC in H. ss.
            }
            {
              cut (lhs <> loc); eauto. clear n1; introv DISJ_LOC.
              exploit le_relacq_tview_disj_loc_cur; eauto.
              ii; des. rewrite CUR_RLX. rewrite CUR_PLN.
              exploit le_relacq_tview_disj_loc_acq; eauto.
              ii; des. rewrite ACQ_RLX. rewrite ACQ_PLN.
              eauto.
            }
          }
          {
            (* inv view *)
            econs; eauto.
            {
              (* current atomic location na-view *)
              introv ATOM_LOC. destruct (Loc.eq_dec lhs loc); subst.
              rewrite LOC_TYPE in ATOM_LOC. ss.
              exploit le_relacq_tview_disj_loc_cur; eauto.
              ii. des1.
              rewrite CUR_PLN. inv VIEW_MATCH; eauto.
            }
            {
              (* current atomic location rlx-view *)
              introv ATOM_LOC. destruct (Loc.eq_dec lhs loc); subst.
              rewrite LOC_TYPE in ATOM_LOC. ss.
              exploit le_relacq_tview_disj_loc_cur; eauto.
              ii. des1.
              rewrite CUR_RLX. inv VIEW_MATCH; eauto.
            }
            {
              (* current non-atomic location rlx-view *) 
              introv NA_LOC. 
              destruct (Loc.eq_dec lhs loc); subst; eauto.
              exploit le_relacq_tview_disj_loc_cur; eauto.
              ii. des1.
              eapply tm_loc_eq_TM_prsv. symmetry. rewrite CUR_RLX. eauto.
              inv LOCAL_WRITE. simpl in LC2. inv LC2.
              eapply mem_write_disj_loc_TM_prsv; eauto.
              inv VIEW_MATCH; eauto.
            }
            {
              (* acquire atomic location na-view *)
              introv ATOM_LOC. destruct (Loc.eq_dec lhs loc); subst.
              rewrite LOC_TYPE in ATOM_LOC. ss.
              exploit le_relacq_tview_disj_loc_acq; eauto.
              ii. des1.
              rewrite ACQ_PLN. inv VIEW_MATCH; eauto.
            }
            {
              (* acquire atomic location rlx-view *)
              introv ATOM_LOC. destruct (Loc.eq_dec lhs loc); subst.
              rewrite LOC_TYPE in ATOM_LOC. ss.
              exploit le_relacq_tview_disj_loc_acq; eauto.
              ii. des1.
              rewrite ACQ_RLX. inv VIEW_MATCH; eauto.
            }
            {
              (* acquire non-atomic location rlx-view *) 
              introv NA_LOC. 
              destruct (Loc.eq_dec lhs loc); subst; eauto.
              exploit le_relacq_tview_disj_loc_acq; eauto.
              ii. des1.
              eapply tm_loc_eq_TM_prsv. symmetry. rewrite ACQ_RLX. eauto.
              inv LOCAL_WRITE. simpl in LC2. inv LC2.
              eapply mem_write_disj_loc_TM_prsv; eauto.
              inv VIEW_MATCH; eauto.
            }
            {
              (* release view for atomic location *)
              introv ATOM_LOC.
              destruct (Loc.eq_dec lhs loc); subst.
              rewrite LOC_TYPE in ATOM_LOC. ss.
              exploit le_strong_relaxed_tview_disj_loc_rel; eauto.
              instantiate (1 := Ordering.plain). eauto. ii. des1.
              rewrite x0. inv VIEW_MATCH; eauto.
            }
          }
          {
            (* injection *)
            clear - ATM_BIT.
            cut (forall loc t t', inj loc t = Some t' -> inj' loc t = Some t').
            ii. left. eauto.
            ii. des; subst; eauto.
          }
          {
            (* src local wf *)
            eapply local_wf_write; eauto.
            clear - INV. ss. des; eauto.
          }
          {
            (* src closed timemap *)
            inv LOCAL_WRITE. inv LC2. inv WRITE. inv PROMISE.
            eapply Memory.add_closed_timemap; eauto.
          }
        }

        (* not dead location *)
        clear - TGT_STEP. inv TGT_STEP. inv LOCAL; ss. inv STATE; ss.
      }
      {
        assert (TRANS: match ow with
                       | Ordering.plain =>
                           let (_, nm) := ai' in if is_dead_loc lhs nm then Inst.skip else Inst.store lhs rhs ow
                       | _ => Inst.store lhs rhs ow
                       end ## transform_blk' ai_b' BB_src =
                       Inst.store lhs rhs ow ## transform_blk' ai_b' BB_src).
        {
          destruct ow; ss; eauto.
        }
        rewrite TRANS in TGT_STEP.
        clear - TGT_STEP. inv TGT_STEP. ss. inv STATE; ss.
      }
    + (* print: contradiction *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      inv TGT_STEP. inv STATE; tryfalse.
    + (* cas : contradiction *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      inv TGT_STEP. inv STATE; tryfalse.
    + (* fence rel: contradiction *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      inv TGT_STEP. inv STATE; tryfalse.
    + (* fence acq: contradiction *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      inv TGT_STEP. inv STATE; tryfalse.
    + (* fence sc: contradiction *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      inv TGT_STEP. inv STATE; tryfalse.
      Unshelve. exact C_src. exact cont_src. exact Prog_src. exact BB_src.
Qed.

Definition na_thrdevt_eq (te1 te2: ThreadEvent.t) :=
  match te1, te2 with
  | ThreadEvent.read loc1 to1 val1 _ ord1, ThreadEvent.read loc2 to2 val2 _ ord2 =>
    loc1 = loc2 /\ ord1 = ord2
  | ThreadEvent.write loc1 from1 to1 val1 _ ord1, ThreadEvent.write loc2 from2 to2 val2 _ ord2 =>
    loc1 = loc2 /\ ord1 = ord2
  | _, _ => (te1 = ThreadEvent.silent /\ te2 = te1)
  end.

Lemma na_read_write_step_case:
  forall inj lo b te
    state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
    state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
    state_src tview_src prm_src sc_src mem_src 
    (MATCH: match_state_dce inj lo b
                            (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                            (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
    (TGT_STEP: Thread.program_step te lo
                                   (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                                   (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt'))
    (NA_READ_WRITE: (exists loc from to v R, te = ThreadEvent.write loc from to v R Ordering.plain) \/
                    (exists loc to v R, te = ThreadEvent.read loc to v R Ordering.plain))
    (PROM_CONS: Local.promise_consistent (Local.mk tview_src prm_src)),
    exists state_src' tview_src' prm_src' sc_src' mem_src' te',
        Thread.program_step te' lo 
                            (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
                            (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
        match_state_dce inj lo false
                        (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                        (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
        na_thrdevt_eq te te'.
Proof.
  ii.
  inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
  destruct BB_src.
  - (* jmp *)
    simpl in AI_FOR_CBLK. inv AI_FOR_CBLK.
    simpl in TGT_STEP.
    inv TGT_STEP. inv STATE; tryfalse. destruct te; ss; tryfalse.
    clear - NA_READ_WRITE. des; ss.
    clear - NA_READ_WRITE. des; ss.
  - (* call *)
    simpl in AI_FOR_CBLK. inv AI_FOR_CBLK.
    destruct ai_tail; ss. inv H0. simpl in TGT_STEP.
    inv TGT_STEP. inv STATE; tryfalse. destruct te; ss; tryfalse.
    clear - NA_READ_WRITE. des; ss.
    clear - NA_READ_WRITE. des; ss.
  - (* be *)
    simpl in AI_FOR_CBLK. inv AI_FOR_CBLK.
    destruct ai_tail; ss. inv H0. simpl in TGT_STEP.
    inv TGT_STEP. inv STATE; tryfalse. destruct te; ss; tryfalse.
    clear - NA_READ_WRITE. des; ss.
    clear - NA_READ_WRITE. des; ss.
  - (* ret *)
    simpl in AI_FOR_CBLK. inv AI_FOR_CBLK.
    simpl in TGT_STEP.
    inv TGT_STEP. inv STATE; tryfalse. destruct te; ss; tryfalse.
    clear - NA_READ_WRITE. des; ss.
    clear - NA_READ_WRITE. des; ss.
  - (* instr *)
    destruct c.
    + (* skip *)
      clear - TGT_STEP NA_READ_WRITE AI_FOR_CBLK.
      inv TGT_STEP.
      ss. destruct (transf_blk ai_tail BB_src) eqn: TRANS_BLK; eauto; ss.
      inv AI_FOR_CBLK. ss. inv STATE; ss. inv BLK. destruct te; des; ss.
      inv AI_FOR_CBLK. ss. inv STATE; ss. inv BLK. destruct te; des; ss.
    + (* assign *)
      clear - TGT_STEP NA_READ_WRITE AI_FOR_CBLK.
      inv TGT_STEP.
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      ss. destruct ai'; ss. destruct (is_dead_reg lhs n); ss.
      inv STATE; ss. inv BLK. destruct te; des; ss.
      inv STATE; ss. inv BLK. destruct te; des; ss.
    + (* load *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      pose proof (nonatomic_or_atomic or) as ORD.
      destruct ORD as [ORD_NA | ORD_AT]; subst.
      {
        (* non-atomic read *)
        destruct ai'. simpl in AI_INTERP.
        destruct (is_dead_reg lhs n) eqn: DEAD_REG.

        (* is dead reg: contradiction *)
        clear - TGT_STEP NA_READ_WRITE.
        inv TGT_STEP. des; subst; ss; try solve [inv STATE; ss].
 
        (* not dead register *)
        inv TGT_STEP.
        destruct NA_READ_WRITE as [(loc0 & from & to & v & R & TE) | (loc0 & to & v & R & TE)].
        subst te. simpl in STATE. inv STATE; tryfalse. 
        subst te. simpl in STATE. inv LOCAL.  
        inv STATE; tryfalse. inv BLK.
        exploit ai_interp_live_loc_cur; eauto. ii. do 3 des1.
        exploit injection_read; eauto. inv INV. des; eauto.
        instantiate (1 := prm_src). ii. do 8 des1.
        do 6 eexists.
        split.
        {
          (* source read step *)
          econs. Focus 2. 
          eapply Local.step_read; eauto.
          simpl. eapply State.step_load; eauto.
        }
        {
          (* match state preservation *)
          split; simpl; eauto.
          inv LOCAL0. simpl in LC2. inv LC2. simpl in READABLE.
          inv LOCAL_READ_SRC. simpl in LC2. inv LC2. simpl in READABLE0.
          econs; eauto.
          {
            (* match state tlocal *)
            econs; eauto. econs; eauto.
            eapply ai_interp_read_prsv; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* InvView *)
            eapply InvView_dce_read_prsv; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* cur acq *)
            eapply cur_acq_read_prsv; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* cur acq pln *)
            eapply cur_acq_pln_read_prsv; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* inj *)
            clear - ATM_BIT. left; eauto.
            split; eauto. ii; des; subst; eauto.
          }
          {
            (* Local wf tgt *)
            eapply local_wf_read; eauto. econs; eauto.
          }
          {
            (* Local wf src *)
            eapply local_wf_read; eauto. econs; eauto.
            clear - INV. ss; des; eauto.
          }
        }
      }
      {
        (* atomic load: contradiction *)
        assert (ATOM_LOAD: match or with
                           | Ordering.plain =>
                             let (nr, _) := ai' in if is_dead_reg lhs nr then Inst.skip else Inst.load lhs loc or
                           | _ => Inst.load lhs loc or
                           end ## transform_blk' ai_b' BB_src =
                           Inst.load lhs loc or ## transform_blk' ai_b' BB_src).
        {
          destruct or; ss.
        }
        rewrite ATOM_LOAD in TGT_STEP.
        clear - TGT_STEP NA_READ_WRITE ORD_AT.
        inv TGT_STEP. des; subst. ss. inv STATE; ss.
        ss. inv STATE; ss. inv BLK; ss.
      }
    + (* store *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      pose proof (nonatomic_or_atomic ow) as ORD.
      destruct ORD as [ORD_NA | ORD_AT]; subst.
      {
        (* non-atomic write *)
        destruct ai'. simpl in AI_INTERP.
        destruct (is_dead_loc lhs n0) eqn: DEAD_REG.

        (* is dead loc: contradiction *)
        clear - TGT_STEP NA_READ_WRITE.
        inv TGT_STEP. des; subst; ss; try solve [inv STATE; ss].

        (* not dead loc *)
        inv TGT_STEP.
        destruct NA_READ_WRITE as [(loc0 & from & to & v & R & TE) | (loc0 & to & v & R & TE)].
        2: {subst te. simpl in STATE. inv STATE; tryfalse. } 
        subst te. simpl in STATE. inv LOCAL.  
        inv STATE; tryfalse. inv BLK.
        assert (LOC_NA: lo loc0 = Ordering.nonatomic).
        {
          clear - LOCAL0. inv LOCAL0; ss. destruct (lo loc0) eqn:LOC_NA_AT; eauto.
          ss. des; ss.
        }
        assert (VAL_EQ: RegFile.eval_expr e R_tgt = RegFile.eval_expr e R_src).
        {
          clear - AI_INTERP.
          eapply ai_interp_live_regs_eq; eauto.
        }
        exploit TM_I_dce_non_atomic_write; eauto.
        {
          clear - VIEW_MATCH LOC_NA. inv VIEW_MATCH; eauto.
        }
        {
          simpl in INV. ss. des; eauto.
        }
        {
          eapply promises_relation_rely_stable; eauto.
          clear - ATM_BIT. des; subst; eauto. unfold incr_inj; ii; eauto.
        }

        ii. do 14 des1.
        do 6 eexists. split.
        { 
          (* source execution *)
          econs.
          2: { eapply Local.step_write; eauto. }
          simpl. econs; eauto.
        }
        splits; try solve [ss; eauto].
        econs; eauto.
        {
          (* memory atomic eq *) 
          eapply Mem_at_eq_na_step_prsv_aux. 
          eapply Thread.na_plain_write_step_intro.
          econs. 2: {  econs. eapply LOCAL0. }
          simpl. instantiate (3 := rtl_lang). eapply State.step_store; eauto.
          2: { simpl; eauto. }
          simpl.
          eapply Mem_at_eq_reflexive.
          eapply Mem_at_eq_na_step_prsv_aux. 
          eapply Thread.na_plain_write_step_intro.
          econs. 2: {  econs. eapply LOCAL_WRITE_SRC. }
          simpl. instantiate (3 := rtl_lang). eapply State.step_store; eauto.
          simpl. eapply Mem_at_eq_reflexive; eauto.
          simpl. eauto.
        }
        {
          (* ai interp *)
          econs; eauto. econs; eauto.
          clear - LOCAL0 LOCAL_WRITE_SRC AI_INTERP INJ' INJ_INCR MON_INJ
                         CUR_ACQ CUR_ACQ_PLN LOCAL_WF_TGT LOCAL_WF_SRC LOC_NA.
          inv LOCAL0; ss. inv LC2. inv LOCAL_WRITE_SRC; ss. inv LC2. des.
          split. eapply sem_live_reg_less; eauto.
          eapply sem_live_loc_write_na_loc; eauto.
          {
            des_if; eauto. ss. des; ss.
          }
          {
            inv WRITABLE; eauto.
          }
          {
            inv LOCAL_WF_TGT; eauto.
          }
          {
            inv WRITABLE0; eauto.
          }
          {
            inv LOCAL_WF_SRC; eauto.
          }
        }
        {
          (* inv view dec *)
          inversion LOCAL0. simpl in LC2. inversion LC2. clear LC2.
          inversion LOCAL_WRITE_SRC. inversion LC2. clear LC2. 
          eapply InvView_dce_write; eauto.
          inv WRITABLE; ss; eauto. inv WRITABLE0; ss; eauto.
          rewrite INJ'. des_if; eauto. simpl in o. des; ss.
          introv DISJ. rewrite INJ'. des_if; ss. des; subst; ss.
          introv DISJ_LOC. eapply Local_write_disj_loc_stable; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          inv LOCAL_WF_TGT; eauto. simpl in INV. des; eauto.
          ii; ss.
        }
        {
          (* cur acq *)
          inversion LOCAL0. simpl in LC2. inversion LC2. clear LC2.
          inversion LOCAL_WRITE_SRC. inversion LC2. clear LC2.
          eapply cur_acq_write_prsv; eauto.
          inv WRITABLE; ss; eauto. inv WRITABLE0; ss; eauto.
          rewrite INJ'. des_if; eauto. simpl in o. des; ss.
        }
        {
          (* cur acq pln *)
          inversion LOCAL0. simpl in LC2. inversion LC2. clear LC2.
          inversion LOCAL_WRITE_SRC. inversion LC2. clear LC2.
          eapply cur_acq_pln_write_prsv; eauto.
          inv WRITABLE; ss; eauto. inv WRITABLE0; ss; eauto.
          rewrite INJ'. des_if; eauto. simpl in o. des; ss.
        }
        {
          (* promises relation *)
          eapply promises_relation_inj_na_write_prsv; eauto.
          clear - ATM_BIT INJ_INCR. eapply incr_inj_transitivity with (inj' := inj'); eauto.
          des; subst; ss; eauto.
          rewrite INJ'. des_if; eauto. simpl in o. des; ss.
        }
        {
          (* inj *)
          left. clear - ATM_BIT INJ_INCR. des; subst; eauto.
        }
        {
          (* local wf tgt *)
          eapply local_wf_write; eauto.
        }
        {
          (* memory closed timemap tgt *)
          clear - CLOSED_SC_TGT LOCAL0. inv LOCAL0. inv LC2. ss.
          inv WRITE. inv PROMISE; ss.
          eapply Memory.add_closed_timemap; eauto.
          eapply Memory.split_closed_timemap; eauto.
          eapply Memory.lower_closed_timemap; eauto.
        }
        {
          (* memory closed tgt *)
          eapply write_step_closed_mem; eauto.
        }
        {
          (* local wf src *)
          eapply local_wf_write; eauto.
          clear - INV. ss. des; eauto.
        }
        {
          (* memory closed timemap src *)
          clear - CLOSED_SC_SRC LOCAL_WRITE_SRC. inv LOCAL_WRITE_SRC. inv LC2. ss.
          inv WRITE. inv PROMISE; ss.
          eapply Memory.add_closed_timemap; eauto.
          eapply Memory.split_closed_timemap; eauto.
          eapply Memory.lower_closed_timemap; eauto.
        }
      }
      { 
        clear - TGT_STEP NA_READ_WRITE ORD_AT. destruct ow; ss. 
        inv TGT_STEP; ss. inv STATE; ss. inv BLK.
        destruct te; ss. inv H0.
        des; ss. inv NA_READ_WRITE. des; subst.
        inv TGT_STEP. inv STATE; ss. des; subst.
        inv TGT_STEP. inv STATE; ss.
        inv TGT_STEP. inv STATE; ss. inv BLK.
        destruct te; ss. inv H0. des; subst; ss.
        inv TGT_STEP. inv STATE; ss. inv BLK.
        destruct te; ss; eauto. inv H0. des; subst. inv NA_READ_WRITE.
        inv NA_READ_WRITE.
      }
    + (* print *)
      clear - TGT_STEP NA_READ_WRITE AI_FOR_CBLK.
      inv TGT_STEP.
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK. ss.
      inv STATE; ss. inv BLK. destruct te; des; ss.
    + (* CAS *)
      clear - TGT_STEP NA_READ_WRITE AI_FOR_CBLK.
      inv TGT_STEP.
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK. ss.
      inv STATE; ss. inv BLK. destruct te; des; ss.
      inv BLK. destruct te; des; ss. inv H0; ss. inv NA_READ_WRITE. ss.
    + (* fence rel *)
      clear - TGT_STEP NA_READ_WRITE AI_FOR_CBLK.
      inv TGT_STEP.
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK. ss.
      inv STATE; ss. inv BLK. destruct te; des; ss.
    + (* fence acq *)
      clear - TGT_STEP NA_READ_WRITE AI_FOR_CBLK.
      inv TGT_STEP.
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK. ss.
      inv STATE; ss. inv BLK. destruct te; des; ss.
    + (* fence sc *)
      clear - TGT_STEP NA_READ_WRITE AI_FOR_CBLK.
      inv TGT_STEP.
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK. ss.
      inv STATE; ss. inv BLK. destruct te; des; ss.
      Unshelve. exact C_src.
      exact cont_tgt.
      exact Prog_tgt.
      exact BB_src.
      exact C_src.
      exact cont_tgt.
      exact Prog_tgt.
      exact BB_src.
Qed.

Lemma atomic_or_out_step_case:
  forall inj lo b te pf
    state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
    state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
    state_src tview_src prm_src sc_src mem_src 
    (MATCH: match_state_dce inj lo b
                            (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                            (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
    (TGT_STEP: Thread.step lo pf te 
                           (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                           (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt'))
    (AT_OR_OUT: ThreadEvent.is_at_or_out_step te),
    exists state_src' tview_src' prm_src' sc_src' mem_src' te' inj',
      Thread.program_step te' lo 
                          (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
                          (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
      incr_inj inj inj' /\ 
      match_state_dce inj' lo true
                      (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                      (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
      thrdevt_eq te te'.
Proof.
  ii.
  inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
  destruct BB_src.
  - (* jmp: contradiction *)
    simpl in AI_FOR_CBLK. inv AI_FOR_CBLK.
    simpl in TGT_STEP.
    inv TGT_STEP. inv STEP. simpl in AT_OR_OUT; tryfalse.
    inv STEP. inv STATE; try solve [simpl in AT_OR_OUT; tryfalse].
    destruct te; ss; tryfalse.
  - (* call: contradiction *) 
    simpl in AI_FOR_CBLK. destruct ai_tail. inv AI_FOR_CBLK.
    simpl in TGT_STEP.
    inv TGT_STEP. inv STEP. simpl in AT_OR_OUT; tryfalse.
    inv STEP. inv STATE; try solve [simpl in AT_OR_OUT; tryfalse].
    destruct te; ss; tryfalse.
  - (* be: contradiction *)
    simpl in AI_FOR_CBLK. destruct ai_tail. inv AI_FOR_CBLK.
    simpl in TGT_STEP.
    inv TGT_STEP. inv STEP. simpl in AT_OR_OUT; tryfalse.
    inv STEP. inv STATE; try solve [simpl in AT_OR_OUT; tryfalse].
    destruct te; ss; tryfalse.
  - (* ret: contradiction *)
    simpl in AI_FOR_CBLK. destruct ai_tail. inv AI_FOR_CBLK.
    simpl in TGT_STEP.
    inv TGT_STEP. inv STEP. simpl in AT_OR_OUT; tryfalse.
    inv STEP. inv STATE; try solve [simpl in AT_OR_OUT; tryfalse].
    destruct te; ss; tryfalse.
  - (* instr *)
    destruct c.
    + (* skip: contradiction *)
      clear - TGT_STEP AT_OR_OUT AI_FOR_CBLK. inv TGT_STEP. inv STEP; ss.
      inv STEP; ss.  destruct (transf_blk ai_tail BB_src) eqn: TRANS_BLK; eauto; ss.
      inv AI_FOR_CBLK. ss. inv STATE; ss. inv BLK. destruct te; ss.
      inv AI_FOR_CBLK. ss. inv STATE; ss. inv BLK. destruct te; ss.
    + (* assign: contradiction *)
      clear - TGT_STEP AT_OR_OUT AI_FOR_CBLK. inv TGT_STEP. inv STEP; ss. 
      inv STEP; ss.  destruct (transf_blk ai_tail BB_src) eqn: TRANS_BLK; eauto; ss. 
      inv AI_FOR_CBLK. ss. inv STATE; ss. destruct te; ss.
      inv AI_FOR_CBLK. ss. destruct l; ss.
      destruct (is_dead_reg lhs n) eqn:Heqe'; eauto.
      inv STATE; ss. destruct te; ss.
      inv STATE; ss. destruct te; ss.
    + (* load *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      pose proof (nonatomic_or_atomic or) as ORD.
      destruct ORD as [NA_ORD | AT_ORD].
      {
        subst or. destruct ai'; simpl in TGT_STEP.
        destruct (is_dead_reg lhs n) eqn:IS_DEAD_REG.
        inv TGT_STEP. inv STEP; ss. inv STEP; ss. inv STATE; ss.
        destruct te; ss.
        inv TGT_STEP. inv STEP; ss. inv STEP; ss. inv STATE; ss.
        destruct te; ss. inv BLK. inv H0; ss.
      }
      {
        assert (LOAD_INSTR: match or with
                            | Ordering.plain =>
                              let (nr, _) := ai' in if is_dead_reg lhs nr then Inst.skip else Inst.load lhs loc or
                            | _ => Inst.load lhs loc or
                            end ## transform_blk' ai_b' BB_src =
                            Inst.load lhs loc or ## transform_blk' ai_b' BB_src).
        {
          destruct or; ss; eauto.
        }
        rewrite LOAD_INSTR in TGT_STEP. clear LOAD_INSTR.
        inv TGT_STEP. inv STEP; ss. inv STEP.
        inv STATE; try solve [destruct te; ss].
        destruct te; simpl in H0; tryfalse. inv H0. inv BLK.
        assert (AT_LOC: lo loc1 = Ordering.atomic).
        {
          clear - AT_ORD LOCAL. destruct (lo loc1) eqn:LOC_TYPE; eauto.
          inv LOCAL. inv LOCAL0. inv LC2; ss.
          rewrite LOC_TYPE in LO. destruct ord; ss.
        }
        exploit InvView_dce_at_loc; eauto. ii. do 3 des1.
        inv LOCAL.
        exploit injection_read; eauto. inv INV. des; eauto.
        instantiate (1 := prm_src). ii. do 8 des1.
        do 6 eexists. exists inj'.
        split.
        {
          (* source read step *)
          econs. Focus 2. 
          eapply Local.step_read; eauto.
          simpl. eapply State.step_load; eauto.
        }
        {
          (* match state preservation *)
          split. clear - ATM_BIT. des; subst; eauto. unfold incr_inj; ii; eauto.
          split; simpl; eauto.
          inv LOCAL0. simpl in LC2. inv LC2. simpl in READABLE.
          inv LOCAL_READ_SRC. simpl in LC2. inv LC2. simpl in READABLE0.
          destruct ai'. simpl in AI_INTERP.
          econs; eauto.
          {
            (* match state tlocal *)
            econs; eauto. econs; eauto. 
            destruct (is_dead_reg r n); eauto.
            eapply ai_interp_read_prsv'; eauto.
            eapply ai_interp_set_reg_dead; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
            eapply ai_interp_read_prsv; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* InvView *)
            eapply InvView_dce_read_prsv; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* cur acq *)
            eapply cur_acq_read_prsv; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* cur acq pln *)
            eapply cur_acq_pln_read_prsv; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* promise relation *)
            clear - ATM_BIT PROM_INJ. des; subst; eauto.
            eapply promises_relation_rely_stable; eauto.
          }
          {
            (* Local wf tgt *)
            eapply local_wf_read; eauto. econs; eauto.
          }
          {
            (* Local wf src *)
            eapply local_wf_read; eauto. econs; eauto.
            clear - INV. ss; des; eauto.
          }

          clear - INV AT_LOC INJ_TO. ss. des.
          exploit ID_ATOMIC; eauto.
        }
      }
    + (* store *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      pose proof (nonatomic_or_atomic ow) as ORD.
      destruct ORD as [NA_ORD | AT_ORD].
      {
        subst ow. destruct ai'; simpl in TGT_STEP.
        destruct (is_dead_loc lhs n0) eqn:IS_DEAD_LOC.
        inv TGT_STEP. inv STEP; ss. inv STEP; ss. inv STATE; ss.
        destruct te; ss.
        inv TGT_STEP. inv STEP; ss. inv STEP; ss. inv STATE; ss.
        destruct te; ss. inv BLK. inv H0; ss.
      }
      {
        assert (STORE_INSTR: match ow with
                             | Ordering.plain =>
                               let (_, nm) := ai' in if is_dead_loc lhs nm then Inst.skip else Inst.store lhs rhs ow
                             | _ => Inst.store lhs rhs ow
                             end ## transform_blk' ai_b' BB_src =
                             Inst.store lhs rhs ow ## transform_blk' ai_b' BB_src).
        {
          destruct ow; ss; eauto.
        }
        rewrite STORE_INSTR in TGT_STEP. clear STORE_INSTR.
        inv TGT_STEP. inv STEP; ss. inv STEP.
        inv STATE; try solve [destruct te; ss].
        destruct te; simpl in H0; tryfalse. inv H0. inv BLK.
        assert (AT_LOC: lo loc0 = Ordering.atomic).
        {
          clear - AT_ORD LOCAL. destruct (lo loc0) eqn:LOC_TYPE; eauto.
          inv LOCAL. inv LOCAL0. inv LC2; ss.
          rewrite LOC_TYPE in LO. destruct ord; ss.
        }
        inv LOCAL. 
        exploit Mem_at_eq_local_write_prsv; eauto.
        {
          instantiate (1 := inj'). simpl in INV. des; eauto.
        }
        {
          simpl. clear - AT_LOC VIEW_MATCH. inv VIEW_MATCH. eauto.
        }
        {
          simpl. inv PROM_INJ; eauto.
          eapply rel_promises_rely_stable; eauto.
          clear - ATM_BIT. des; subst; eauto. unfold incr_inj; ii; eauto.
        }
        {
          instantiate (1 := None). econs; eauto.
        }
        {
          simpl in INV. clear - INV. des; subst. inv INJ_MEM; eauto.
        }
        {
          simpl. clear - VIEW_MATCH AT_LOC. inv VIEW_MATCH. eauto.
        }
        {
          clear - AI_INTERP AT_LOC AT_ORD.
          unfold transf_instr in AI_INTERP. destruct ai'.
          destruct ord; ss. ii. des.
          eapply sem_live_loc_all; eauto.
          ii. des. eapply sem_live_loc_all; eauto.
        }
        {
          simpl. eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          inv LOCAL_WF_TGT; eauto. instantiate (1 := mem_src).
          clear - INV. ss. des; eauto.
        }

        ii. exploit x0. econs; eauto. clear - INV. ss. des; eauto. inv LOCAL_WF_TGT; eauto.
        clear x0. instantiate (1 := sc_src). ii. do 12 des1.
        destruct lc2'. renames tview to tview_src', promises to prm_src'.
        assert (NA_LOC_STABLE_TGT: forall loc0,
                   lo loc0 = Ordering.nonatomic -> (mem_tgt loc0) = (mem_tgt' loc0)).
        {
          clear - LOCAL0 AT_LOC.
          ii. eapply Local_write_disj_loc_stable; eauto.
          ii; subst. rewrite AT_LOC in H. ss.
        }
        assert (NA_LOC_STABLE_SRC: forall loc0,
                   lo loc0 = Ordering.nonatomic -> (mem_src loc0) = (mem2' loc0)).
        {
          clear - WRITE2 AT_LOC.
          ii. eapply Local_write_disj_loc_stable; eauto.
          ii; subst. rewrite AT_LOC in H. ss.
        }
        assert (W_REL_VIEWINJ: opt_ViewInj inj'0 released releasedw2).
        {
          inv LOCAL0. inv LC2. inv WRITE2. inv LC2. simpl. 
          eapply opt_ViewInj_write_released_inj_general; eauto.
          {
            eapply incr_inj_ViewInj; eauto.
            clear - VIEW_MATCH AT_LOC. inv VIEW_MATCH. eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
            inv LOCAL_WF_TGT; eauto. simpl in INV; des; eauto.
          }
          {
            introv ORD. eapply incr_inj_ViewInj; eauto.
            clear - AI_INTERP AT_LOC AT_ORD ORD.
            unfold transf_instr in AI_INTERP. destruct ai'.
            destruct ord; ss. ii. des.
            eapply sem_live_loc_all; eauto.
            ii. des. eapply sem_live_loc_all; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
            inv LOCAL_WF_TGT; eauto. simpl in INV; des; eauto.
          }
          {
            eapply incr_inj_closed_tviewInj; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
            inv LOCAL_WF_TGT; eauto. simpl in INV; des; eauto.
          }
          {
            des_if; eauto. simpl in o. destruct o; ss.
          }
          econs; eauto. econs; eauto.
        }
        assert (INJ_MEM': MsgInj inj'0 mem_tgt' mem2').
        {
          eapply write_step_msgInj_stable; eauto.
          clear - INV. ss. des; eauto.
          subst. des_if; eauto. simpl in o. des1; ss.
        }
        do 6 eexists. exists inj'0. splits.
        {
          (* source execution *)
          econs.
          2: { eapply Local.step_write; eauto. }
          simpl. econs; eauto.
          clear - AI_INTERP AT_ORD.
          unfold transf_instr in *. destruct ai'; ss.
          destruct ord; tryfalse; try solve [symmetry; eapply ai_interp_live_regs_eq; eauto].
        }
        {
          (* incr inj *)
          clear - INCR_INJ ATM_BIT. eapply incr_inj_transitivity with (inj' := inj'); eauto.
          des; subst; ss; eauto.
        }
        {
          (* match state *)
          econs; eauto.
          {
            (* I dce *)
            clear ATM_BIT.  simpl in INV. des.
            econs; eauto.
            inv LOCAL0; ss. eapply incr_inj_TMapInj; eauto.
            eapply closed_tm_to_closed_TMapInj; eauto.
            splits; eauto. subst inj'0. eapply INJ_MEM'.
            ii.
            assert (GET': Memory.get loc to' mem_src = Some (from', Message.concrete val R')).
            {
              clear - H AT_LOC H2 NA_LOC_STABLE_SRC.
              unfold Memory.get in *. rewrite NA_LOC_STABLE_SRC; eauto.
            }
            exploit TS_RSV; eauto. des_ifH H0. simpl in a. des1; subst. rewrite AT_LOC in H2. ss.
            eauto.
            ii. do 2 des1. exists to_r. split; eauto.
            introv ITV COVER. eapply x0 in ITV. contradiction ITV.
            inv COVER. econs. 2: { eapply ITV0. }
            unfold Memory.get in *. rewrite NA_LOC_STABLE_SRC; eauto.
            ii. eapply Local_write_rsv_prsv in WRITE2.
            eapply WRITE2 in H. eauto.
            ii. des_ifH H0. simpl in a. des1; subst. inv H0; eauto. eauto.
            eapply write_step_closed_mem; eauto.
          }
          {
            (* match state tlocal *)
            inv LOCAL0. inv LC2. inv WRITE2. inv LC2.
            unfold transf_instr in AI_INTERP. destruct ai'; simpl in AI_INTERP.
            econs; eauto. econs; eauto.
            destruct ord; tryfalse.
            eapply ai_interp_write_stable; eauto. des_if; eauto. simpl in o. des1; ss.
            eapply ai_interp_write_stable; eauto. des_if; eauto. simpl in o. des1; ss.
            eapply ai_interp_write_stable with (e := e); eauto.
            clear - AI_INTERP.
            eapply ge_ai_interp_prsv; eauto. econs; ss; eauto.
            eapply NREG.ge_refl. econs; eauto. destruct n0; eauto.
            unfold LocSet.Subset. ii; ss. eapply LocSet.Facts.empty_iff in H. ss.
            des_if; ss. destruct o; ss.
            eapply ai_interp_write_stable with (e := e); eauto.
            clear - AI_INTERP.
            eapply ge_ai_interp_prsv; eauto. econs; ss; eauto.
            eapply NREG.ge_refl. econs; eauto. destruct n0; eauto.
            unfold LocSet.Subset. ii; ss. eapply LocSet.Facts.empty_iff in H. ss.
            des_if; eauto. simpl in o. des1; ss.
          }
          {
            (* InvView dce *)
            inversion LOCAL0. simpl in LC2. inversion LC2. clear LC2.
            inversion WRITE2. inversion LC2. clear LC2.  subst.
            eapply InvView_dce_write; eauto.
            inv WRITABLE; ss; eauto. inv WRITABLE0; ss; eauto.
            des_if; eauto. simpl in o. des1; ss.
            introv DISJ.  des_if; ss. des; subst; ss.
            introv DISJ_LOC. eapply Local_write_disj_loc_stable; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
            inv LOCAL_WF_TGT; eauto. simpl in INV. des; eauto.
            ii; ss.
            clear - AI_INTERP H. unfold transf_instr in *.
            destruct ai'; ss. destruct ord; ss; try solve [des; eapply sem_live_loc_all; eauto].
          }
          {
            (* cur acq *)
            inversion LOCAL0. simpl in LC2. inversion LC2. clear LC2.
            inversion WRITE2. inversion LC2. clear LC2.
            eapply cur_acq_write_prsv; eauto. subst inj'0; eauto.
            subst inj'0; eauto.
            inv WRITABLE; ss; eauto. inv WRITABLE0; ss; eauto.
            des_if; eauto. simpl in o. des1; ss.
          }
          {
            (* cur acq pln *)
            inversion LOCAL0. simpl in LC2. inversion LC2. clear LC2.
            inversion WRITE2. inversion LC2. clear LC2.
            eapply cur_acq_pln_write_prsv; eauto.
            subst inj'0; eauto. subst inj'0; eauto.
            inv WRITABLE; ss; eauto. inv WRITABLE0; ss; eauto.
            des_if; eauto. simpl in o. des; ss.
          }
          {
            (* promises relation *)
            eapply promises_relation_inj_write_kind_match_prsv; eauto.
            eapply promises_relation_rely_stable; eauto.
            clear - ATM_BIT INCR_INJ.
            eapply incr_inj_transitivity; eauto. des; subst; eauto.
            unfold incr_inj; ii; eauto. unfold incr_inj; ii; eauto.
            subst. des_if; eauto. simpl in o. des1; ss.
          }
          {
            (* Local wf tgt *)
            eapply local_wf_write; eauto.
          }
          {
            (* memory closed timemap tgt *)
            clear - CLOSED_SC_TGT LOCAL0. inv LOCAL0. inv LC2. ss.
            inv WRITE. inv PROMISE; ss.
            eapply Memory.add_closed_timemap; eauto.
            eapply Memory.split_closed_timemap; eauto.
            eapply Memory.lower_closed_timemap; eauto.
          }
          {
            (* memory closed tgt *)
            eapply write_step_closed_mem; eauto.
          }
          {
            (* local wf src *)
            eapply local_wf_write; eauto.
            clear - INV. ss. des; eauto.
          }
          {
            (* memory closed timemap src *)
            clear - CLOSED_SC_SRC WRITE2. inv WRITE2. inv LC2. ss.
            inv WRITE. inv PROMISE; ss.
            eapply Memory.add_closed_timemap; eauto.
            eapply Memory.split_closed_timemap; eauto.
            eapply Memory.lower_closed_timemap; eauto.
          }
        }
        simpl. des; eauto.
      }
    + (* print *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      unfold transf_instr in AI_INTERP. destruct ai' as (nr, nm).
      assert (VIEW_INJ_CUR_ACQ: 
                ViewInj inj' (TView.cur tview_tgt) (TView.cur tview_src) /\
                ViewInj inj' (TView.acq tview_tgt) (TView.acq tview_src)).
      {
        clear - AI_INTERP. unfold ai_interp in AI_INTERP. des.
        split. eapply sem_live_loc_all; eauto. eapply sem_live_loc_all'; eauto.
      }
      destruct VIEW_INJ_CUR_ACQ as (VIEW_INJ_CUR & VIEW_INJ_ACQ).
      assert (VIEW_INJ_SC: TMapInj inj' sc_tgt sc_src).
      {
        clear - INV. ss. des. eauto.
      }
      inv TGT_STEP. inv STEP. simpl in AT_OR_OUT; tryfalse.
      inv STEP; try solve [simpl in AT_OR_OUT; tryfalse].
      inv STATE; tryfalse. inv BLK. destruct te; simpl in H0; tryfalse. inv H0.
      inv LOCAL. inv LOCAL0. inv LC2. simpl in RELEASE.
      do 6 eexists. exists inj'.
      splits.
      {
        (* source execution *)
        econs.   
        2: { eapply Local.step_syscall; eauto.
             econs; eauto; simpl.
             inv PROM_INJ.

             introv ORD. eapply RELEASE in ORD.
             eapply rel_promises_inj_nonsynch; eauto.
             {
               instantiate (1 := inj'). clear - ATM_BIT.
               des; subst; eauto. unfold incr_inj; ii; eauto.
             }
             {
               simpl in INV. des; eauto.
             }
             {
               inv LOCAL_WF_TGT; eauto.
             }
             {
               inv LOCAL_WF_SRC; eauto.
             }

             introv ORD_SEQCST. eapply PROMISES in ORD_SEQCST. simpl in ORD_SEQCST.
             subst prm_tgt. eapply promises_relation_bot; eauto.
             clear - INV LOCAL_WF_SRC. ss; des. ii.
             eapply NO_RSVs; eauto. inv LOCAL_WF_SRC; ss. eauto.
        }
        simpl. econs; eauto.
      }
      {
        (* incr inj *)
        clear - ATM_BIT. des; subst; eauto.
        unfold incr_inj; ii; eauto.
      }
      {
        (* match state dce *)
        simpl.
        econs; eauto.
        {
          (* Inv dce *)
          clear ATM_BIT. simpl in INV. des. 
          econs; eauto. 
          eapply TMapInj_sc_fence; eauto.
          unfold TView.read_fence_tview; simpl.
          assert (ORD: Ordering.le Ordering.acqrel Ordering.seqcst = true). eauto.
          rewrite ORD. clear - VIEW_INJ_ACQ. unfold ViewInj in *.
          destruct tview_tgt, tview_src; ss; eauto. destruct acq, acq0; ss. des; eauto.
          eapply closed_tviewInj_read_fence; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; eauto.
          eapply closed_tm_to_closed_TMapInj; eauto.
          inv INJ_MEM; eauto.
        }
        {
          (* match state tlocal *)
          econs; eauto. econs; eauto.
          eapply ai_interp_scfence_prsv; eauto.
          eapply ai_interp_read_fence; eauto.
          eapply ai_interp_set_expr_live; eauto.
          eapply closed_tviewInj_read_fence; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          inv LOCAL_WF_TGT; eauto. simpl in INV. des; eauto.
          eapply closed_tm_to_closed_TMapInj; eauto.
          simpl in INV; des; eauto.
          simpl in INV. clear ATM_BIT. des. inv INJ_MEM; eauto.
        }
        {
          (* Inv View dce *)
          eapply InvView_dce_write_fence; eauto.
          eapply closed_tviewInj_read_fence; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          inv LOCAL_WF_TGT; eauto. simpl in INV. des; eauto.
          eapply closed_tm_to_closed_TMapInj; eauto. simpl in INV; des; eauto.
          clear - INV. ss. des. inv INJ_MEM; eauto.
        }
        {
          (* cur acq *)
          eapply cur_acq_write_sc_fence; eauto.
          eapply cur_acq_read_fence; eauto.
          inv LOCAL_WF_SRC; ss.
          exploit TViewFacts.read_fence_future; eauto. i. des1; eauto.
          eapply closed_tm_to_closed_TMapInj; eauto. simpl in INV; des; eauto.
          clear - INV. ss. des. inv INJ_MEM; eauto.
        }
        {
          (* cur acq pln *)
          eapply cur_acq_pln_sc_fence_write; eauto.
          eapply closed_tviewInj_read_fence; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          inv LOCAL_WF_TGT; eauto. simpl in INV. des; eauto.
          eapply closed_tm_to_closed_TMapInj; eauto. simpl in INV; des; eauto.
          clear - INV. ss. des. inv INJ_MEM; eauto.
          eapply cur_acq_pln_read_fence; eauto.
          inv LOCAL_WF_TGT; eauto. inv LOCAL_WF_SRC; eauto.
        }
        {
          (* promises relation *)
          eapply promises_relation_rely_stable; eauto.
          clear - ATM_BIT. des; subst; eauto. unfold incr_inj in *; ii; eauto.
        }
        {
          (* local wf tgt *)
          eapply local_wf_fence; eauto.
        }
        {
          (* memory closed tgt *)
          exploit TViewFacts.read_fence_future.
          inv LOCAL_WF_TGT. eauto. simpl. inv LOCAL_WF_TGT; eauto.
          simpl. i. des1.
          exploit TViewFacts.write_fence_future; eauto.
          i. do 2 des1. eauto.
        }
        {
          (* local wf src *)
          eapply local_wf_fence; eauto.
          clear - INV. ss. des; eauto.
        }
        {
          (* memory closed src *)
          inv LOCAL_WF_SRC. ss. 
          exploit TViewFacts.read_fence_future; [eapply TVIEW_WF | eauto..].
          i. des1.
          exploit TViewFacts.write_fence_future; [| eapply WF_TVIEW | eauto..].
          clear - INV. des; eauto.
          i. do 2 des1; eauto.
        }
      }
      simpl.
      eapply ai_interp_live_regs_eq in AI_INTERP. rewrite AI_INTERP; eauto.
    + (* cas *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      pose proof (nonatomic_or_atomic or) as ORD.
      destruct ORD as [NA_ORD | AT_ORD].
      { 
        subst or. clear - TGT_STEP AT_OR_OUT.
        inv TGT_STEP; ss. inv STEP; ss. inv STEP; ss.
        inv STATE; ss. destruct te; ss. inv H0. inv BLK. ss.
        inv BLK. destruct te; ss.
      }
      {
        unfold transf_instr in AI_INTERP. destruct ai' as (nr & nm).
        assert (READ_VAL_EQ: RegFile.eval_expr er R_tgt = RegFile.eval_expr er R_src).
        {
          clear - AI_INTERP. des_ifH AI_INTERP; eauto.
          unfold ai_interp in *. des.
          eapply sem_live_reg_less in AI_INTERP.
          eapply sem_live_reg_regs_eq; eauto.
          unfold ai_interp in *. des.
          eapply sem_live_reg_less in AI_INTERP.
          eapply sem_live_reg_regs_eq; eauto.
        }
        assert (WRITE_VAL_EQ: RegFile.eval_expr ew R_tgt = RegFile.eval_expr ew R_src).
        {
          clear - AI_INTERP. des_ifH AI_INTERP; eauto.
          unfold ai_interp in *. des.
          eapply sem_live_reg_regs_eq; eauto.
          unfold ai_interp in *. des.
          eapply sem_live_reg_regs_eq; eauto.
        }
        inv TGT_STEP. inv STEP. simpl in AT_OR_OUT. tryfalse.
        inv STEP. inv STATE; try solve [destruct te; ss].
        destruct te; simpl in H0; tryfalse. inv H0. inv BLK.

        (* update step *)
        assert (AT_LOC: lo loc1 = Ordering.atomic).
        {
          clear - AT_ORD LOCAL. destruct (lo loc1) eqn:LOC_TYPE; eauto.
          inv LOCAL. inv LOCAL1.
          rewrite LOC_TYPE in LO. destruct ordr; ss.
        }
        exploit InvView_dce_at_loc; eauto. ii. do 3 des1.
        inv LOCAL. destruct lc2. renames tview to tview_tgt0, promises to prm_tgt0.
        exploit injection_read; eauto. inv INV. des; eauto.
        instantiate (1 := prm_src). ii. do 8 des1.
        assert (prm_tgt = prm_tgt0).
        {
          inv LOCAL1; subst. simpl in LC2. inv LC2. eauto.
        }
        subst prm_tgt0.
        assert (LOCAL_WF_TGT': Local.wf (Local.mk tview_tgt0 prm_tgt) mem_tgt).
        {
          eapply local_wf_read; eauto.
        }
        renames tview_src' to tview_src0.
        assert (LOCAL_WF_SRC': Local.wf (Local.mk tview_src0 prm_src) mem_src).
        {
          eapply local_wf_read; eauto. simpl in INV; des; eauto.
        }
        assert (INV_VIEW_MATCH': InvView_dce inj' lo tview_tgt0 tview_src0 mem_src).
        {
          inv LOCAL1. inv LC2. inv LOCAL_READ_SRC. inv LC2.
          eapply InvView_dce_read_prsv; eauto.
          eapply closed_optview_msginj_implies_closed_viewInj; eauto.
          simpl in INV. des; eauto.
          simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
        }
        assert (AI_INTERP_READ: 
                  ai_interp inj' (RegFun.add r Int.one R_tgt) tview_tgt0 
                            (RegFun.add r Int.one R_src) tview_src0
                            (nr, if Ordering.le Ordering.acqrel ordw then (NMem LocSet.empty) else nm)).
        {
          inv LOCAL1. inv LC2. inv LOCAL_READ_SRC. inv LC2.
          eapply ai_interp_read_prsv'; eauto.
          clear - AI_INTERP.
          unfold ai_interp in *.
          destruct (Ordering.le ordw Ordering.strong_relaxed) eqn:ORD'; ss.
          des. split; eauto.
          eapply sem_live_reg_less in AI_INTERP. eapply sem_live_reg_less in AI_INTERP. eauto.
          destruct (Ordering.le Ordering.acqrel ordw) eqn:ORD''; ss; eauto.
          destruct ordw; ss.
          des. split.
          eapply sem_live_reg_less in AI_INTERP. eapply sem_live_reg_less in AI_INTERP. eauto.
          destruct (Ordering.le Ordering.acqrel ordw) eqn:ORD''; ss; eauto.
          destruct ordw; ss.
          eapply closed_optview_msginj_implies_closed_viewInj; eauto.
          simpl in INV. des; eauto.
          simpl in INV. des; inv INJ_MEM; eauto.
        }
        assert (CUR_ACQ': cur_acq lo inj' (TView.cur tview_tgt0) (TView.acq tview_tgt0)
                                  (TView.cur tview_src0) (TView.acq tview_src0)).
        {
          inv LOCAL1. inv LC2. inv LOCAL_READ_SRC. inv LC2.
          eapply cur_acq_read_prsv; eauto.
          eapply closed_optview_msginj_implies_closed_viewInj; eauto.
          simpl in INV. des; eauto.
          simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
        }
        assert (CUR_ACQ_PLN': cur_acq_pln lo inj' (TView.cur tview_tgt0) (TView.acq tview_tgt0)
                                          (TView.cur tview_src0) (TView.acq tview_src0)).
        {
          inv LOCAL1. inv LC2. inv LOCAL_READ_SRC. inv LC2.
          eapply cur_acq_pln_read_prsv; eauto.
          eapply closed_optview_msginj_implies_closed_viewInj; eauto.
          simpl in INV. des; eauto.
          simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
        }
        assert (tsr = to').
        {
          clear - INJ_TO INV AT_LOC. ss. des.
          eapply ID_ATOMIC in INJ_TO; eauto.
        }
        subst to'.
        exploit Mem_at_eq_local_write_prsv; eauto.
        {
          simpl in INV. des; eauto.
        }
        {
          simpl. eauto.
        }
        {
          simpl. inv PROM_INJ; eauto.
          eapply rel_promises_rely_stable; eauto.
          clear - ATM_BIT. des; subst; eauto. unfold incr_inj; ii; eauto.
        }
        {
          simpl in INV. clear - INV. des; subst. inv INJ_MEM; eauto.
        }
        {
          simpl. clear - INV_VIEW_MATCH' AT_LOC. inv INV_VIEW_MATCH'. eauto.
        }
        {
          clear - AI_INTERP_READ AT_LOC AT_ORD. introv ORD.
          destruct ordw; ss. des_ifH AI_INTERP_READ; ss.
          des. eapply sem_live_loc_all; eauto.
          des_ifH AI_INTERP_READ; ss.
          des. eapply sem_live_loc_all; eauto.
        }
        {
          simpl. eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          inv LOCAL_WF_TGT'; eauto. instantiate (1 := mem_src).
          clear - INV. ss. des; eauto.
        }
 
        ii. exploit x0; eauto.
        {
          eapply closed_optview_msginj_implies_closed_viewInj; eauto.
          simpl in INV. des; eauto.
        }
        {
          simpl in INV. des; eauto.
        }
        clear x0. instantiate (1 := sc_src). ii. do 12 des1.
        destruct lc2'. renames tview to tview_src', promises to prm_src'.
        assert (NA_LOC_STABLE_TGT: forall loc0,
                   lo loc0 = Ordering.nonatomic -> (mem_tgt loc0) = (mem_tgt' loc0)).
        {
          clear - LOCAL2 AT_LOC.
          ii. eapply Local_write_disj_loc_stable; eauto.
          ii; subst. rewrite AT_LOC in H. ss.
        }
        assert (NA_LOC_STABLE_SRC: forall loc0,
                   lo loc0 = Ordering.nonatomic -> (mem_src loc0) = (mem2' loc0)).
        {
          clear - WRITE2 AT_LOC.
          ii. eapply Local_write_disj_loc_stable; eauto.
          ii; subst. rewrite AT_LOC in H. ss.
        }
        assert (W_REL_VIEWINJ: opt_ViewInj inj'0 releasedw releasedw2).
        {
          inv LOCAL2. inv LC2. inv WRITE2. inv LC2. simpl. 
          eapply opt_ViewInj_write_released_inj_general; eauto.
          {
            eapply incr_inj_ViewInj; eauto.
            clear - INV_VIEW_MATCH' AT_LOC. inv INV_VIEW_MATCH'. eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
            inv LOCAL_WF_TGT'; eauto. simpl in INV; des; eauto.
          }
          {
            introv ORD. eapply incr_inj_ViewInj; eauto.
            clear - AI_INTERP_READ AT_LOC AT_ORD ORD.
            des_ifH AI_INTERP_READ; ss. des.
            eapply sem_live_loc_all; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
            inv LOCAL_WF_TGT'; eauto. simpl in INV; des; eauto.
          }
          {
            eapply incr_inj_closed_tviewInj; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
            inv LOCAL_WF_TGT'; eauto. simpl in INV; des; eauto.
          }
          {
            des_if; eauto. simpl in o. destruct o; ss.
          }
          eapply incr_inj_opt_ViewInj; eauto.
          eapply closed_optview_msginj_implies_closed_viewInj; eauto.
          simpl in INV. des; eauto.
          eapply incr_inj_closed_opt_ViewInj; eauto.
          eapply closed_optview_msginj_implies_closed_viewInj; eauto.
          simpl in INV. des; eauto.
        }
        assert (INJ_MEM': MsgInj inj'0 mem_tgt' mem2').
        {
          eapply write_step_msgInj_stable; eauto.
          clear - INV. ss. des; eauto.
          subst. des_if; eauto. simpl in o. des1; ss.
        }
        do 6 eexists. exists inj'0. splits.
        {
          (* source execution *)
          econs. 
          2: { eapply Local.step_update; eauto. }
          simpl. econs; eauto.
        }
        {
          (* incr inj *)
          clear - INCR_INJ ATM_BIT. eapply incr_inj_transitivity with (inj' := inj'); eauto.
          des; subst; ss; eauto.
        }
        {
          (* match state *)
          econs; eauto.
          {
            (* I dce *)
            clear ATM_BIT.  simpl in INV. des.
            econs; eauto.
            inv LOCAL2; ss. eapply incr_inj_TMapInj; eauto.
            eapply closed_tm_to_closed_TMapInj; eauto.
            splits; eauto. subst inj'0. eapply INJ_MEM'.
            ii.
            assert (GET': Memory.get loc to' mem_src = Some (from', Message.concrete val R'0)).
            {
              clear - H AT_LOC H2 NA_LOC_STABLE_SRC.
              unfold Memory.get in *. rewrite NA_LOC_STABLE_SRC; eauto.
            }
            exploit TS_RSV; eauto. des_ifH H0. simpl in a. des1; subst. rewrite AT_LOC in H2. ss.
            eauto.
            ii. do 2 des1. exists to_r. split; eauto.
            introv ITV COVER. eapply x0 in ITV. contradiction ITV.
            inv COVER. econs. 2: { eapply ITV0. }
            unfold Memory.get in *. rewrite NA_LOC_STABLE_SRC; eauto.
            ii. eapply Local_write_rsv_prsv in WRITE2.
            eapply WRITE2 in H. eauto.
            ii. des_ifH H0. simpl in a. des1; subst. inv H0; eauto. eauto.
            eapply write_step_closed_mem. 2: { eapply WRITE2; eauto. }
            inv LOCAL_READ_SRC. inv LC2. eapply closed_mem_implies_closed_msg; eauto.
            eauto. eauto.
          }
          {
            (* match state tlocal *)
            inv LOCAL2. inv LC2. inv WRITE2. inv LC2.
            econs; eauto. econs; eauto.
            destruct (Ordering.le Ordering.acqrel ordw) eqn:ORDW.
            eapply ai_interp_write_stable'; eauto.
            clear - AI_INTERP_READ. eapply ge_ai_interp_prsv; eauto.
            econs; ss; eauto. eapply NREG.ge_refl; eauto. econs; eauto.
            destruct nm; ss. ii. eapply LocSet.Facts.empty_iff in H. ss.
            des_if; eauto. simpl in o. des1; ss.
            eapply ai_interp_write_stable'; eauto.
            des_if; eauto. simpl in o. des1; ss.
          }
          {
            (* InvView dce *)
            inversion LOCAL2. simpl in LC2. inversion LC2. clear LC2.
            inversion WRITE2. inversion LC2. clear LC2.  subst.
            eapply InvView_dce_write; eauto.
            inv WRITABLE; ss; eauto. inv WRITABLE0; ss; eauto.
            des_if; eauto. simpl in o. des1; ss.
            introv DISJ.  des_if; ss. des; subst; ss.
            introv DISJ_LOC. eapply Local_write_disj_loc_stable; eauto.
            eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
            inv LOCAL_WF_TGT'; eauto. simpl in INV. des; eauto.
            ii; ss.
            clear - AI_INTERP_READ H. des.
            destruct ordw; ss; try solve [des; eapply sem_live_loc_all; eauto].
          }
          {
            (* cur acq *)
            inversion LOCAL2. simpl in LC2. inversion LC2. clear LC2.
            inversion WRITE2. inversion LC2. clear LC2.
            eapply cur_acq_write_prsv; eauto. subst inj'0; eauto.
            subst inj'0; eauto.
            inv WRITABLE; ss; eauto. inv WRITABLE0; ss; eauto.
            des_if; eauto. simpl in o. des1; ss.
          }
          {
            (* cur acq pln *)
            inversion LOCAL2. simpl in LC2. inversion LC2. clear LC2.
            inversion WRITE2. inversion LC2. clear LC2.
            eapply cur_acq_pln_write_prsv; eauto.
            subst inj'0; eauto. subst inj'0; eauto.
            inv WRITABLE; ss; eauto. inv WRITABLE0; ss; eauto.
            des_if; eauto. simpl in o. des; ss.
          }
          {
            (* promises relation *)
            eapply promises_relation_inj_write_kind_match_prsv; eauto.
            eapply promises_relation_rely_stable; eauto.
            clear - ATM_BIT INCR_INJ.
            eapply incr_inj_transitivity; eauto. des; subst; eauto.
            unfold incr_inj; ii; eauto.
            unfold incr_inj; ii; eauto.
            subst. des_if; eauto. simpl in o. des1; ss.
          }
          {
            (* Local wf tgt *)
            eapply local_wf_write; eauto.
          }
          {
            (* memory closed timemap tgt *)
            clear - CLOSED_SC_TGT LOCAL2. inv LOCAL2. inv LC2. ss.
            inv WRITE. inv PROMISE; ss.
            eapply Memory.add_closed_timemap; eauto.
            eapply Memory.split_closed_timemap; eauto.
            eapply Memory.lower_closed_timemap; eauto.
          }
          {
            (* memory closed tgt *)
            eapply write_step_closed_mem; eauto.
          }
          {
            (* local wf src *)
            eapply local_wf_write; eauto.
            clear - INV. ss. des; eauto.
          }
          {
            (* memory closed timemap src *)
            clear - CLOSED_SC_SRC WRITE2. inv WRITE2. inv LC2. ss.
            inv WRITE. inv PROMISE; ss.
            eapply Memory.add_closed_timemap; eauto.
            eapply Memory.split_closed_timemap; eauto.
            eapply Memory.lower_closed_timemap; eauto.
          }
        }
        simpl. rewrite READ_VAL_EQ, WRITE_VAL_EQ. splits; eauto.

        (* read case *)
        destruct te; tryfalse. simpl in H0. inv H0. inv LOCAL. inv BLK.
        assert (AT_LOC: lo loc1 = Ordering.atomic).
        {
          clear - AT_ORD LOCAL0 ATOMIC. destruct (lo loc1) eqn:LOC_TYPE; eauto.
          inv LOCAL0. inv LC2. ss. rewrite LOC_TYPE in LO; ss.
        }
        exploit InvView_dce_at_loc; eauto. ii. do 3 des1.
        exploit injection_read; eauto. inv INV. des; eauto.
        instantiate (1 := prm_src). ii. do 8 des1.
        do 6 eexists. exists inj'.
        split.
        {
          (* source read step *)
          econs.
          2: { eapply Local.step_read; eauto. }
          simpl. eapply State.step_cas_flip; eauto.
          rewrite <- READ_VAL_EQ; eauto.
        }
        {
          (* match state preservation *)
          split. clear - ATM_BIT. des; subst; eauto. unfold incr_inj; ii; eauto.
          split; simpl; eauto.
          inv LOCAL0. simpl in LC2. inv LC2. simpl in READABLE.
          inv LOCAL_READ_SRC. simpl in LC2. inv LC2. simpl in READABLE0.
          econs; eauto.
          {
            (* match state tlocal *)
            econs; eauto. econs; eauto. 
            eapply ai_interp_read_prsv'; eauto.
            clear - AI_INTERP. des_ifH AI_INTERP.
            unfold ai_interp in *; ss. des.
            econs; eauto. repeat (eapply sem_live_reg_less in AI_INTERP; eauto).
            unfold ai_interp in *; ss. des.
            splits; eauto.
            repeat (eapply sem_live_reg_less in AI_INTERP; eauto).
            eapply ge_sem_live_loc; eauto. unfold nmem_ge; ii. destruct nm; ss.
            ii. eapply LocSet.Facts.empty_iff in H. ss.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* InvView *)
            eapply InvView_dce_read_prsv; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* cur acq *)
            eapply cur_acq_read_prsv; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* cur acq pln *)
            eapply cur_acq_pln_read_prsv; eauto.
            eapply closed_optview_msginj_implies_closed_viewInj; eauto.
            simpl in INV. des; eauto.
            simpl in INV. destruct INV as (TMAP_INJ & MSG_INJ & _). inv MSG_INJ; eauto.
          }
          {
            (* promise relation *)
            clear - ATM_BIT PROM_INJ. des; subst; eauto.
            eapply promises_relation_rely_stable; eauto.
          }
          {
            (* Local wf tgt *)
            eapply local_wf_read; eauto. econs; eauto.
          }
          {
            (* Local wf src *)
            eapply local_wf_read; eauto. econs; eauto.
            clear - INV. ss; des; eauto.
          }

          clear - INV AT_LOC INJ_TO. ss. des.
          exploit ID_ATOMIC; eauto.
        }
      }
    + (* release fence *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      unfold transf_instr in AI_INTERP. destruct ai' as (nr, nm).
      assert (VIEW_INJ_CUR: ViewInj inj' (TView.cur tview_tgt) (TView.cur tview_src)).
      {
        clear - AI_INTERP. unfold ai_interp in AI_INTERP. des.
        eapply sem_live_loc_all; eauto.
      }
      inv TGT_STEP. inv STEP. simpl in AT_OR_OUT; tryfalse.
      inv STEP; try solve [simpl in AT_OR_OUT; tryfalse].
      inv STATE; tryfalse. inv BLK. destruct te; simpl in H0; tryfalse. inv H0.
      inv LOCAL. inv LOCAL0. inv LC2. simpl in RELEASE.
      do 6 eexists. exists inj'.
      splits.
      {
        (* source execution *)
        econs. 
        2: { eapply Local.step_fence; eauto.
             instantiate (5 := Ordering.relaxed).
             instantiate (4 := Ordering.acqrel). econs; eauto; simpl.
             inv PROM_INJ.

             introv ORD. eapply RELEASE in ORD.
             eapply rel_promises_inj_nonsynch; eauto.
             {
               instantiate (1 := inj'). clear - ATM_BIT.
               des; subst; eauto. unfold incr_inj; ii; eauto.
             }
             {
               simpl in INV. des; eauto.
             }
             {
               inv LOCAL_WF_TGT; eauto.
             }
             {
               inv LOCAL_WF_SRC; eauto.
             }
             ii; ss.
        }
        simpl. econs; eauto.
      }
      {
        (* incr inj *)
        clear - ATM_BIT. des; subst; eauto.
        unfold incr_inj; ii; eauto.
      }
      {
        (* match state dce *)
        simpl.
        econs; eauto.
        {
          (* match state local *)
          econs; eauto. econs; eauto.
          eapply ai_interp_write_fence; eauto.
          eapply ai_interp_read_fence; eauto.
          eapply ge_ai_interp_prsv; eauto. econs; ss; eauto.
          eapply NREG.ge_refl; eauto. econs; eauto.
          destruct nm; eauto. introv EMPTY. eapply LocSet.Facts.empty_iff in EMPTY; ss.
          ii; tryfalse. 
        } 
        {
          (* Inv View dce *)
          eapply InvView_dce_write_fence_prsv; eauto.
          eapply InvView_dce_read_fence_prsv; eauto.
          ii; ss.
        }
        {
          (* cur acq *)
          eapply cur_acq_write_fence; eauto. ii; ss.
        }
        {
          (* cur acq pln *)
          eapply cur_acq_pln_write_fence; eauto. ii; ss.
        }
        {
          (* promise rel *)
          eapply promises_relation_rely_stable; eauto.
          clear - ATM_BIT. des; subst; eauto. unfold incr_inj; ii; eauto.
        }
        {
          (* local wf tgt *)
          eapply local_wf_fence; eauto.
        }
        {
          (* local wf src *)
          eapply local_wf_fence; eauto.
          clear - INV. ss. des; eauto.
        }
      }
      simpl. eauto.
    + (* acquire fence *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      unfold transf_instr in AI_INTERP. destruct ai' as (nr, nm).
      inv TGT_STEP. inv STEP. simpl in AT_OR_OUT; tryfalse.
      inv STEP; try solve [simpl in AT_OR_OUT; tryfalse].
      inv STATE; tryfalse. inv BLK. destruct te; simpl in H0; tryfalse. inv H0.
      inv LOCAL. inv LOCAL0. inv LC2. simpl in RELEASE.
      do 6 eexists. exists inj'.
      splits.
      {
        (* source execution *)
        econs. 
        2: { eapply Local.step_fence; eauto.
             instantiate (5 := Ordering.acqrel).
             instantiate (4 := Ordering.relaxed). econs; eauto; simpl.
             inv PROM_INJ.

             introv ORD. eapply RELEASE in ORD.
             eapply rel_promises_inj_nonsynch; eauto.
             {
               instantiate (1 := inj'). clear - ATM_BIT.
               des; subst; eauto. unfold incr_inj; ii; eauto.
             }
             {
               simpl in INV. des; eauto.
             }
             {
               inv LOCAL_WF_TGT; eauto.
             }
             {
               inv LOCAL_WF_SRC; eauto.
             }
             ii; ss.
        }
        simpl. econs; eauto.
      }
      {
        (* incr inj *)
        clear - ATM_BIT. des; subst; eauto.
        unfold incr_inj; ii; eauto.
      }
      {
        (* match state dce *)
        simpl.
        econs; eauto.
        {
          (* match state local *)
          econs; eauto. econs; eauto.
          eapply ai_interp_write_fence; eauto.
          eapply ai_interp_read_fence; eauto.
          ii; tryfalse.
        } 
        {
          (* Inv View dce *)
          eapply InvView_dce_write_fence_prsv; eauto.
          eapply InvView_dce_read_fence_prsv; eauto.
          ii; ss. ii; ss.
        }
        {
          (* cur acq *)
          eapply cur_acq_write_fence; eauto.
          eapply cur_acq_read_fence; eauto.
          ii; ss.
        }
        {
          (* cur acq pln *)
          eapply cur_acq_pln_write_fence; eauto.
          eapply cur_acq_pln_read_fence; eauto.
          inv LOCAL_WF_TGT; eauto. inv LOCAL_WF_SRC; eauto. ii; ss.
        }
        {
          (* promise rel *)
          eapply promises_relation_rely_stable; eauto.
          clear - ATM_BIT. des; subst; eauto. unfold incr_inj; ii; eauto.
        }
        {
          (* local wf tgt *)
          eapply local_wf_fence; eauto.
        }
        {
          (* local wf src *)
          eapply local_wf_fence; eauto.
          clear - INV. ss. des; eauto.
        }
      }
      simpl. eauto.
    + (* sc fence *)
      simpl in AI_FOR_CBLK.
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS. 
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
      simpl in TGT_STEP.
      unfold transf_instr in AI_INTERP. destruct ai' as (nr, nm).
      assert (VIEW_INJ_CUR_ACQ: 
                ViewInj inj' (TView.cur tview_tgt) (TView.cur tview_src) /\
                ViewInj inj' (TView.acq tview_tgt) (TView.acq tview_src)).
      {
        clear - AI_INTERP. unfold ai_interp in AI_INTERP. des.
        split. eapply sem_live_loc_all; eauto. eapply sem_live_loc_all'; eauto.
      }
      destruct VIEW_INJ_CUR_ACQ as (VIEW_INJ_CUR & VIEW_INJ_ACQ).
      assert (VIEW_INJ_SC: TMapInj inj' sc_tgt sc_src).
      {
        clear - INV. ss. des. eauto.
      }
      inv TGT_STEP. inv STEP. simpl in AT_OR_OUT; tryfalse.
      inv STEP; try solve [simpl in AT_OR_OUT; tryfalse].
      inv STATE; tryfalse. inv BLK. destruct te; simpl in H0; tryfalse. inv H0.
      inv LOCAL. inv LOCAL0. inv LC2. simpl in RELEASE.
      do 6 eexists. exists inj'.
      splits.
      {
        (* source execution *)
        econs. 
        2: { eapply Local.step_fence; eauto.
             instantiate (5 := Ordering.relaxed).
             instantiate (4 := Ordering.seqcst). econs; eauto; simpl.
             inv PROM_INJ.

             introv ORD. eapply RELEASE in ORD.
             eapply rel_promises_inj_nonsynch; eauto.
             {
               instantiate (1 := inj'). clear - ATM_BIT.
               des; subst; eauto. unfold incr_inj; ii; eauto.
             }
             {
               simpl in INV. des; eauto.
             }
             {
               inv LOCAL_WF_TGT; eauto.
             }
             {
               inv LOCAL_WF_SRC; eauto.
             }

             introv ORD_SEQCST. eapply PROMISES in ORD_SEQCST. simpl in ORD_SEQCST.
             subst prm_tgt. eapply promises_relation_bot; eauto.
             clear - INV LOCAL_WF_SRC. ss; des. ii.
             eapply NO_RSVs; eauto. inv LOCAL_WF_SRC; ss. eauto.
        }
        simpl. econs; eauto.
      }
      {
        (* incr inj *)
        clear - ATM_BIT. des; subst; eauto.
        unfold incr_inj; ii; eauto.
      }
      {
        (* match state dce *)
        simpl.
        econs; eauto.
        {
          (* Inv dce *)
          clear ATM_BIT. simpl in INV. des. 
          econs; eauto. 
          eapply TMapInj_sc_fence; eauto.
          unfold TView.read_fence_tview; simpl.
          assert (ORD: Ordering.le Ordering.acqrel Ordering.relaxed = false). eauto.
          rewrite ORD. clear - VIEW_INJ_CUR. unfold ViewInj in *.
          destruct tview_tgt, tview_src; ss; eauto. destruct cur, cur0; ss. des; eauto.
          eapply closed_tviewInj_read_fence; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; eauto.
          eapply closed_tm_to_closed_TMapInj; eauto.
          inv INJ_MEM; eauto.
        }
        {
          (* match state tlocal *)
          econs; eauto. econs; eauto.
          eapply ai_interp_scfence_prsv; eauto.
          eapply closed_tviewInj_read_fence; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          inv LOCAL_WF_TGT; eauto. simpl in INV. des; eauto.
          eapply closed_tm_to_closed_TMapInj; eauto.
          simpl in INV; des; eauto.
          simpl in INV. clear ATM_BIT. des. inv INJ_MEM; eauto.
        }
        {
          (* Inv View dce *)
          eapply InvView_dce_write_fence; eauto.
          eapply closed_tviewInj_read_fence; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          inv LOCAL_WF_TGT; eauto. simpl in INV. des; eauto.
          eapply closed_tm_to_closed_TMapInj; eauto. simpl in INV; des; eauto.
          clear - INV. ss. des. inv INJ_MEM; eauto.
        }
        {
          (* cur acq *)
          eapply cur_acq_write_sc_fence; eauto.
          inv LOCAL_WF_SRC; ss.
          exploit TViewFacts.read_fence_future; eauto. i. des1; eauto.
          eapply closed_tm_to_closed_TMapInj; eauto. simpl in INV; des; eauto.
          clear - INV. ss. des. inv INJ_MEM; eauto.
        }
        {
          (* cur acq pln *)
          eapply cur_acq_pln_sc_fence_write; eauto.
          eapply closed_tviewInj_read_fence; eauto.
          eapply closed_tview_msginj_implies_closed_tviewInj; eauto.
          inv LOCAL_WF_TGT; eauto. simpl in INV. des; eauto.
          eapply closed_tm_to_closed_TMapInj; eauto. simpl in INV; des; eauto.
          clear - INV. ss. des. inv INJ_MEM; eauto.
        }
        {
          (* promises relation *)
          eapply promises_relation_rely_stable; eauto.
          clear - ATM_BIT. des; subst; eauto. unfold incr_inj in *; ii; eauto.
        }
        {
          (* local wf tgt *)
          eapply local_wf_fence; eauto.
        }
        {
          (* memory closed tgt *)
          exploit TViewFacts.write_fence_future; eauto.
          inv LOCAL_WF_TGT; eauto. simpl. inv LOCAL_WF_TGT; eauto.
          simpl. ii. do 2 des1; eauto.
        }
        {
          (* local wf src *)
          eapply local_wf_fence; eauto.
          clear - INV. ss. des; eauto.
        }
        {
          (* memory closed src *)
          inv LOCAL_WF_SRC. ss. 
          exploit TViewFacts.write_fence_future; [| eapply TVIEW_WF | eauto..].
          clear - INV. des; eauto.
          ii. do 2 des1; eauto.
        }
      }
      simpl. eauto.
Qed.

Lemma promise_step_case
      inj lo te
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_dce inj lo true
                              (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                              (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (TGT_STEP: Thread.step lo false te 
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt'))
      (PROM_CONS: Local.promise_consistent (Local.mk tview_src prm_src)):
  exists state_src' tview_src' prm_src' sc_src' mem_src' inj',
    rtc (Thread.prc_step lo) 
        (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
        (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
    incr_inj inj inj' /\ 
    match_state_dce inj' lo true
                    (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                    (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src').
Proof.
  inv TGT_STEP. inv STEP. inv LOCAL. simpl in PROMISE, LC2.
  symmetry in LC2. inv LC2. inv MATCH.
  destruct kind.
  - (* memory add *)
    destruct msg.
    {
      (* add a new concrete message *)
      exploit promise_add_concrete_I_dce_prsv;
        [eapply PROMISE | | eapply INV | eauto..].
      {
        eapply promises_relation_rely_stable; eauto.
        clear - ATM_BIT. des; subst; ss.
      }
      {
        inv LOCAL_WF_TGT; eauto.
      }
      {
        inv LOCAL_WF_SRC; eauto.
      }
      {
        clear - INV ATM_BIT. des; ss. des; subst.
        inv INJ_MEM; eauto.
      }

      i. do 15 des1.
      do 5 eexists. exists inj'0.
      splits.
      {
        (* source step *)
        eapply Operators_Properties.clos_rt1n_step.
        econs. econs; eauto.
      }
      clear - ATM_BIT INCR_INJ'. des; subst; ss.
      {
        (* match state *)
        econs; eauto; simpl.
        {
          (* match state tlocal *)
          inv MATCH_THRD_LOCAL. econs; eauto.
          inv CUR_STK_FRAME. econs; eauto.
          clear - AI_INTERP INCR_INJ' ATM_BIT.
          unfold ai_interp in *. destruct ai; ss. des; ss.
          split; eauto.
          unfold sem_live_loc in *. ii.
          exploit AI_INTERP0; eauto. ii; eauto.
          des. splits; eauto.
        }
        {
          (* Inv View dce *)
          eapply InvView_dce_rely_stable' with (inj := inj'); eauto.
          clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; ss.
        }
        {
          (* cur acq *)
          eapply cur_acq_rely_stable; eauto.
        }
        {
          (* cur acq pln *)
          eapply cur_acq_pln_rely_stable; eauto.
        }
        {
          (* Local wf tgt *)
          eapply local_wf_promise; eauto.
        }
        {
          (* closed timemap sc *)
          eapply Memory.promise_closed_timemap; eauto.
        }
        { 
          (* closed memory tgt *)
          eapply promise_step_closed_mem with (mem1 := mem_tgt); eauto.
          econs; eauto.
        }
        {
          (* Local wf src *)
          eapply local_wf_promise; eauto.
          clear - INV. ss. des; eauto.
        }
        {
          (* closed timemap sc src *)
          eapply Memory.promise_closed_timemap; eauto.
        }
      }
    }
    {
      (* add a reservation *)
      exploit promise_add_reserve_I_dce_prsv;
        [eapply PROMISE | | eapply INV | eauto..].
      eapply promises_relation_rely_stable; eauto.
      clear - ATM_BIT. des; subst; ss.
      inv LOCAL_WF_TGT; eauto.
      inv LOCAL_WF_SRC; eauto.
      clear - INV. ss. des. inv INJ_MEM; eauto.

      i. do 7 des1.
      exists state_src tview_src prm_src' sc_src mem_src' inj'.
      splits.
      {
        (* source step *)
        des1.
        eapply Operators_Properties.clos_rt1n_step.
        econs. econs; eauto.
        des1; subst. econs; eauto.
      }
      {
        (* incr inj *)
        clear - ATM_BIT. des; subst; ss.
      }
      {
        (* match state *)
        econs; eauto; simpl.
        {
          (* match state tlocal *)
          inv MATCH_THRD_LOCAL. econs; eauto.
        }
        {
          (* Inv View dce *)
          eapply InvView_dce_rely_stable' with
            (inj := inj') (mem_src := mem_src); eauto.
          ii; eauto.
          clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; ss.
        }
        {
          (* Local wf tgt *)
          eapply local_wf_promise; eauto.
        }
        {
          (* closed timemap sc *)
          eapply Memory.promise_closed_timemap; eauto.
        }
        { 
          (* closed memory tgt *)
          eapply promise_step_closed_mem with (mem1 := mem_tgt); eauto.
          econs; eauto.
        }
        {
          (* Local wf src *)
          clear ATM_BIT. des; subst; eauto.
          eapply local_wf_promise; eauto.
          clear - INV. ss. des; eauto.
        }
        {
          (* closed timemap sc src *)
          clear ATM_BIT. des; subst; eauto.
          eapply Memory.promise_closed_timemap; eauto.
        }
      }
    }
  - (* memory split *)  
    lets PROMISE': PROMISE. inv PROMISE'.
    do 2 des1. subst msg3.
    do 2 des1. subst msg. clear TS PROMISES MEM.
    exploit promise_split_I_dce_prsv;
      [eapply PROMISE | | eapply INV | eauto..].
    eapply promises_relation_rely_stable; eauto.
    clear - ATM_BIT. des; subst; ss.
    inv LOCAL_WF_TGT; eauto.
    inv LOCAL_WF_SRC; eauto.
    clear - INV. ss. des. inv INJ_MEM; eauto.

    i. do 15 des1.
    exists state_src tview_src prm_src' sc_src mem_src' inj'0.
    splits.
    {
      (* source step *)
      eapply Operators_Properties.clos_rt1n_step.
      econs. econs; eauto.
    }
    {
      (* incr inj *) 
      clear - ATM_BIT INCR_INJ'. des; subst; ss.
    }
    {
      (* match state *)
      econs; eauto; simpl.
      {
        (* match state tlocal *)
        inv MATCH_THRD_LOCAL. econs; eauto.
        inv CUR_STK_FRAME. econs; eauto.
        clear - AI_INTERP INCR_INJ' ATM_BIT.
        unfold ai_interp in *. destruct ai; ss. des; ss.
        split; eauto.
        unfold sem_live_loc in *. ii.
        exploit AI_INTERP0; eauto. ii; eauto.
        des. splits; eauto.
      }
      {
        (* Inv View dce *)
        eapply InvView_dce_rely_stable' with
            (inj := inj') (mem_src := mem_src); eauto.
        ii; eauto.
        clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; ss.
      }
      {
        (* cur acq *)
        eapply cur_acq_rely_stable; eauto.
      }
      {
        (* cur acq pln *)
        eapply cur_acq_pln_rely_stable; eauto.
      }
      {
        (* Local wf tgt *)
        eapply local_wf_promise; eauto.
      }
      {
        (* closed timemap sc *)
        eapply Memory.promise_closed_timemap; eauto.
      }
      { 
        (* closed memory tgt *)
        eapply promise_step_closed_mem with (mem1 := mem_tgt); eauto.
        econs; eauto.
      }
      {
        (* Local wf src *)
        clear ATM_BIT. des; subst; eauto.
        eapply local_wf_promise; eauto.
        clear - INV. ss. des; eauto.
      }
      {
        (* closed timemap sc src *)
        clear ATM_BIT. des; subst; eauto.
        eapply Memory.promise_closed_timemap; eauto.
      }
    }
  - (* memory lower *)
    lets PROMISE': PROMISE. inv PROMISE'. do 2 des1. subst msg1.
    exploit lower_succeed_wf; eauto. ii. do 3 des1. inv MSG_LE.
    clear MEM PROMISES TS GET TS0 MSG_WF RELEASED.
    exploit promise_lower_I_dce_prsv;
      [eapply PROMISE | | | eapply INV | eauto..].
    instantiate (2 := inj').
    eapply promises_relation_rely_stable; eauto.
    clear - ATM_BIT. des; subst; ss.
    clear - ATM_BIT. des; subst; ss.
    inv LOCAL_WF_TGT; eauto.
    inv LOCAL_WF_SRC; eauto.
    clear - INV. ss. des. inv INJ_MEM; eauto.
    clear - PROM_CONS. unfold Local.promise_consistent in *; ss.
    ii. exploit PROM_CONS; eauto. ii.
    eapply Memory.get_ts in H; eauto. des; subst; try solve [auto_solve_time_rel]. eauto.
 
    i. do 14 des1. des; ss. des1; subst.
    exists state_src tview_src prm_src' sc_src mem_src' inj'.
    splits; try solve [ss].
    {
      (* source step *)
      eapply Operators_Properties.clos_rt1n_step.
      econs. econs; eauto.
    }
    {
      (* match state *)
      econs; eauto; simpl.
      {
        (* match state tlocal *)
        inv MATCH_THRD_LOCAL. econs; eauto.
      }
      {
        (* Inv View dce *)
        eapply InvView_dce_rely_stable' with
            (inj := inj') (mem_src := mem_src); eauto.
        ss.
        clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; ss.
      }
      {
        (* Local wf tgt *)
        eapply local_wf_promise; eauto.
      }
      {
        (* closed timemap sc *)
        eapply Memory.promise_closed_timemap; eauto.
      }
      { 
        (* closed memory tgt *)
        eapply promise_step_closed_mem with (mem1 := mem_tgt); eauto.
        econs; eauto.
      }
      {
        (* Local wf src *)
        eapply local_wf_promise; eauto.
        clear - INV. ss. des; eauto.
      }
      {
        (* closed timemap sc src *)
        eapply Memory.promise_closed_timemap; eauto.
      }
    }
  - (* memory cancel *)
    des; ss.
Qed.

Lemma pf_promise_step_case
      inj lo b te
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_dce inj lo b
                              (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                              (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (TGT_STEP: Thread.step lo true te 
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt'))
      (PRM_STEP: (exists loc t, ThreadEvent.is_promising te = Some (loc, t)))
      (PROM_CONS: Local.promise_consistent (Local.mk tview_src prm_src)):
  exists state_src' tview_src' prm_src' sc_src' mem_src',
    rtc (@Thread.pf_promise_step rtl_lang) 
        (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
        (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
    match_state_dce inj lo b
                    (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                    (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src').
Proof.
  des. inv TGT_STEP.
  2: {  inv STEP. inv LOCAL; ss. }
  inv STEP; ss. inv LOCAL; ss. symmetry in LC2. inv LC2.
  inv PRM_STEP.
  destruct kind; ss.
  - (* lower to none *)
    destruct msg1; ss. destruct msg; ss. destruct released0; ss.
    inv MATCH.
    exploit promise_lower_I_dce_prsv;
      [eapply PROMISE | | | eapply INV | eauto..].
    instantiate (2 := inj).
    eapply promises_relation_rely_stable; eauto.
    clear - ATM_BIT. des; subst; ss.
    clear - ATM_BIT. des; subst; ss.
    inv LOCAL_WF_TGT; eauto.
    inv LOCAL_WF_SRC; eauto.
    clear - INV. ss. des. inv INJ_MEM; eauto.
    clear - PROM_CONS. unfold Local.promise_consistent in *; ss.
    ii. exploit PROM_CONS; eauto. ii.
    eapply Memory.get_ts in H; eauto. des; subst; try solve [auto_solve_time_rel]. eauto.
    
    i. do 13 des1.
    destruct R'; simpl in VIEW_INJ_REL; tryfalse.
    exists state_src tview_src prm_src' sc_src mem_src'.
    splits; try solve [ss].
    {
      (* source step *)
      eapply Operators_Properties.clos_rt1n_step.
      econs. econs; eauto.
      inv PRM_ADD'. do 2 des1. subst msg'.
      simpl. eauto.
    }
    {
      (* match state *)
      econs; eauto; simpl.
      {
        (* match state tlocal *)
        inv MATCH_THRD_LOCAL. econs; eauto.
      }
      {
        (* Inv View dce *)
        eapply InvView_dce_rely_stable' with
            (inj := inj') (mem_src := mem_src); eauto.
        ss.
        clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; ss.
      }
      {
        (* Local wf tgt *)
        eapply local_wf_promise; eauto.
      }
      {
        (* closed timemap sc *)
        eapply Memory.promise_closed_timemap; eauto.
      }
      { 
        (* closed memory tgt *)
        eapply promise_step_closed_mem with (mem1 := mem_tgt); eauto.
        econs; eauto.
      }
      {
        (* Local wf src *)
        eapply local_wf_promise; eauto.
        clear - INV. ss. des; eauto.
      }
      {
        (* closed timemap sc src *)
        eapply Memory.promise_closed_timemap; eauto.
      }
    }
  - (* cancel *)
    inv MATCH.
    exploit promise_cancel_I_dce_prsv;
      [eapply PROMISE | | | eapply INV | eauto..].
    instantiate (2 := inj).
    eapply promises_relation_rely_stable; eauto. ss.
    clear - ATM_BIT. des; subst; ss.
    inv LOCAL_WF_TGT; eauto.
    inv LOCAL_WF_SRC; eauto.
    clear - INV. ss. des. inv INJ_MEM; eauto.
    
    i. do 9 des1.
    exists state_src tview_src prm_src' sc_src mem_src'.
    splits; try solve [ss].
    {
      (* source step *)
      des1.
      eapply Operators_Properties.clos_rt1n_step.
      econs. econs; eauto.
      des1; subst. eauto.
    }
    {
      (* match state *)
      econs; eauto; simpl.
      {
        (* match state tlocal *)
        inv MATCH_THRD_LOCAL. econs; eauto.
      }
      {
        (* Inv View dce *)
        eapply InvView_dce_rely_stable' with
            (inj := inj') (mem_src := mem_src); eauto.
        ss.
        clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; ss.
      }
      {
        (* Local wf tgt *)
        eapply local_wf_promise; eauto.
      }
      {
        (* closed timemap sc *)
        eapply Memory.promise_closed_timemap; eauto.
      }
      { 
        (* closed memory tgt *)
        eapply promise_step_closed_mem with (mem1 := mem_tgt); eauto.
        econs; eauto.
      }
      {
        (* Local wf src *)
        des1.
        eapply local_wf_promise; eauto.
        clear - INV. ss. des; eauto.
        des1; subst; eauto.
      }
      {
        (* closed timemap sc src *)
        des1.
        eapply Memory.promise_closed_timemap; eauto.
        des1; subst. eauto.
      }
    }
Qed.

Lemma rely_step_case:
  forall inj inj' lo
    state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
    sc_tgt' mem_tgt'
    state_src tview_src prm_src sc_src mem_src
    sc_src' mem_src'
    (MATCH: match_state_dce inj lo true
                            (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                            (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
    (RELY: Rely inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)
                inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src')
                prm_tgt prm_src lo)
    (INV: I_dce lo inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src')),
    match_state_dce inj' lo true
                    (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt' mem_tgt')
                    (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src' mem_src').
Proof.
  ii. inv MATCH. inv RELY.
  destruct ATM_BIT; tryfalse. destruct H; tryfalse. des; subst.
  econs; eauto.
  {
    (* match state tlocal *)
    inv MATCH_THRD_LOCAL. econs; eauto.
    inv CUR_STK_FRAME. econs; eauto.
    clear - AI_INTERP INJ_INCR.
    unfold ai_interp in *. destruct ai; ss. des.
    split; eauto.
    unfold sem_live_loc in *. ii.
    exploit AI_INTERP0; eauto. ii; eauto.
    des. splits; eauto.
  }
  {
    (* Inv View *)
    eapply InvView_dce_rely_stable; eauto.
    clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; ss.
  }
  {
    (* cur acq *)
    eapply cur_acq_rely_stable; eauto.
  }
  {
    (* cur acq pln *)
    eapply cur_acq_pln_rely_stable; eauto.
  }
  {
    (* promise relation *)
    eapply promises_relation_rely_stable; eauto.
  }
  {
    (* Local wf tgt *) 
    inv ENV_STEPS.
    eapply concrete_incr_local_wf_prsv.
    2: { simpl; simpl in PRM_TGT_IN; eauto. }
    2: { eapply LOCAL_WF_TGT. }
    clear - MEM_TGT_INCR. ss.
    unfold concrete_mem_incr in MEM_TGT_INCR.
    ii. eapply MEM_TGT_INCR in H; des; eauto.
  }

  inv ENV_STEPS; eauto.
  inv ENV_STEPS; eauto.

  {
    (* Local wf src *) 
    inv ENV_STEPS.
    eapply concrete_incr_local_wf_prsv.
    2: { simpl; simpl in PRM_SRC_IN; eauto. }
    2: { eapply LOCAL_WF_SRC. }
    clear - MEM_SRC_INCR. ss.
    unfold concrete_mem_incr in MEM_SRC_INCR.
    ii. eapply MEM_SRC_INCR in H; des; eauto.
  }
  {
    inv ENV_STEPS. simpl in CLOSED_SC.
    simpl in CLOSED_MEM. clear - INV CLOSED_SC.
    simpl in INV. des.
    eapply inj_sc_fence_tm_closed; eauto.
  }
Qed.

Lemma done_step_case
      inj lo b
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_src tview_src prm_src sc_src mem_src
      (MATCH: match_state_dce inj lo b
                            (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                            (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (DONE: Thread.is_done (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)):
  exists inj',
      Thread.is_done (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src) /\
      incr_inj inj inj' /\
      I_dce lo inj' (Build_Rss sc_tgt mem_tgt sc_src mem_src).
Proof.
  inv MATCH. inv DONE. simpl in H, H0. inv H. inv H0.
  exploit promises_relation_bot; eauto.
  clear - INV LOCAL_WF_SRC. ss. des; eauto. ii. inv LOCAL_WF_SRC; ss.
  eapply PROMISES in H; eauto.
  introv PRM_SRC. subst.
  exists inj'. splits; eauto.
  - econs; eauto. ss. inv MATCH_THRD_LOCAL; ss. subst; ss.
    inv STK_FRAMES. inv CUR_STK_FRAME.
    destruct BB_src; ss; eauto.
    + (* jmp: contradiction *)
      inv AI_FOR_CBLK; ss.
    + (* call: contradiction *)
      destruct ai_tail; ss. inv AI_FOR_CBLK. ss.
    + (* be: contradiction *)
      destruct ai_tail; ss. inv AI_FOR_CBLK. ss.
    + (* instr: contradiction *)
      pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS.
      destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
      rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK. ss.
  - clear - ATM_BIT. des; subst; eauto. ss.
Qed.

Lemma transform_blk_load
      aib BB_src BB_tgt' r x o
      (TRANS_BB: transform_blk' aib BB_src = Inst.load r x o ## BB_tgt'):
  exists BB_src', BB_src = Inst.load r x o ## BB_src'.
Proof.
  destruct BB_src; ss; try solve [destruct aib; ss].
  destruct aib; try solve [destruct aib; ss].
  ss. inv TRANS_BB. eauto. ss.
  destruct c; ss.
  destruct l; ss. des_ifH TRANS_BB; ss.
  destruct or; ss; eauto.
  destruct l; ss. des_ifH TRANS_BB; ss.
  inv TRANS_BB; eauto.
  inv TRANS_BB; eauto.
  inv TRANS_BB; eauto.
  inv TRANS_BB; eauto.
  inv TRANS_BB; eauto.
  destruct ow; ss; tryfalse.
  destruct l; ss. des_ifH TRANS_BB; ss.
Qed. 

Lemma transform_blk_cas
      aib BB_src BB_tgt' r x or ow er ew
      (TRANS_BB: transform_blk' aib BB_src = Inst.cas r x er ew or ow ## BB_tgt'):
  exists BB_src', BB_src = Inst.cas r x er ew or ow ## BB_src'.
Proof.
  destruct BB_src; ss; try solve [destruct aib; ss].
  destruct aib; try solve [destruct aib; ss].
  ss. inv TRANS_BB. eauto. ss.
  destruct c; ss.
  destruct l; ss. des_ifH TRANS_BB; ss.
  destruct or0; ss; eauto.
  destruct l; ss. des_ifH TRANS_BB; ss.
  destruct ow0; ss; eauto.
  destruct l; ss. des_ifH TRANS_BB; ss.
  inv TRANS_BB; ss. eauto.
Qed.

Lemma transform_blk_store
      aib BB_src BB_tgt' x e ow 
      (TRANS_BB: transform_blk' aib BB_src = Inst.store x e ow ## BB_tgt'):
  exists BB_src', BB_src = Inst.store x e ow ## BB_src'.
Proof.
  destruct BB_src; ss; try solve [destruct aib; ss].
  destruct aib; try solve [destruct aib; ss].
  ss. inv TRANS_BB. eauto.
  ss.
  destruct c; ss.
  destruct l; ss. des_ifH TRANS_BB; ss.
  destruct or; ss; eauto.
  destruct l; ss. des_ifH TRANS_BB; ss.
  destruct ow0; ss; eauto.
  destruct l; ss. des_ifH TRANS_BB; ss.
  inv TRANS_BB; ss. eauto.
  inv TRANS_BB; ss. eauto.
  inv TRANS_BB; ss. eauto.
  inv TRANS_BB; ss. eauto.
  inv TRANS_BB; ss. eauto.
Qed.

Lemma abort_step_case
      inj lo b
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_src tview_src prm_src sc_src mem_src
      (MATCH: match_state_dce inj lo b
                              (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                              (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (ABORT: Thread.is_abort (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt) lo):
    Thread.is_abort (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src) lo.
Proof.
  inv ABORT. simpl in H. simpl in H0.
  des1. econs.
  - (* promise consistent *)
    simpl.
    eapply match_state_dce_implies_promise_consistent; eauto.
  - (* abort *)
    simpl. des1. destruct H0.
    + left. introv ABORT_SRC. contradiction H0. clear H0.
      des1.
      {
        do 2 des1.
        inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
        left.
        destruct BB_src.
        {
          (* jmp *)
          simpl in AI_FOR_CBLK. inv AI_FOR_CBLK.
          simpl. inv ABORT_SRC; tryfalse.
          symmetry in BLK. inv BLK. renames b' to BB_src'.
          exploit transform_cdhp_prop; eauto. instantiate (1 := afunc).
          introv BB_TGT. des1.
          do 2 eexists. eapply State.step_jmp; eauto.
        }
        {
          (* call *)
          simpl in AI_FOR_CBLK. destruct ai_tail. inv AI_FOR_CBLK.
          simpl. inv ABORT_SRC; tryfalse.
          symmetry in BLK. inv BLK. renames ch0 to C_src', b' to BB_src', b2 to BB_src1.
          exploit transform_cdhp_prop; eauto. instantiate (1 := afunc).
          introv BB_TGT'. destruct BB_TGT' as (BB_tgt' & BB_TGT').
          exploit transform_prog_proper; eauto.
          i. do 2 des1. destruct func_t as (C_tgt' & f1').
          unfold transform_func in x1.
          destruct (LvDS.analyze_func_backward (C_src', f1) succ transf_blk) eqn:Heqe; tryfalse.
          inv x1. renames a to afunc'.
          exploit transform_cdhp_prop; [eapply ENTRY_BLK | eauto..].
          instantiate (1 := afunc'). introv BB_TGT1.
          destruct BB_TGT1 as (BB_tgt1 & BB_TGT1).
          do 2 eexists.
          eapply State.step_call; eauto.
        }
        {
          (* be *)
          simpl in AI_FOR_CBLK. destruct ai_tail. inv AI_FOR_CBLK.
          simpl. inv ABORT_SRC; tryfalse. symmetry in BLK. inv BLK.
          assert (EXPR_EQ: RegFile.eval_expr e0 R_tgt = RegFile.eval_expr e0 R_src).
          {
            eapply sem_live_reg_regs_eq; eauto.
            unfold ai_interp in *. des1; eauto.
          }
          des1.
          {
            des1. exploit transform_cdhp_prop; eauto. instantiate (1 := afunc). i. des1.
            do 2 eexists.
            eapply State.step_be; eauto.
          }
          {
            des1. exploit transform_cdhp_prop; eauto. instantiate (1 := afunc). i. des1.
            do 2 eexists.
            eapply State.step_be; eauto.
          }
        }
        {
          (* ret *)
          simpl in AI_FOR_CBLK. inv AI_FOR_CBLK.
          simpl. inv ABORT_SRC; tryfalse. clear BLK.
          inv STK_FRAMES.
          do 2 eexists. eapply State.step_ret; eauto.
        }
        {
          (* instruction *)
          destruct c; 
          try simpl in AI_FOR_CBLK;
          try (pose proof (transf_blk_cons ai_tail BB_src) as CONS_ANALYSIS);
          try (destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS);
               rewrite CONS_ANALYSIS in AI_FOR_CBLK; simpl in AI_FOR_CBLK).

          (* skip *)
          inv AI_FOR_CBLK. simpl.
          do 2 eexists. eapply State.step_skip; eauto.

          (* assign *)
          unfold transf_instr in AI_FOR_CBLK. destruct ai'.
          destruct (is_dead_reg lhs n) eqn:IS_DEAD_REG. inv AI_FOR_CBLK.
          simpl. rewrite IS_DEAD_REG.
          do 2 eexists. eapply State.step_skip; eauto.
          inv AI_FOR_CBLK. simpl. rewrite IS_DEAD_REG.
          do 2 eexists. eapply State.step_assign; eauto.

          (* load *)
          unfold transf_instr in AI_FOR_CBLK. destruct ai'.  
          destruct (is_dead_reg lhs n) eqn:IS_DEAD_REG. inv AI_FOR_CBLK.
          simpl.
          destruct or; try solve [do 2 eexists; eapply State.step_load; eauto].
          rewrite IS_DEAD_REG. do 2 eexists. eapply State.step_skip; eauto.
          inv AI_FOR_CBLK. simpl.
          destruct or; try solve [do 2 eexists; eapply State.step_load; eauto].
          rewrite IS_DEAD_REG. do 2 eexists. eapply State.step_load; eauto.

          (* store *)
          unfold transf_instr in AI_FOR_CBLK. destruct ai'.  
          destruct (is_dead_loc lhs n0) eqn:IS_DEAD_LOC. inv AI_FOR_CBLK.
          simpl.
          destruct ow; try solve [do 2 eexists; eapply State.step_store; eauto].
          rewrite IS_DEAD_LOC. do 2 eexists. eapply State.step_skip; eauto.
          inv AI_FOR_CBLK. simpl.
          destruct ow; try solve [do 2 eexists; eapply State.step_store; eauto].
          rewrite IS_DEAD_LOC. do 2 eexists. eapply State.step_store; eauto.

          (* print *)
          unfold transf_instr in AI_FOR_CBLK. destruct ai'. inv AI_FOR_CBLK.
          simpl. do 2 eexists. eapply State.step_out; eauto.

          (* cas *)
          unfold transf_instr in AI_FOR_CBLK. destruct ai'. inv AI_FOR_CBLK.
          assert (EXPR_EQ: RegFile.eval_expr ew R_tgt = RegFile.eval_expr ew R_src
                           /\ RegFile.eval_expr er R_tgt = RegFile.eval_expr er R_src).
          {
            des_ifH AI_INTERP.
            split. eapply ai_interp_live_regs_eq; eauto.
            eapply ai_interp_set_expr_live in AI_INTERP.
            eapply ai_interp_live_regs_eq; eauto.
            split. eapply ai_interp_live_regs_eq; eauto.
            eapply ai_interp_set_expr_live in AI_INTERP.
            eapply ai_interp_live_regs_eq; eauto.
          }
          destruct EXPR_EQ as (EXPR_EQw & EXPR_EQr).
          inv ABORT_SRC; tryfalse. symmetry in BLK. inv BLK.
          simpl.
          do 2 eexists. eapply State.step_cas_same; eauto. 
          simpl. symmetry in BLK. inv BLK.
          do 2 eexists. eapply State.step_cas_flip; eauto.

          (* fence rel *)
          unfold transf_instr in AI_FOR_CBLK. destruct ai'. inv AI_FOR_CBLK.
          inv ABORT_SRC; tryfalse.
          simpl. do 2 eexists. eapply State.step_fence_rel; eauto.

          (* fence acq *)
          unfold transf_instr in AI_FOR_CBLK. destruct ai'. inv AI_FOR_CBLK.
          inv ABORT_SRC; tryfalse.
          simpl. do 2 eexists. eapply State.step_fence_acq; eauto.

          (* fence sc *)
          unfold transf_instr in AI_FOR_CBLK. destruct ai'. inv AI_FOR_CBLK.
          inv ABORT_SRC; tryfalse.
          simpl. do 2 eexists. eapply State.step_fence_sc; eauto.
        }
      }
      {
        right.
        inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
        inv ABORT_SRC; ss. subst.
        unfold transf_blk in AI_FOR_CBLK. inv AI_FOR_CBLK. simpl.
        econs; eauto. ss. inv STK_FRAMES; eauto.
      }
    + (* mode contradiction *)
      des1.
      {
        do 5 des1. des1. 

        (* mode contradiction: read *)
        inv H0; tryfalse. 

        inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
        exploit transform_blk_load; [eapply TRANS_PBLK | eauto..]. i. des1. subst.
        right. left. do 4 eexists. split. left.
        eapply State.step_load; eauto. eauto.

        inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
        renames rf to R_tgt.
        exploit transform_blk_cas; [eapply TRANS_PBLK | eauto..]. i. des1. subst.
        assert (EXPR_EQ: RegFile.eval_expr ew R_tgt = RegFile.eval_expr ew R_src
                         /\ RegFile.eval_expr er R_tgt = RegFile.eval_expr er R_src).
        {
          clear - AI_INTERP AI_FOR_CBLK. ss.
          pose proof (transf_blk_cons ai_tail BB_src') as CONS_ANALYSIS.
          destruct CONS_ANALYSIS as (ai' & ai_b' & CONS_ANALYSIS).
          rewrite CONS_ANALYSIS in AI_FOR_CBLK. inv AI_FOR_CBLK.
          unfold transf_instr in *. destruct ai'.
          des_ifH AI_INTERP.
          split. eapply ai_interp_live_regs_eq; eauto.
          eapply ai_interp_set_expr_live in AI_INTERP.
          eapply ai_interp_live_regs_eq; eauto.
          split. eapply ai_interp_live_regs_eq; eauto.
          eapply ai_interp_set_expr_live in AI_INTERP.
          eapply ai_interp_live_regs_eq; eauto.
        }
        destruct EXPR_EQ as (EXPR_EQw & EXPR_EQr). 
        right. left. do 4 eexists. split. left.
        eapply State.step_cas_flip; eauto.
        rewrite <- EXPR_EQr; eauto.
        eauto.

        (* mode contradiction: write *)
        inv H0; tryfalse.
        inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
        exploit transform_blk_store; [eapply TRANS_PBLK | eauto..]. i. des1. subst.
        right. left. do 4 eexists. split. right.
        eapply State.step_store; eauto.
        eauto.
      }
      {
        do 7 des1.
        inv H0.
        inv MATCH. inv MATCH_THRD_LOCAL. inv CUR_STK_FRAME.
        exploit transform_blk_cas; [eapply TRANS_PBLK | eauto..]. i. des1. subst.
        right. right.
        do 6 eexists. split. 
        eapply State.step_cas_same; eauto.
        eauto.
      }
      Unshelve.
      exact Int.zero. exact Int.zero. exact Int.zero.
      exact Int.zero. exact Int.zero. exact Int.zero.
      exact Int.zero. exact Int.zero. exact Int.zero. exact Int.zero.
Qed.
