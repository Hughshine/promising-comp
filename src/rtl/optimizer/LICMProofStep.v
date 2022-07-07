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
Require Import LICMProofMState.
Require Import Lib_Memory.
Require Import Lib_Step.
Require Import Lib_Ordering.

Lemma atomic_or_out_step_case
      inj lo b te pf
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_linv inj lo b
                               (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                               (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (TGT_STEP: Thread.step lo pf te 
                             (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                             (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt'))
      (AT_OR_OUT: ThreadEvent.is_at_or_out_step te):
  exists state_src' tview_src' prm_src' sc_src' mem_src' inj' te',
    Thread.program_step te' lo 
                        (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
                        (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
    incr_inj inj inj' /\ 
    match_state_linv inj' lo true
                     (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                     (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
    thrdevt_eq te te'.
Proof.
  inv MATCH. inv TGT_STEP. inv STEP; ss. inv STEP.
  inv MATCH_THRD_LOCAL. inv MATCH_CUR.
  {
    (* execution not preheader *)
    destruct BB_s.
    - (* jmp *)
      des1. subst. inv STATE; ss; destruct te; ss.
      inv BLK_REL; inv STATE; ss; destruct te; ss.
    - (* call *)
      des1. subst. inv STATE; ss; destruct te; ss.
      inv BLK_REL; inv STATE; ss; destruct te; ss.
    - (* be *)
      des1. subst. inv STATE; ss; destruct te; ss.
      inv BLK_REL; inv STATE; ss; destruct te; ss.
    - (* ret *)
      des1. subst. inv STATE; ss; destruct te; ss.
      inv BLK_REL; inv STATE; ss; destruct te; ss.
    - (* instr *)
      eapply BBlock_cons in BLK_REL. do 2 des1. subst. renames BB_s to BB_s'.
      destruct c; ss;
        try solve [inv STATE; ss; destruct te; ss].
      + (* load *)
        inv STATE; tryfalse. symmetry in BLK. inv BLK.
        destruct te; simpl in H0; ss. inv H0. do 2 des1.
        pose proof (nonatomic_or_atomic ord). des1; subst; tryfalse. clear AT_OR_OUT.
        inv LOCAL.
        exploit Local_read_tview_le_prsv; eauto.
        {
          simpl. eapply mem_id_le_identity; eauto.
        }
        {
          simpl. eauto.
        }

        i. do 5 des1. simpl in PROM_LE', TVIEW_LE'.
        destruct lc2'. renames tview to tview_src', promises to prm_src'.
        do 5 eexists. exists (spec_inj mem_tgt') (ThreadEvent.read loc0 ts val released' ord).
        splits; eauto.
        {
          econs. ss. econs; eauto.
          econs; eauto.
        }
        {
          clear - ATM_BIT. des; subst; eauto.
          ii; eauto.
        }
        {
          ss. inv LOCAL0. ss. inv LC2. inv LE_READ. ss. inv LC2.
          econs; eauto.
          unfold I_linv. splits; eauto.
          econs; eauto. eapply EXEC_NOT_PH; eauto.
          introv REG_IN. eapply ORIGN_REGS in REG_IN.
          destruct (Reg.eq_dec r lhs); subst; eauto.
          do 2 (rewrite RegFun.add_spec_eq). eauto.
          do 2 (rewrite RegFun.add_spec_neq; eauto).
          clear - SUBSET_REG. ii. eapply SUBSET_REG; eauto. eapply RegSet.union_spec; eauto.
          introv GET_PRM. eapply PRM_INDOM in GET_PRM. des1.
          clear - GET_PRM ATM_BIT. des; subst; eauto.
          eapply local_wf_read; eauto. econs; eauto.
          eapply local_wf_read; eauto. econs; eauto.
        }
      + (* store *)
        inv STATE; tryfalse. symmetry in BLK. inv BLK.
        destruct te; simpl in H0; ss. inv H0. do 2 des1.
        pose proof (nonatomic_or_atomic ord). des1; subst; tryfalse. clear AT_OR_OUT.
        inv LOCAL.
        lets LOCAL_SRC: LOCAL0. 
        eapply Local_write_tview_le_prsv with
            (lc1' := Local.mk tview_src prm_tgt) (sc1' := sc_src) in LOCAL_SRC; eauto.
        simpl in LOCAL_SRC. do 7 des1.
        destruct lc2'; ss. subst. renames tview to tview_src'. 
        do 5 eexists.
        exists (spec_inj mem_tgt') (ThreadEvent.write loc from to (RegFile.eval_expr rhs R_t) released' ord).
        splits; eauto.
        {
          econs; eauto. simpl.
          econs; eauto.
          eapply expr_eval_eq; eauto.
          clear - SUBSET_REG ORIGN_REGS. ii.
          symmetry. eapply ORIGN_REGS; eauto.
          eapply SUBSET_REG; eauto. eapply RegSet.union_spec; eauto.
        }    
        {
          clear - ATM_BIT LOCAL0. des; subst; ss; eauto.
          {
            ii. eapply ATM_BIT0 in H. unfold spec_inj in *.
            destruct (Memory.get loc0 t mem_tgt) eqn:MEM_GET; ss; eauto.
            destruct p. destruct t1; ss. inv H.
            exploit write_step_concrete_msg_prsv; eauto.
            i. do 2 des1. rewrite H. eauto.
          }
          {
            ii. unfold spec_inj in *.
            destruct (Memory.get loc0 t mem_tgt) eqn:GET_MEM; ss.
            destruct p. destruct t1; ss. inv H.
            exploit write_step_concrete_msg_prsv; eauto.
            i. do 2 des1. rewrite H. eauto.
          }
        }
        { 
          econs; eauto.
          {
            unfold I_linv; ss. splits; eauto. inv LOCAL0. ss.
          } 
          {
            econs; eauto. eapply EXEC_NOT_PH; eauto.
            ii. eapply SUBSET_REG; eauto. eapply RegSet.union_spec; eauto.
          }
          {
            introv PRM_GET. eapply local_wf_write in LOCAL0; eauto.
            clear - LOCAL0 PRM_GET. inv LOCAL0; ss.
            exploit PROMISES; eauto. i.
            unfold spec_inj. rewrite H; ss; eauto.
          }
          {
            eapply local_wf_write; eauto.
          }
          {
            inv LOCAL0. simpl in LC2. inv LC2.
            inv WRITE. inv PROMISE; ss.
            eapply Memory.add_closed_timemap; eauto.
            eapply Memory.split_closed_timemap; eauto.
            eapply Memory.lower_closed_timemap; eauto.
          }
          {
            eapply write_step_closed_mem; eauto.
          }
          {
            eapply local_wf_write; eauto.
          }
          {
            inv LE_WRITE. simpl in LC2. inv LC2.
            inv WRITE. inv PROMISE; ss.
            eapply Memory.add_closed_timemap; eauto.
            eapply Memory.split_closed_timemap; eauto.
            eapply Memory.lower_closed_timemap; eauto.
          }
          {
            eapply write_step_closed_mem; eauto.
          }
        }
      + (* print(e) *)
        inv STATE; tryfalse. symmetry in BLK. inv BLK.
        destruct te; simpl in H0; ss. inv H0. do 2 des1.
        inv LOCAL.
        exploit Local_sc_fence_tview_le_prsv; eauto; simpl.
        {
          inv LOCAL_WF_TGT; ss; eauto.
        }
        {
          instantiate (1 := Local.mk tview_src prm_tgt). s. eauto.
        }
        {
          s. eapply mem_id_le_identity; eauto.
        }

        i. do 4 des1.
        destruct lc2'. simpl in TVIEW_LE'. 
        do 5 eexists. exists (spec_inj mem_tgt') (ThreadEvent.syscall {| Event.output := (RegFile.eval_expr e R_s) |}).
        splits; s.
        {
          econs; eauto. s.
          eapply State.step_out; eauto.
        }
        {
          clear - ATM_BIT. des; subst; eauto.
          ii; eauto.
        }
        {
          econs; eauto.
          {
            unfold I_linv. splits; eauto.
          }
          {
            econs; eauto. econs; eauto.
            ii. eapply SUBSET_REG; eauto. eapply RegSet.union_spec; eauto.
          }
          {
            inv FENCE_LE; ss; eauto. inv LC2.
            inv LOCAL0; ss. inv LC2. eauto.
          }
          {
            ii. inv LOCAL0; ss. inv LC2.
            exploit PRM_INDOM; eauto. i. des1.
            clear - ATM_BIT H0. des; subst; eauto.
          }
          {
            inv LOCAL0; ss. inv LC2.
            eapply local_wf_fence; eauto.
          }
          {
            inv LOCAL0; ss. inv LC2; ss.
            exploit TViewFacts.read_fence_future.
            inv LOCAL_WF_TGT. eauto. simpl. inv LOCAL_WF_TGT; eauto.
            simpl. i. des1.
            exploit TViewFacts.write_fence_future; [ | | eapply CLOSED_TVIEW | eauto..]; eauto.
            i. do 2 des1. eauto.
          }
          {
            inv FENCE_LE; ss. inv LC2; ss.
            eapply local_wf_fence; eauto.
          }
          {
            inv FENCE_LE; ss. inv LC2; ss.
            exploit TViewFacts.read_fence_future.
            inv LOCAL_WF_SRC. eauto. simpl. inv LOCAL_WF_SRC; eauto.
            simpl. i. des1.
            exploit TViewFacts.write_fence_future; [ | | eapply CLOSED_TVIEW | eauto..]; eauto.
            i. do 2 des1. eauto.
          }
        }
        {
          assert (EXPR_EVAL_EQ: RegFile.eval_expr e R_t = RegFile.eval_expr e R_s).
          {
            eapply expr_eval_eq; eauto.
            i. eapply ORIGN_REGS; eauto. eapply SUBSET_REG.
            eapply RegSet.union_spec; eauto.
          }
          rewrite EXPR_EVAL_EQ. eauto.
        }
      + (* cas *) 
        inv STATE; tryfalse; try (symmetry in BLK; inv BLK).
        {
          destruct te; simpl in H0; ss. inv H0. do 2 des1. subst.
          inv LOCAL.
          assert (EXPR_R_EQ: RegFile.eval_expr er R_t = RegFile.eval_expr er R_s).
          {
            eapply expr_eval_eq; eauto.
            ii. eapply ORIGN_REGS; eauto. eapply SUBSET_REG; eauto.
            eapply RegSet.union_spec; eauto.
            left. eapply RegSet.add_spec; eauto. right.
            eapply RegSet.union_spec; eauto.
          }
          assert (EXPR_W_EQ: RegFile.eval_expr ew R_t = RegFile.eval_expr ew R_s).
          {
            eapply expr_eval_eq; eauto.
            ii. eapply ORIGN_REGS; eauto. eapply SUBSET_REG; eauto.
            eapply RegSet.union_spec; eauto.
            left. eapply RegSet.add_spec; eauto. right.
            eapply RegSet.union_spec; eauto.
          }
          
          exploit Local_read_tview_le_prsv; eauto.
          {
            s. eapply mem_id_le_identity; eauto.
          }
          {
            s. eauto.
          }
          i. do 5 des1. 
          exploit Local_write_tview_le_prsv;
            [eapply LOCAL2 | eapply MEM_LE | | eapply TVIEW_LE' | eauto..].
          {
            clear - LOCAL1 LE_READ. inv LOCAL1; ss. inv LE_READ; ss.
          }
          {
            inv LOCAL1; ss. 
            eapply closed_mem_implies_wf_msg_view in GET; eauto.
          }
          {
            inv LE_READ; ss. 
            eapply closed_mem_implies_wf_msg_view in GET; eauto.
          }
          {
            eapply local_wf_read; eauto.
          }
          {
            eapply local_wf_read; eauto.
          }

          instantiate (1 := sc_src). s. i. do 7 des1.
          destruct lc2'0; ss. subst.
          do 5 eexists. exists (spec_inj mem_tgt').          
          exists (ThreadEvent.update loc0 tsr tsw (RegFile.eval_expr er R_s) (RegFile.eval_expr ew R_s)
                                released' released'0 ordr ordw).
          splits; eauto.
          {
            econs; eauto. s.
            eapply State.step_cas_same; eauto.
            econs; eauto.
            rewrite EXPR_R_EQ in LE_READ; eauto.
            rewrite EXPR_W_EQ in LE_WRITE; eauto.
          }
          {
            clear - ATM_BIT LOCAL2. des; subst; ss; eauto.
            {
              ii. eapply ATM_BIT0 in H. unfold spec_inj in *.
              destruct (Memory.get loc t mem_tgt) eqn:MEM_GET; ss; eauto.
              destruct p. destruct t1; ss. inv H.
              exploit write_step_concrete_msg_prsv; eauto.
              i. do 2 des1. rewrite H. eauto.
            }
            {
              ii. unfold spec_inj in *.
              destruct (Memory.get loc t mem_tgt) eqn:GET_MEM; ss.
              destruct p. destruct t1; ss. inv H.
              exploit write_step_concrete_msg_prsv; eauto.
              i. do 2 des1. rewrite H. eauto.
            }
          }
          {
            econs; eauto.
            {
              unfold I_linv. splits; eauto. inv LOCAL2; ss.
            }
            {
              econs; eauto. eapply EXEC_NOT_PH; eauto.
              i. destruct (Reg.eq_dec r lhs); subst.
              do 2 (rewrite RegFun.add_spec_eq; eauto).
              do 2 (rewrite RegFun.add_spec_neq; eauto).
              i. eapply SUBSET_REG; eauto.
              eapply RegSet.union_spec; eauto.
            }
            { 
              i. exploit local_wf_read; [eapply LOCAL1 | eauto..]. 
              i. exploit local_wf_write; [eapply LOCAL2 | eauto..].
              i. inv H1; ss. eapply PROMISES in H. unfold spec_inj.
              rewrite H; ss. eauto.
            }
            {
              eapply local_wf_write; eauto.
              eapply local_wf_read; eauto.
            }
            {
              inv LOCAL2. inv LC2. ss.
              inv WRITE. inv PROMISE; ss.
              eapply Memory.add_closed_timemap; eauto.
              eapply Memory.split_closed_timemap; eauto.
              eapply Memory.lower_closed_timemap; eauto.
            }
            {
              eapply write_step_closed_mem with (mem1 := mem_tgt) (releasedr := releasedr); eauto.
              inv LOCAL1; ss. eapply closed_mem_implies_closed_msg; eauto.
              eapply local_wf_read; eauto.
            }
            {
              eapply local_wf_write; eauto.
              eapply local_wf_read; eauto.
            }
            {
              inv LE_WRITE. inv LC2.
              inv WRITE. inv PROMISE; ss.
              eapply Memory.add_closed_timemap; eauto.
              eapply Memory.split_closed_timemap; eauto.
              eapply Memory.lower_closed_timemap; eauto.
            }
            {
              eapply write_step_closed_mem with (mem1 := mem_src) (releasedr := released'); eauto.
              inv LE_READ; ss. eapply closed_mem_implies_closed_msg; eauto.
              eapply local_wf_read; eauto.
            }
          }
        }
        {
          destruct te; simpl in H0; ss. inv H0. do 2 des1. subst.
          inv LOCAL.
          assert (EXPR_R_EQ: RegFile.eval_expr er R_t = RegFile.eval_expr er R_s).
          {
            eapply expr_eval_eq; eauto.
            ii. eapply ORIGN_REGS; eauto. eapply SUBSET_REG; eauto.
            eapply RegSet.union_spec; eauto.
            left. eapply RegSet.add_spec; eauto. right.
            eapply RegSet.union_spec; eauto.
          }

          exploit Local_read_tview_le_prsv; eauto.
          {
            s. eapply mem_id_le_identity; eauto.
          }
          {
            s. eauto.
          }
          i. do 5 des1; ss. destruct lc2'.
          do 5 eexists. exists (spec_inj mem_tgt'). 
          exists (ThreadEvent.read loc0 ts val released' ord).
          splits; eauto.
          {
            econs; eauto. s.
            eapply State.step_cas_flip; eauto.
            rewrite <- EXPR_R_EQ. eauto.
          }
          {
            ss. clear - ATM_BIT. des; subst; eauto. ii; eauto.
          }
          {
            econs; eauto.
            {
              unfold I_linv. splits; eauto.
            }
            {
              econs; eauto. econs; eauto. i.
              destruct (Reg.eq_dec r lhs); subst; eauto.
              do 2 (rewrite RegFun.add_spec_eq; eauto).
              do 2 (rewrite RegFun.add_spec_neq; eauto).
              i. eapply SUBSET_REG; eauto. eapply RegSet.union_spec; eauto.
            }
            {
              ss. inv LOCAL0; ss. inv LC2; ss.
              inv LE_READ; ss. inv LC2; ss.
            }
            {
              ii. inv LOCAL0; ss. inv LC2; ss.
              inv LE_READ; ss. inv LC2; ss.
              inv LOCAL_WF_TGT; ss. eapply PROMISES in H.
              unfold spec_inj. rewrite H. eauto.
            }
            {
              eapply local_wf_read; eauto.
            }
            {
              eapply local_wf_read; eauto.
            }
          }
        }
      + (* fence rel *)
        inv STATE; tryfalse. symmetry in BLK. inv BLK.
        destruct te; simpl in H0; ss. inv H0. do 2 des1.
        inv LOCAL.
        exploit Local_fence_tview_le_prsv; [eapply LOCAL0 | eauto..]; s.
        {
          ii. tryfalse.
        }
        {
          inv LOCAL_WF_TGT; ss; eauto.
        }
        {
          instantiate (1 := Local.mk tview_src prm_tgt). s. eauto.
        }
        {
          s. eapply mem_id_le_identity; eauto.
        }

        instantiate (1 := sc_src).
        i. do 2 des1. destruct lc2'. renames tview to tview_src', promises to prm_src'; ss.
        assert (PRM_EQ: prm_tgt = prm_src').
        {
          clear - FENCE_LE. inv FENCE_LE; ss. inv LC2; eauto.
        }
        subst prm_src'.
        do 5 eexists. exists (spec_inj mem_tgt') (ThreadEvent.fence Ordering.relaxed Ordering.acqrel).
        splits; eauto.
        {
          econs; eauto. s.
          eapply State.step_fence_rel; eauto.
        }
        {
          clear - ATM_BIT. des; subst; eauto. ii; eauto.
        }
        {
          assert (PRM_EQ: prm_tgt = prm_tgt').
          {
            clear - LOCAL0. inv LOCAL0; ss; eauto. inv LC2; eauto.
          }
          subst prm_tgt.
          econs; eauto.
          {
            (* Inv *)
            unfold I_linv. splits; eauto.
            inv LOCAL0; ss.
          }
          {
            (* match tlocal *)
            econs; eauto. econs; eauto.
          }
          {
            (* prm indom *)
            clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; ss. ii.
            eapply PROMISES in H. unfold spec_inj. rewrite H; eauto.
          }
          {
            (* local wf tgt *)
            eapply Local_wf_fence_not_sc; eauto. ii; ss.
          }
          {
            (* closed timemap *) 
            exploit Local.fence_step_future; [eapply LOCAL0 | eauto..]. s. i. do 3 des1. eauto.
          }
          {
            (* local wf src *)
            exploit Local.fence_step_future; [eapply FENCE_LE | eauto..]. s. i. do 3 des1. eauto.
          }
        }
      + (* fence acq *)
        inv STATE; tryfalse. symmetry in BLK. inv BLK.
        destruct te; simpl in H0; ss. inv H0. do 2 des1.
        inv LOCAL.
        exploit Local_fence_tview_le_prsv; [eapply LOCAL0 | eauto..]; s.
        {
          ii. tryfalse.
        }
        {
          inv LOCAL_WF_TGT; ss; eauto.
        }
        {
          instantiate (1 := Local.mk tview_src prm_tgt). s. eauto.
        }
        {
          s. eapply mem_id_le_identity; eauto.
        }

        instantiate (1 := sc_src).
        i. do 2 des1. destruct lc2'. renames tview to tview_src', promises to prm_src'; ss.
        assert (PRM_EQ: prm_tgt = prm_src').
        {
          clear - FENCE_LE. inv FENCE_LE; ss. inv LC2; eauto.
        }
        subst prm_src'.
        do 5 eexists. exists (spec_inj mem_tgt') (ThreadEvent.fence Ordering.acqrel Ordering.relaxed).
        splits; eauto.
        {
          econs; eauto. s. eapply State.step_fence_acq; eauto.
        }
        {
          clear - ATM_BIT. des; subst; eauto. ii; des; eauto.
        }
        {
          assert (PRM_EQ: prm_tgt = prm_tgt').
          {
            clear - LOCAL0. inv LOCAL0; ss; eauto. inv LC2; eauto.
          }
          subst prm_tgt.
          econs; eauto.
          {
            (* Inv *)
            unfold I_linv. splits; eauto.
            inv LOCAL0; ss.
          }
          {
            (* match tlocal *)
            econs; eauto. econs; eauto.
          }
          {
            (* prm indom *)
            clear - LOCAL_WF_TGT. inv LOCAL_WF_TGT; ss. ii.
            eapply PROMISES in H. unfold spec_inj. rewrite H; eauto.
          }
          {
            (* local wf tgt *)
            eapply Local_wf_fence_not_sc; eauto. ii; ss.
          }
          {
            (* closed timemap *) 
            exploit Local.fence_step_future; [eapply LOCAL0 | eauto..]. s. i. do 3 des1. eauto.
          }
          {
            (* local wf src *)
            exploit Local.fence_step_future; [eapply FENCE_LE | eauto..]. s. i. do 3 des1. eauto.
          }
        }
      + (* fence sc *)
        inv STATE; tryfalse. symmetry in BLK. inv BLK.
        destruct te; simpl in H0; ss. inv H0. do 2 des1.
        inv LOCAL.
        exploit Local_sc_fence_tview_le_prsv; eauto; simpl.
        {
          inv LOCAL_WF_TGT; ss; eauto.
        }
        {
          instantiate (1 := Local.mk tview_src prm_tgt). s. eauto.
        }
        {
          s. eapply mem_id_le_identity; eauto.
        }

        i. do 4 des1.
        destruct lc2'. simpl in TVIEW_LE'.
        do 5 eexists. exists (spec_inj mem_tgt') (ThreadEvent.fence Ordering.relaxed Ordering.seqcst).
        splits; s; eauto.
        {
          econs; eauto. s. 
          eapply State.step_fence_sc; eauto.
        }
        {
          clear - ATM_BIT. des; subst; eauto.
          ii; eauto.
        }
        {
          econs; eauto.
          {
            unfold I_linv. splits; eauto.
          }
          {
            econs; eauto. econs; eauto.
          }
          {
            inv FENCE_LE; ss; eauto. inv LC2.
            inv LOCAL0; ss. inv LC2. eauto.
          }
          {
            ii. inv LOCAL0; ss. inv LC2.
            exploit PRM_INDOM; eauto. i. des1.
            clear - ATM_BIT H0. des; subst; eauto.
          }
          {
            inv LOCAL0; ss. inv LC2.
            eapply local_wf_fence; eauto.
          }
          {
            inv LOCAL0; ss. inv LC2; ss.
            exploit TViewFacts.read_fence_future.
            inv LOCAL_WF_TGT. eauto. simpl. inv LOCAL_WF_TGT; eauto.
            simpl. i. des1.
            exploit TViewFacts.write_fence_future; [ | | eapply CLOSED_TVIEW | eauto..]; eauto.
            i. do 2 des1. eauto.
          }
          {
            inv FENCE_LE; ss. inv LC2; ss.
            eapply local_wf_fence; eauto.
          }
          {
            inv FENCE_LE; ss. inv LC2; ss.
            exploit TViewFacts.read_fence_future.
            inv LOCAL_WF_SRC. eauto. simpl. inv LOCAL_WF_SRC; eauto.
            simpl. i. des1.
            exploit TViewFacts.write_fence_future; [ | | eapply CLOSED_TVIEW | eauto..]; eauto.
            i. do 2 des1. eauto.
          }
        }
  }
  {
    (* execution preheader *)
    destruct BB_t.
    - (* jmp *)
      des1. subst. inv STATE; ss; destruct te; ss.
      inv BLK_REL; inv STATE; ss; destruct te; ss.
    - (* call *)
      des1. subst. inv STATE; ss; destruct te; ss.
      inv BLK_REL; inv STATE; ss; destruct te; ss.
    - (* be *)
      des1. subst. inv STATE; ss; destruct te; ss.
      inv BLK_REL; inv STATE; ss; destruct te; ss.
    - (* ret *)
      des1. subst. inv STATE; ss; destruct te; ss.
      inv BLK_REL; inv STATE; ss; destruct te; ss.
    - (* instr *)
      destruct c; ss;
        try solve [inv STATE; ss; destruct te; ss].
      destruct or; ss. do 2 des1.
      inv STATE; ss. inv BLK. destruct te; ss. inv H0. ss.
  }
Qed.
  
Lemma silent_step_case
      inj lo b
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_linv inj lo b
                               (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                               (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (TGT_STEP: Thread.program_step ThreadEvent.silent lo
                                     (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                                     (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt'))
      (PROM_CONS: Local.promise_consistent (Local.mk tview_src prm_src)):
  (exists state_src' tview_src' prm_src' sc_src' mem_src',
      rtc (Thread.na_step lo) 
          (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
          (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
      match_state_linv inj lo false
                       (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                       (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src')) \/
  Thread.is_abort (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src) lo.
Proof.
  inv MATCH. inv TGT_STEP. inv LOCAL.
  inv MATCH_THRD_LOCAL. inv MATCH_CUR.
  {
    (* execution not preheader *)
    destruct BB_s.
    - (* jmp f *)
      des1; subst; ss.
      {
        destruct (cdhp_s ! f0) eqn:CDHP_S0; ss.

        (* the next block exists *)
        renames t to BB_s.
        left. inv STATE; ss. inv BLK. renames b' to BB_t.
        lets LOOP_INVS': LOOP_INVS.
        unfold det_loop_invs in LOOP_INVS. rewrite PTree.gmap in LOOP_INVS.
        unfold option_map in LOOP_INVS.
        unfold Func in *. rewrite CDHP_S in LOOP_INVS.
        exploit transC'_prop; eauto.
        {
          instantiate (1 := ep). instantiate (1 := lo). 
          destruct (cdhp_s ! ep) eqn:CDHP_S'; ss; eauto. 
          right. exists t. split; eauto. inv LOOP_INVS; eauto.
          inv LOOP_INVS. eauto.
        }
        
        introv CONT_BB.
        do 5 eexists. splits.
        {
          eapply Operators_Properties.clos_rt1n_step; eauto.
          eapply Thread.na_tau_step_intro; eauto. econs; eauto.
          s. eapply State.step_jmp; eauto.
        }
        {
          econs; eauto. econs; eauto. econs; eauto.
          ii. eapply reg_in_blk_in_cdhp; eauto.
          clear - ATM_BIT. des; subst; eauto.
        }

        (* the block does not exist *)
        right. unfold Thread.is_abort; s. split; eauto.
        left. ii. destruct H. do 2 des1. inv H; ss. inv BLK. rewrite CDHP_S0 in TGT. tryfalse.
        inv H; ss.
      }
      {
        inv BLK_REL. 
        destruct (cdhp_s ! f0) eqn:CDHP_S0; ss.

        (* the next block exists *)
        renames t to BB_s. left.
        inv STATE; ss. symmetry in BLK. inv BLK. renames b' to BB_t'.
        lets LOOP_INVS': LOOP_INVS.
        unfold det_loop_invs in LOOP_INVS'. rewrite PTree.gmap in LOOP_INVS'.
        unfold option_map in LOOP_INVS'.
        unfold Func in LOOP_INVS'. rewrite CDHP_S in LOOP_INVS'.
        destruct (cdhp_s ! ep) eqn: CDHP_S_EP; ss.
        
        lets TRANSC': TRANSC. 
        eapply well_defined_preheader with (lo := lo) in TRANSC; eauto.
        do 3 des1. rewrite TRANSC in CDHP_S0. inv CDHP_S0.
        do 5 eexists.
        splits.
        {
          eapply Operators_Properties.clos_rt1n_step; eauto.
          eapply Thread.na_tau_step_intro; eauto. econs; eauto.
          s. eapply State.step_jmp; eauto.
        }
        {
          econs; eauto. econs; eauto. eapply EXEC_PH; eauto.
          clear - ATM_BIT. des; subst; eauto.
        }
        {
          instantiate (1 := ep). unfold loop_invC.
          inv LOOP_INVS'. eauto.
        }
 
        inv LOOP_INVS'. ss. inv TRANSC.
        rewrite PTree.gempty in PT. ss.

        (* the next block does not exist *)
        right. unfold Thread.is_abort; s. split; eauto.
        left. ii. destruct H.
        do 2 des1. inv H; ss. inv BLK. rewrite CDHP_S0 in TGT. ss.
        inv H; ss.
      }
    - (* call *)
      des1.
      2: {  inv BLK_REL. } 
      subst. ss. inv STATE; ss. symmetry in BLK. inv BLK.

      destruct (cdhp_s ! fret) eqn:CDHP_S_RET.

      (* cont exists *)
      renames ch0 to cdhp_t0, b2 to BB_t2, b' to BB_t', t to BB_s'.
      exploit transC'_prop; [eapply TRANSC | eapply STACK | eapply CDHP_S_RET | eauto..].
      {
        instantiate (1 := ep). instantiate (1 := lo).
        unfold det_loop_invs in LOOP_INVS.
        rewrite PTree.gmap in LOOP_INVS. unfold option_map in LOOP_INVS.
        unfold Func in LOOP_INVS. rewrite CDHP_S in LOOP_INVS.
        destruct (cdhp_s ! ep) eqn:Heqe; ss; eauto. inv LOOP_INVS; eauto.
        inv LOOP_INVS; eauto.
      }
      introv RET_BLK_REL.
      lets OPT': OPT. 
      assert (FIND_FUNC_S: exists cdhp_s0 f2' loopinvs',
                 prog_s ! f0 = Some (cdhp_s0, f2') /\
                 TransC (cdhp_s0, f2') loopinvs' = (cdhp_t0, f2) /\
                 ((cdhp_s0 ! f2' = None /\ loopinvs' = nil) \/
                  (exists BB_s0, cdhp_s0 ! f2' = Some BB_s0 /\ loop_invC lo (cdhp_s0, f2') = loopinvs'))).
      {
        clear - OPT FIND_FUNC. unfold LInv in OPT. inv OPT.
        rewrite PTree.gmap in FIND_FUNC. unfold option_map in FIND_FUNC.
        destruct (prog_s ! f0) eqn: CDHP_S'. inv FIND_FUNC; eauto.
        unfold det_loop_invs in *. 
        try rewrite PTree.gmap in *. unfold option_map in *. try rewrite CDHP_S' in *.
        destruct f. destruct (c ! f) eqn:Heqe; eauto.
        do 3 eexists. splits; eauto.
        do 3 eexists. splits; eauto.
        tryfalse.
      }
      do 5 des1.
      exploit transC_prop; eauto.
      i. do 7 des1. left.
      destruct BLK_REL as [BLK_REL | BLK_REL].
      {
        do 5 eexists. splits.
        {
          eapply Operators_Properties.clos_rt1n_step.
          eapply Thread.na_tau_step_intro; eauto.
          econs; eauto. s. eapply State.step_call; eauto.
        }
        {
          econs; eauto. econs; eauto. 
          des1. econs; eauto.
          unfold det_loop_invs. rewrite PTree.gmap.
          unfold option_map. rewrite FIND_FUNC_S. rewrite GET_BB_S. eauto.
          ii. eapply reg_in_blk_in_cdhp; eauto.

          econs; eauto.
          econs; eauto. ii. eapply reg_in_blk_in_cdhp; eauto.

          clear - ATM_BIT. des; subst; eauto.
        }
      }
      {
        des1.
        do 5 eexists. splits.
        {
          eapply Operators_Properties.clos_rt1n_step.
          eapply Thread.na_tau_step_intro; eauto.
          econs; eauto. s. eapply State.step_call; eauto.
        }
        {
          econs; eauto. econs; eauto. eapply EXEC_PH; eauto.
          unfold det_loop_invs. rewrite PTree.gmap.
          unfold option_map. rewrite FIND_FUNC_S. rewrite GET_BB_S. eauto.
          econs; eauto.
          econs; eauto. ii. eapply reg_in_blk_in_cdhp; eauto.
          clear - ATM_BIT. des; subst; eauto.
        }
      }

      (* cont does not exist *)
      right. unfold Thread.is_abort; s. split; eauto.
      left. ii. destruct H.
      do 2 des1. inv H; ss. inv BLK. rewrite CDHP_S_RET in STACK0. ss.
      inv H; ss.
    - (* be *)
      assert (EXPR_R_EQ: RegFile.eval_expr e R_t = RegFile.eval_expr e R_s).
      {
        eapply expr_eval_eq; eauto.
      }
      des1; subst; ss.
      {
        inv STATE; ss. symmetry in BLK. inv BLK.
        destruct BRANCH as [BRANCH | BRANCH].
        {
          des1.
          destruct (cdhp_s ! f1) eqn:CDHP_S_CONT.

          (* next block exists *)
          renames b' to BB_t, t to BB_s. left.
          lets LOOP_INVS': LOOP_INVS.
          unfold det_loop_invs in LOOP_INVS. rewrite PTree.gmap in LOOP_INVS.
          unfold option_map in LOOP_INVS.
          unfold Func in *. rewrite CDHP_S in LOOP_INVS.
          exploit transC'_prop; eauto.
          {
            instantiate (1 := ep). instantiate (1 := lo). 
            destruct (cdhp_s ! ep) eqn:CDHP_S'; ss; eauto. 
            right. exists t. split; eauto. inv LOOP_INVS; eauto.
            inv LOOP_INVS. eauto.
          }
          introv CONT_BB.
          do 5 eexists. splits.
          {
            eapply Operators_Properties.clos_rt1n_step; eauto.
            eapply Thread.na_tau_step_intro; eauto. econs; eauto.
            s. eapply State.step_be; eauto. rewrite <- EXPR_R_EQ. eauto.
          }
          {
            econs; eauto. econs; eauto. econs; eauto.
            ii. eapply reg_in_blk_in_cdhp; eauto.
            clear - ATM_BIT. des; subst; eauto.
          }

          (* next block does not exists *)
          right. unfold Thread.is_abort; s.
          splits; eauto. left. ii. destruct H.
          do 2 des1. inv H; ss. inv BLK.
          rewrite <- EXPR_R_EQ in BRANCH1.
          destruct BRANCH1 as [BRANCH1 | BRANCH1]; ss.
          des1. rewrite CDHP_S_CONT in BRANCH1. ss.
          des1. rewrite BRANCH0 in BRANCH2. ss.
          inv H; ss.
        }
        {
          des1.
          destruct (cdhp_s ! f2) eqn:CDHP_S_CONT.

          (* next block exists *)
          renames b' to BB_t, t to BB_s. left.
          lets LOOP_INVS': LOOP_INVS.
          unfold det_loop_invs in LOOP_INVS. rewrite PTree.gmap in LOOP_INVS.
          unfold option_map in LOOP_INVS.
          unfold Func in *. rewrite CDHP_S in LOOP_INVS.
          exploit transC'_prop; eauto.
          {
            instantiate (1 := ep). instantiate (1 := lo). 
            destruct (cdhp_s ! ep) eqn:CDHP_S'; ss; eauto. 
            right. exists t. split; eauto. inv LOOP_INVS; eauto.
            inv LOOP_INVS. eauto.
          }
          introv CONT_BB.
          do 5 eexists. splits.
          {
            eapply Operators_Properties.clos_rt1n_step; eauto.
            eapply Thread.na_tau_step_intro; eauto. econs; eauto.
            s. eapply State.step_be; eauto. rewrite <- EXPR_R_EQ. eauto.
          }
          {
            econs; eauto. econs; eauto. econs; eauto.
            ii. eapply reg_in_blk_in_cdhp; eauto.
            clear - ATM_BIT. des; subst; eauto.
          }

          (* next block does not exists *)
          right. unfold Thread.is_abort; s. 
          splits; eauto. left. ii. destruct H.
          do 2 des1. inv H; ss. inv BLK. 
          rewrite <- EXPR_R_EQ in BRANCH1. 
          destruct BRANCH1 as [BRANCH1 | BRANCH1]; ss.
          des1. rewrite BRANCH2 in BRANCH0. ss.
          des1. rewrite CDHP_S_CONT in BRANCH1. ss.
          inv H; ss.
        }
      }
      {
        inv BLK_REL.
        {
          inv STATE; ss. symmetry in BLK. inv BLK.
          destruct BRANCH as [BRANCH | BRANCH].
          { 
            des1. 
            destruct (cdhp_s ! f1) eqn:CDHP_S0; ss.

            (* the next block exists *)
            renames t to BB_s. left. renames b' to BB_t'.
            lets LOOP_INVS': LOOP_INVS.
            unfold det_loop_invs in LOOP_INVS'. rewrite PTree.gmap in LOOP_INVS'.
            unfold option_map in LOOP_INVS'.
            unfold Func in LOOP_INVS'. rewrite CDHP_S in LOOP_INVS'.
            destruct (cdhp_s ! ep) eqn: CDHP_S_EP; ss.
            
            lets TRANSC': TRANSC. 
            eapply well_defined_preheader with (lo := lo) in TRANSC; eauto.
            do 3 des1. rewrite TRANSC in CDHP_S0. inv CDHP_S0.
            do 5 eexists.
            splits.
            {
              eapply Operators_Properties.clos_rt1n_step; eauto.
              eapply Thread.na_tau_step_intro; eauto. econs; eauto.
              s. eapply State.step_be; eauto.
              rewrite <- EXPR_R_EQ; eauto.
            }
            {
              econs; eauto. econs; eauto. eapply EXEC_PH; eauto.
              clear - ATM_BIT. des; subst; eauto.
            }
            {
              instantiate (1 := ep). unfold loop_invC.
              inv LOOP_INVS'. eauto.
            }
            
            inv LOOP_INVS'. ss. inv TRANSC.
            rewrite PTree.gempty in PT. ss.

            (* the next block does not exist *)
            right. unfold Thread.is_abort; s. split; eauto.
            left. ii. destruct H.
            do 2 des1. inv H; ss. inv BLK.
            destruct BRANCH1 as [BRANCH1 | BRANCH1].
            {
              des1. rewrite CDHP_S0 in BRANCH1. tryfalse.
            }
            {
              des1. rewrite <- EXPR_R_EQ in BRANCH2.
              rewrite BRANCH0 in BRANCH2. ss.
            }
            inv H; ss.
          }
          {
            des1.
            destruct (cdhp_s ! f2) eqn:CDHP_S_CONT.

            (* next block exists *)
            renames b' to BB_t, t to BB_s. left.
            lets LOOP_INVS': LOOP_INVS.
            unfold det_loop_invs in LOOP_INVS. rewrite PTree.gmap in LOOP_INVS.
            unfold option_map in LOOP_INVS.
            unfold Func in *. rewrite CDHP_S in LOOP_INVS.
            exploit transC'_prop; eauto.
            {
              instantiate (1 := ep). instantiate (1 := lo). 
              destruct (cdhp_s ! ep) eqn:CDHP_S'; ss; eauto. 
              right. exists t. split; eauto. inv LOOP_INVS; eauto.
              inv LOOP_INVS. eauto.
            }
            introv CONT_BB.
            do 5 eexists. splits.
            {
              eapply Operators_Properties.clos_rt1n_step; eauto.
              eapply Thread.na_tau_step_intro; eauto. econs; eauto.
              s. eapply State.step_be; eauto. rewrite <- EXPR_R_EQ. eauto.
            }
            {
              econs; eauto. econs; eauto. econs; eauto.
              ii. eapply reg_in_blk_in_cdhp; eauto.
              clear - ATM_BIT. des; subst; eauto.
            }

            (* next block does not exists *)
            right. unfold Thread.is_abort; s. 
            splits; eauto. left. ii. destruct H.
            do 2 des1. inv H; ss. inv BLK. 
            rewrite <- EXPR_R_EQ in BRANCH1. 
            destruct BRANCH1 as [BRANCH1 | BRANCH1]; ss.
            des1. rewrite BRANCH2 in BRANCH0. ss.
            des1. rewrite CDHP_S_CONT in BRANCH1. ss.
            inv H; ss.
          }
        }
        {
          inv STATE; ss. symmetry in BLK. inv BLK.
          destruct BRANCH as [BRANCH | BRANCH].
          {
            des1.
            destruct (cdhp_s ! f1) eqn:CDHP_S_CONT.

            (* next block exists *)
            renames b' to BB_t, t to BB_s. left.
            lets LOOP_INVS': LOOP_INVS.
            unfold det_loop_invs in LOOP_INVS. rewrite PTree.gmap in LOOP_INVS.
            unfold option_map in LOOP_INVS.
            unfold Func in *. rewrite CDHP_S in LOOP_INVS.
            exploit transC'_prop; eauto.
            {
              instantiate (1 := ep). instantiate (1 := lo). 
              destruct (cdhp_s ! ep) eqn:CDHP_S'; ss; eauto. 
              right. exists t. split; eauto. inv LOOP_INVS; eauto.
              inv LOOP_INVS. eauto.
            }
            introv CONT_BB.
            do 5 eexists. splits.
            {
              eapply Operators_Properties.clos_rt1n_step; eauto.
              eapply Thread.na_tau_step_intro; eauto. econs; eauto.
              s. eapply State.step_be; eauto. rewrite <- EXPR_R_EQ. eauto.
            }
            {
              econs; eauto. econs; eauto. econs; eauto.
              ii. eapply reg_in_blk_in_cdhp; eauto.
              clear - ATM_BIT. des; subst; eauto.
            }

            (* next block does not exists *)
            right. unfold Thread.is_abort; s.
            splits; eauto. left. ii. destruct H.
            do 2 des1. inv H; ss. inv BLK.
            rewrite <- EXPR_R_EQ in BRANCH1.
            destruct BRANCH1 as [BRANCH1 | BRANCH1]; ss.
            des1. rewrite CDHP_S_CONT in BRANCH1. ss.
            des1. rewrite BRANCH0 in BRANCH2. ss.
            inv H; ss.
          }
          {
            des1. 
            destruct (cdhp_s ! f2) eqn:CDHP_S0; ss.

            (* the next block exists *)
            renames t to BB_s. left. renames b' to BB_t'.
            lets LOOP_INVS': LOOP_INVS.
            unfold det_loop_invs in LOOP_INVS'. rewrite PTree.gmap in LOOP_INVS'.
            unfold option_map in LOOP_INVS'.
            unfold Func in LOOP_INVS'. rewrite CDHP_S in LOOP_INVS'.
            destruct (cdhp_s ! ep) eqn: CDHP_S_EP; ss.
            
            lets TRANSC': TRANSC. 
            eapply well_defined_preheader with (lo := lo) in TRANSC; eauto.
            do 3 des1. rewrite TRANSC in CDHP_S0. inv CDHP_S0.
            do 5 eexists.
            splits.
            {
              eapply Operators_Properties.clos_rt1n_step; eauto.
              eapply Thread.na_tau_step_intro; eauto. econs; eauto.
              s. eapply State.step_be; eauto.
              rewrite <- EXPR_R_EQ; eauto.
            }
            {
              econs; eauto. econs; eauto. eapply EXEC_PH; eauto.
              clear - ATM_BIT. des; subst; eauto.
            }
            {
              instantiate (1 := ep). unfold loop_invC.
              inv LOOP_INVS'. eauto.
            }
            
            inv LOOP_INVS'. ss. inv TRANSC.
            rewrite PTree.gempty in PT. ss.

            (* the next block does not exist *)
            right. unfold Thread.is_abort; s. split; eauto.
            left. ii. destruct H.
            do 2 des1. inv H; ss. inv BLK.
            destruct BRANCH1 as [BRANCH1 | BRANCH1].
            {
              des1. rewrite <- EXPR_R_EQ in BRANCH2. rewrite BRANCH2 in BRANCH0. ss.
            }
            {
              des1. rewrite CDHP_S0 in BRANCH1. tryfalse.
            }
            inv H; ss.
          }
        }
        {
          inv STATE; ss. symmetry in BLK. inv BLK.
          destruct BRANCH as [BRANCH | BRANCH].
          {
            des1.  
            destruct (cdhp_s ! f1) eqn:CDHP_S0; ss.

            (* the next block exists *)
            renames t to BB_s. left. renames b' to BB_t'.
            lets LOOP_INVS': LOOP_INVS.
            unfold det_loop_invs in LOOP_INVS'. rewrite PTree.gmap in LOOP_INVS'.
            unfold option_map in LOOP_INVS'.
            unfold Func in LOOP_INVS'. rewrite CDHP_S in LOOP_INVS'.
            destruct (cdhp_s ! ep) eqn: CDHP_S_EP; ss.
            
            lets TRANSC': TRANSC. clear PT2.
            eapply well_defined_preheader with (lo := lo) in TRANSC; eauto.
            do 3 des1. rewrite TRANSC in CDHP_S0. inv CDHP_S0.
            do 5 eexists.
            splits.
            {
              eapply Operators_Properties.clos_rt1n_step; eauto.
              eapply Thread.na_tau_step_intro; eauto. econs; eauto.
              s. eapply State.step_be; eauto.
              rewrite <- EXPR_R_EQ; eauto.
            }
            {
              econs; eauto. econs; eauto. eapply EXEC_PH; eauto.
              clear - ATM_BIT. des; subst; eauto.
            }
            {
              instantiate (1 := ep). unfold loop_invC.
              inv LOOP_INVS'. eauto.
            }
            
            inv LOOP_INVS'. ss. inv TRANSC.
            rewrite PTree.gempty in PT1. ss.

            (* the next block does not exist *)
            right. unfold Thread.is_abort; s. split; eauto.
            left. ii. destruct H.
            do 2 des1. inv H; ss. inv BLK.
            destruct BRANCH1 as [BRANCH1 | BRANCH1].
            {
              des1. rewrite CDHP_S0 in BRANCH1. tryfalse.
            }
            {
              des1. rewrite <- EXPR_R_EQ in BRANCH2. rewrite BRANCH0 in BRANCH2. ss.
            }
            inv H; ss.
          }
          {
            des1.  
            destruct (cdhp_s ! f2) eqn:CDHP_S0; ss.

            (* the next block exists *)
            renames t to BB_s. left. renames b' to BB_t'.
            lets LOOP_INVS': LOOP_INVS.
            unfold det_loop_invs in LOOP_INVS'. rewrite PTree.gmap in LOOP_INVS'.
            unfold option_map in LOOP_INVS'.
            unfold Func in LOOP_INVS'. rewrite CDHP_S in LOOP_INVS'.
            destruct (cdhp_s ! ep) eqn: CDHP_S_EP; ss.
            
            lets TRANSC': TRANSC.
            eapply well_defined_preheader with (lo := lo) in TRANSC; eauto.
            do 3 des1. rewrite TRANSC in CDHP_S0. inv CDHP_S0.
            do 5 eexists.
            splits.
            {
              eapply Operators_Properties.clos_rt1n_step; eauto.
              eapply Thread.na_tau_step_intro; eauto. econs; eauto.
              s. eapply State.step_be; eauto.
              rewrite <- EXPR_R_EQ; eauto.
            }
            {
              econs; eauto. econs; eauto. eapply EXEC_PH; eauto.
              clear - ATM_BIT. des; subst; eauto.
            }
            {
              instantiate (1 := ep). unfold loop_invC.
              inv LOOP_INVS'. eauto.
            }
            
            inv LOOP_INVS'. ss. inv TRANSC.
            rewrite PTree.gempty in PT1. ss.

            (* the next block does not exist *)
            right. unfold Thread.is_abort; s. split; eauto.
            left. ii. destruct H.
            do 2 des1. inv H; ss. inv BLK.
            destruct BRANCH1 as [BRANCH1 | BRANCH1].
            {
              des1. rewrite <- EXPR_R_EQ in BRANCH2. rewrite BRANCH2 in BRANCH0. ss.
            }
            {
              des1. rewrite CDHP_S0 in BRANCH1. tryfalse.
            }
            inv H; ss.
          }
        }
      }
    - (* ret *)
      des1. subst. left. ss.
      inv STATE; ss. clear BLK.
      inv MATCH_CONT.
      do 5 eexists.
      splits.
      {
        eapply Operators_Properties.clos_rt1n_step; eauto.
        eapply Thread.na_tau_step_intro; eauto. econs; eauto.
        s. eapply State.step_ret; eauto.
      }
      {
        econs; eauto. econs; eauto.
        clear - ATM_BIT. des; subst; eauto.
      }
      inv BLK_REL.
    - (* instr *)
      eapply BBlock_cons in BLK_REL. do 2 des1. subst. renames BB_s to BB_s'.
      destruct c; ss;
        try solve [inv STATE; ss; inv BLK; ss]; tryfalse.
      {
        (* skip *)
        inv STATE; tryfalse. symmetry in BLK. inv BLK.
        left.
        do 5 eexists.
        splits.
        {
          eapply Operators_Properties.clos_rt1n_step; eauto.
          eapply Thread.na_tau_step_intro; eauto. econs; eauto.
          s. eapply State.step_skip; eauto.
        }
        {
          econs; eauto. econs; eauto. econs; eauto.
          clear - ATM_BIT. des; subst; eauto.
        }
      }
      {
        (* assign *)
        assert (EXPR_R_EQ: RegFile.eval_expr rhs R_t = RegFile.eval_expr rhs R_s).
        {
          eapply expr_eval_eq; eauto.
          ii. eapply ORIGN_REGS; eauto. eapply SUBSET_REG; eauto.
          eapply RegSet.union_spec. left.
          eapply RegSet.add_spec. eauto.
        }
        left. inv STATE; ss. symmetry in BLK. inv BLK.
        do 5 eexists.
        splits.
        {
          eapply Operators_Properties.clos_rt1n_step; eauto.
          eapply Thread.na_tau_step_intro; eauto. econs; eauto.
          s. eapply State.step_assign; eauto.
        }
        {
          econs; eauto. econs; eauto. econs; eauto.
          rewrite <- EXPR_R_EQ. ii.
          destruct (Pos.eq_dec r lhs); subst.
          do 2 (rewrite RegFun.add_spec_eq). eauto.
          do 2 (rewrite RegFun.add_spec_neq; eauto).
          ii. eapply SUBSET_REG; eauto.
          eapply RegSet.union_spec; eauto.
          clear - ATM_BIT. des; subst; eauto.
        }
      }
  }
  {
    (* execution preheader *)
    left. simpl in STATE. destruct BB_t; ss.
    {
      (* jmp *)
      des_ifH WDPH; tryfalse. subst f0.
      inv STATE; tryfalse. symmetry in BLK. inv BLK. renames b' to BB_t.
      exploit transC'_prop; eauto.
      {
        instantiate (1 := ep). instantiate (1 := lo).
        unfold det_loop_invs in LOOP_INVS. rewrite PTree.gmap in LOOP_INVS.
        unfold option_map in LOOP_INVS.
        unfold Func in LOOP_INVS. rewrite CDHP_S in LOOP_INVS.
        destruct (cdhp_s ! ep) eqn:CDHP_S_EP; ss; eauto.
        right. exists t. split; eauto. inv LOOP_INVS; eauto.
        left. inv LOOP_INVS; eauto.
      }

      i. do 5 eexists.
      splits. eauto.
      econs; eauto. econs; eauto. econs; eauto.
      ii. eapply reg_in_blk_in_cdhp; eauto.
      clear - ATM_BIT. des; subst; eauto.
    }
    {
      destruct c; ss.

      (* assign *)
      des1. do 5 eexists.
      splits. eauto. inv STATE; tryfalse.
      symmetry in BLK. inv BLK.
      econs; eauto. econs; eauto.
      eapply EXEC_PH; eauto.
      {
        ii. destruct (Pos.eq_dec r lhs); subst; tryfalse.
        rewrite RegFun.add_spec_neq; eauto.
      }
      clear - ATM_BIT. des; subst; eauto.

      (* na load *)
      destruct or; ss. inv STATE; tryfalse.
    }
  }
Qed.

Lemma na_read_step_case
      inj lo b loc to v R
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_linv inj lo b
                               (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                               (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (TGT_STEP: Thread.program_step (ThreadEvent.read loc to v R Ordering.plain) lo
                                     (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                                     (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')):
  exists state_src' tview_src' prm_src' sc_src' mem_src',
    rtc (Thread.na_step lo) 
         (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
         (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
    match_state_linv inj lo false
                     (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                     (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src').
Proof.
  inv MATCH. inv TGT_STEP. inv LOCAL. ss.
  do 2 des1. subst. inv STATE; tryfalse.
  inv MATCH_THRD_LOCAL.
  inv MATCH_CUR.
  - renames b' to BB_t'.
    eapply BBlock_cons' in BLK_REL. destruct BLK_REL as (BB_s' & BLK & BLK_REL). subst BB_s. ss.
    exploit Local_read_tview_le_prsv; eauto; s; eauto.
    {
      eapply mem_id_le_identity; eauto.
    }
    i. do 5 des1. destruct lc2'. ss. renames promises to prm_src', tview to tview_src'.
    assert (PRM_EQ: prm_tgt = prm_tgt' /\ prm_tgt = prm_src').
    {
      clear - LOCAL0 LE_READ. inv LOCAL0; ss. inv LC2. inv LE_READ. ss. inv LC2.
      eauto.
    }
    des1. subst. 
    do 5 eexists.
    split.
    {
      eapply Operators_Properties.clos_rt1n_step; eauto.
      eapply Thread.na_plain_read_step_intro; eauto.
      econs; eauto. s. eapply State.step_load; eauto.
    }
    {
      eapply match_state_linv_intro with (inj' := (spec_inj mem_tgt')); eauto.
      s. splits; eauto.
      econs; eauto. 
      econs; eauto.
      {
        clear - ORIGN_REGS. ii.
        destruct (Pos.eq_dec r0 r); subst; eauto.
        do 2 (rewrite RegFun.add_spec_eq; eauto).
        do 2 (rewrite RegFun.add_spec_neq; eauto).
      }
      {
        clear - SUBSET_REG. ii. eapply SUBSET_REG; eauto.
        eapply RegSet.union_spec; eauto.
      }
      {
        clear - BLK_REL. des; eauto.
      }
      clear - ATM_BIT. des; subst; eauto.
      eapply local_wf_read; eauto.
      eapply local_wf_read; eauto.
    }
  - simpl in WDPH. do 2 des1. renames b' to BB_t'.
    exploit Local.read_step_future; eauto. s. i. do 3 des1.
    do 5 eexists.
    splits. eauto.
    assert (prm_tgt = prm_tgt').
    {
      clear - LOCAL0. inv LOCAL0; ss. inv LC2. eauto.
    }
    subst prm_tgt'.
    eapply match_state_linv_intro with (inj' := (spec_inj mem_tgt')); eauto.
    s. splits; eauto.
    econs; eauto.
    {
      eapply EXEC_PH; eauto.
      clear - ORIGN_REGS WDPH. ii.
      destruct (Pos.eq_dec r0 r); subst; tryfalse.
      rewrite RegFun.add_spec_neq; eauto.
    }
    {
      eapply TView.TView.le_PreOrder_obligation_2; eauto.
    }
    {
      clear - ATM_BIT. des; subst; eauto.
    }
Qed.

Lemma na_write_step_case
      inj lo b loc from to v R
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_linv inj lo b
                               (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                               (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (TGT_STEP: Thread.program_step (ThreadEvent.write loc from to v R Ordering.plain) lo
                                     (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                                     (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')):
  exists state_src' tview_src' prm_src' sc_src' mem_src',
    Thread.program_step (ThreadEvent.write loc from to v R Ordering.plain) lo 
                        (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src)
                        (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src') /\
    match_state_linv inj lo false
                     (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                     (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src').
Proof.
  inv MATCH. inv TGT_STEP. inv LOCAL. ss. do 2 des1. subst.
  inv STATE. inv MATCH_THRD_LOCAL. inv MATCH_CUR.
  - eapply BBlock_cons' in BLK_REL. do 2 des1. subst. renames b' to BB_t'.
    exploit Local_write_tview_le_prsv;
      [eapply LOCAL0 | eapply MEM_LE |
       instantiate (1 := Local.mk tview_src prm_tgt); eauto | eauto..].

    instantiate (1 := sc_src). i. do 7 des1. ss. destruct lc2' as (tview_src' & prm_src'). ss; subst.
    renames mem2' to mem_src', rf to R_t.
    assert (REG_EvAL_EQ: RegFile.eval_expr e R_s = RegFile.eval_expr e R_t).
    {
      eapply expr_eval_eq; eauto.
      ii. symmetry. eapply ORIGN_REGS; eauto. eapply SUBSET_REG; eauto.
      eapply RegSet.union_spec. left. eauto.
    }
    assert (R = None).
    {
      clear - LOCAL0. inv LOCAL0; ss.
    }
    subst R.
    assert (released' = None).
    {
      clear - LE_WRITE. inv LE_WRITE; ss.
    }
    subst released'.
    do 5 eexists. split.
    {
      econs; eauto. s. econs; eauto.
    }
    {
      eapply match_state_linv_intro with (inj' := spec_inj mem_tgt'); eauto.
      {
        (* inv *)
        s. splits; eauto. inv LOCAL0; ss.
      }      
      {
        (* match tlocal *)
        econs; eauto. econs; eauto. ii. eapply SUBSET_REG; eauto.
        eapply RegSet.union_spec; eauto.
        clear - BLK_REL0. des; subst; eauto.
      }
      {
        (* prm *)
        introv PRM_GET.
        exploit concrete_prm_local_write_noadd; [eapply LE_WRITE | eauto..].
        s. i. do 4 des1. eapply PRM_INDOM; eauto.
      }
      {
        (* atomic bit *) 
        assert (forall loc to from val R, Memory.get loc to mem_tgt = Some (from, Message.concrete val R) ->
                                     exists from' R',
                                       Memory.get loc to mem_tgt' = Some (from', Message.concrete val R')).
        {
          ii. eapply write_step_concrete_msg_prsv; eauto.
        }
        left. splits; eauto. clear BLK_REL0. des; subst; eauto.
        {
          clear - ATM_BIT0 H. ii. exploit ATM_BIT0; eauto. ii.
          unfold spec_inj in *; ss.
          destruct (Memory.get loc t mem_tgt) eqn:Heqe; ss.
          destruct p. destruct t1; ss. inv H1. exploit H; eauto. i. des.
          rewrite H1; eauto.
        }
        {
          clear - H. ii. unfold spec_inj in *; ss.
          destruct (Memory.get loc t mem_tgt) eqn:Heqe; ss.
          destruct p. destruct t1; ss. inv H0.
          exploit H; eauto. i. des. rewrite H0; ss.
        }        
      } 
      {
        eapply local_wf_write; eauto.
      }
      {
        inv LOCAL0. simpl in LC2. inv LC2.
        inv WRITE. inv PROMISE; ss.
        eapply Memory.add_closed_timemap; eauto.
        eapply Memory.split_closed_timemap; eauto.
        eapply Memory.lower_closed_timemap; eauto.
      }
      {
        eapply write_step_closed_mem; eauto.
      }
      {
        eapply local_wf_write; eauto.
      }
      {
        inv LE_WRITE. simpl in LC2. inv LC2.
        inv WRITE. inv PROMISE; ss.
        eapply Memory.add_closed_timemap; eauto.
        eapply Memory.split_closed_timemap; eauto.
        eapply Memory.lower_closed_timemap; eauto.
      }
      {
        eapply write_step_closed_mem; eauto.
      }
    }
  - inv WDPH; ss.
Qed.

Lemma promise_step_case
      inj lo te
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_linv inj lo true
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
    match_state_linv inj' lo true
                     (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                     (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src').
Proof.
  inv MATCH. des; ss; subst; des; ss. inv TGT_STEP; ss.
  inv STEP; ss.
  exploit Local_promise_tview_prsv; [eapply LOCAL | eapply MEM_LE | idtac..]; ss.
  instantiate (1 := Local.mk tview_src prm_tgt). s. eauto.
  s; eauto. eauto.

  i. do 5 des1. subst.
  destruct lc2' as (tview_src' & prm_src'); ss.
  eexists. exists tview_src' prm_src' sc_src mem2' (spec_inj mem_tgt').
  splits.
  {
    eapply Operators_Properties.clos_rt1n_step; eauto.
    econs; eauto. econs; eauto.
  }
  {
    unfold incr_inj, spec_inj. ii.
    destruct (Memory.get loc0 t mem_tgt) eqn:GET; ss. destruct p; ss.
    destruct t1; ss. inv H.
    inv LOCAL; ss. inv LC2; ss. inv PROMISE; ss.
    {
      eapply Memory.add_get1 in GET; eauto. rewrite GET; ss.
    }
    {
      eapply Memory.split_get1 in GET; eauto.
      destruct GET as (f' & GET & LE). rewrite GET; ss.
    }
    {
      do 2 des1. subst.
      eapply Memory.lower_get1 in GET; eauto.
      destruct GET as (m' & GET & LE). rewrite GET; ss.
      exploit lower_succeed_wf; eauto. i. do 5 des1.
      inv MSG_LE; ss. inv LE; ss.
    }
  }
  {
    econs; eauto.
    {
      (* invariant *)
      s. splits; eauto.
    }
    {
      (* inj *)
      ii. exploit Local.promise_step_future; [eapply LE_PRM | eauto..].
      s. i. do 3 des1. inv WF2; ss.
      eapply PROMISES in H. unfold spec_inj.
      clear - H MEM_LE'. inv MEM_LE'; ss.
      eapply SOUND in H; eauto. des. rewrite H; eauto.
    }
    {
      (* local wf tgt *)
      exploit Local.promise_step_future; [eapply LOCAL | eauto..].
      i. do 2 des1. eauto.
    }
    {
      (* closed timemap tgt  *)
      inv LOCAL; ss.
      eapply Memory.promise_closed_timemap; eauto.
    }
    {
      (* mem tgt *)
      eapply promise_step_closed_mem; eauto.
    }
    {
      (* local wf src *)
      exploit Local.promise_step_future; [eapply LE_PRM | eauto..].
      i. do 2 des1. eauto.
    }
    {
      (* closed timemap src  *)
      inv LE_PRM; ss.
      eapply Memory.promise_closed_timemap; eauto.
    }
    {
      (* mem src *)
      eapply promise_step_closed_mem; eauto.
    }
  }
Qed.

Lemma pf_promise_step_case
      inj lo b te
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_tgt' tview_tgt' prm_tgt' sc_tgt' mem_tgt'
      state_src tview_src prm_src sc_src mem_src 
      (MATCH: match_state_linv inj lo b
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
    match_state_linv inj lo b
                     (Thread.mk rtl_lang state_tgt' (Local.mk tview_tgt' prm_tgt') sc_tgt' mem_tgt')
                     (Thread.mk rtl_lang state_src' (Local.mk tview_src' prm_src') sc_src' mem_src').
Proof.
  inv TGT_STEP; ss.
  2: { inv STEP; ss; eauto. inv LOCAL; ss; des; ss; tryfalse. }
  inv STEP.
  inv MATCH; ss. do 4 des1; subst.
  destruct msg; ss.
  - destruct released; ss; eauto. destruct kind; ss.
    destruct msg1; ss; eauto.
    inv LOCAL; ss. inv PROMISE; ss; eauto.
    destruct kind; ss. destruct msg1; ss.
    2: {  inv LOCAL; ss. inv PROMISE; ss; tryfalse. } 
    exploit lower_to_none_tview_le_prsv; [eapply LOCAL | eapply MEM_LE | | | eapply LOCAL_WF_SRC | eauto..]; eauto.
    s. i. do 4 des1. subst.
    destruct lc2' as (tview_src' & prm_src').
    do 5 eexists.
    splits.
    {
      eapply Operators_Properties.clos_rt1n_step; eauto.
      econs; eauto. econs; eauto.
    }
    {
      eapply match_state_linv_intro with (inj' := spec_inj mem_tgt'); eauto.
      econs; eauto.
      {
        (* view le *)
        inv LOCAL; ss. inv LC2. inv LE_WRITE; ss. inv LC2; ss.
      }
      {
        (* promise inj *)
        s. i. inv LE_WRITE; ss. inv LC2; ss.
        inv PROMISE; ss. do 2 des1. inv RESERVE.
        erewrite Memory.lower_o in H; eauto.
        des_ifH H; ss. des1; subst. inv H.
        exploit Memory.lower_get0; [eapply PROMISES | eauto..].
        i. do 2 des1. eauto.
        eauto.
      }
      {
        (* inj *)
        des; subst; eauto.
        {
          left. splits; eauto.
          ii.  eapply ATM_BIT0 in H; eauto. unfold spec_inj in *; ss.
          destruct (Memory.get loc1 t0 mem_tgt) eqn:Heqe; ss.
          destruct p; ss. destruct t2; ss. inv H.
          inv LOCAL; ss. inv LC2; ss. inv PROMISE; ss.
          do 2 des1; subst; ss. inv RESERVE. 
          eapply Memory.lower_get1 in Heqe; eauto. do 2 des1.
          inv MSG_LE; ss. rewrite GET2; ss.
        }
        {
          right. split; eauto.
          eapply functional_extensionality; eauto. i.
          eapply functional_extensionality; eauto. i.
          unfold spec_inj.
          inv LOCAL; ss. inv LC2; ss. inv PROMISE; ss. des. inv RESERVE.
          destruct (Memory.get x x0 mem_tgt) eqn:Heqe1;
            destruct (Memory.get x x0 mem_tgt') eqn:Heqe2; ss; eauto.
          {
            destruct p, p0; ss. destruct t1, t3; ss.
            eapply Memory.lower_get1 in Heqe1; eauto.
            do 2 des1. inv MSG_LE; ss. rewrite Heqe2 in GET2; ss.
            erewrite Memory.lower_o in Heqe2; eauto.
            des_ifH Heqe2; ss; subst.
            des1; subst; ss. inv Heqe2; ss.
            exploit Memory.lower_get0; [eapply MEM | eauto..]. i. do 2 des1.
            rewrite Heqe1 in GET. ss.
            rewrite Heqe1 in Heqe2; ss.
          }
          {
            destruct p; ss. destruct t1; ss; eauto.
            eapply Memory.lower_get1 in Heqe1; eauto.
            do 2 des1. rewrite Heqe2 in GET2; ss.
          }
          {
            destruct p; ss. destruct t1; ss.
            erewrite Memory.lower_o in Heqe2; eauto.
            des_ifH Heqe2; ss. des1; subst.
            inv Heqe2. exploit Memory.lower_get0; [eapply MEM | eauto..].
            i. do 2 des1. rewrite Heqe1 in GET. tryfalse.
            rewrite Heqe1 in Heqe2; ss.
          }
        }
      }
      {
        (* local wf tgt *)
        s.
        exploit Local.promise_step_future; [eapply LOCAL | eauto..]. s.
        i. do 2 des1. eauto.
      }
      {
        (* closed timemap tgt  *)
        inv LOCAL; ss.
        eapply Memory.promise_closed_timemap; eauto.
      }
      {
        (* mem tgt *)
        eapply promise_step_closed_mem; eauto.
      }
      {
        (* local wf src *)
        exploit Local.promise_step_future; [eapply LE_WRITE | eauto..].
        i. do 2 des1. eauto.
      }
      {
        (* closed timemap src  *)
        inv LE_WRITE; ss.
        eapply Memory.promise_closed_timemap; eauto.
      }
      {
        (* mem src *)
        eapply promise_step_closed_mem; eauto.
      }
    }
  - lets LOCAL': LOCAL. inv LOCAL'; ss. symmetry in LC2. inv LC2.
    destruct kind; ss. destruct msg1; ss.
    exploit cancel_tview_le_prsv;
      [eapply LOCAL | eapply MEM_LE | | eapply LOCAL_WF_TGT | eapply LOCAL_WF_SRC | eauto..]; eauto.
    s. i. do 4 des1. destruct lc2' as (tview_src' & prm_src'); ss. subst.
    eexists. exists tview_src' prm_tgt' sc_src mem2'.
    splits.
    {
      eapply Operators_Properties.clos_rt1n_step; eauto.
      econs; eauto. econs; eauto.
    }
    {
      eapply match_state_linv_intro with (inj' := spec_inj mem_tgt'); eauto.
      {
        (* inv *)
        econs; eauto.
      }
      {
        (* TView le *)
        inv LE_WRITE; ss; eauto. inv LC2. eauto.
      }
      {
        (* inj *)
        clear - LOCAL PRM_INDOM. inv LOCAL; ss. inv LC2; ss. ii.
        inv PROMISE; ss. erewrite Memory.remove_o in H; eauto.
        des_ifH H; ss. eauto.
      }
      {
        des; subst; eauto.
        {
          left; splits; eauto.
          clear - ATM_BIT0 LOCAL. inv LOCAL; ss. inv LC2; ss.
          inv PROMISE; ss. ii. eapply ATM_BIT0 in H.
          unfold spec_inj in *; ss.
          destruct (Memory.get loc0 t mem_tgt) eqn:Heqe; ss.
          destruct p; ss. destruct t1; ss. inv H.
          eapply Memory.concrete_msg_remove_rsv_stable in Heqe; eauto.
          rewrite Heqe; ss.
        }
        {
          right. split; eauto.
          eapply functional_extensionality; eauto. i.
          eapply functional_extensionality; eauto. i.
          unfold spec_inj.
          inv LOCAL; ss. inv LC2; ss. inv PROMISE; ss.
          destruct (Memory.get x x0 mem_tgt) eqn:Heqe1;
            destruct (Memory.get x x0 mem_tgt') eqn:Heqe2; ss; eauto.
          {
            destruct p, p0; ss. destruct t1, t3; ss.
            eapply Memory.concrete_msg_remove_rsv_stable in Heqe1; eauto.
            rewrite Heqe1 in Heqe2. tryfalse.
            erewrite Memory.remove_o in Heqe2; eauto.
            des_ifH Heqe2; ss. rewrite Heqe1 in Heqe2. ss.
          }
          {
            destruct p; ss. destruct t1; ss; eauto.
            eapply Memory.concrete_msg_remove_rsv_stable in Heqe1; eauto.
            rewrite Heqe2 in Heqe1. tryfalse.
          }
          {
            destruct p; ss. destruct t1; ss.
            erewrite Memory.remove_o in Heqe2; eauto.
            des_ifH Heqe2; ss. rewrite Heqe1 in Heqe2. ss.
          }
        }
      }
      {
        (* local wf tgt *)
        s.
        exploit Local.promise_step_future; [eapply LOCAL | eauto..]. s.
        i. do 2 des1. eauto.
      }
      {
        (* closed timemap tgt  *)
        inv LOCAL; ss.
        eapply Memory.promise_closed_timemap; eauto.
      }
      {
        (* mem tgt *)
        eapply promise_step_closed_mem; eauto.
      }
      {
        (* local wf src *)
        exploit Local.promise_step_future; [eapply LE_WRITE | eauto..].
        i. do 2 des1. eauto.
      }
      {
        (* closed timemap src  *)
        inv LE_WRITE; ss.
        eapply Memory.promise_closed_timemap; eauto.
      }
      {
        (* mem src *)
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
      (MATCH: match_state_linv inj lo true
                               (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                               (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (RELY: Rely inj (Build_Rss sc_tgt mem_tgt sc_src mem_src)
                  inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src')
                  prm_tgt prm_src lo)
      (INV: I_linv lo inj' (Build_Rss sc_tgt' mem_tgt' sc_src' mem_src')):
  match_state_linv inj' lo true
                   (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt' mem_tgt')
                   (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src' mem_src').
Proof.
  inv MATCH. inv RELY; ss. inv ENV_STEPS; ss.
  do 2 des1. do 2 des1. subst.
  econs; eauto.
  {
    (* Inv *)
    econs; eauto.
  }
  {
    (* prm indom *)
    clear - PRM_TGT_IN. ii.
    eapply PRM_TGT_IN in H. unfold spec_inj. rewrite H; ss. eauto.
  }
  {
    (* local wf tgt *)
    eapply concrete_incr_local_wf_prsv.
    2: { simpl; simpl in PRM_TGT_IN; eauto. }
    2: { eapply LOCAL_WF_TGT. }
    clear - MEM_TGT_INCR. ss.
    unfold concrete_mem_incr in MEM_TGT_INCR.
    ii. eapply MEM_TGT_INCR in H; des; eauto.
  }
  {
    (* local wf src *)
    eapply concrete_incr_local_wf_prsv.
    2: { simpl; simpl in PRM_TGT_IN; eauto. }
    2: { eapply LOCAL_WF_SRC. }
    clear - MEM_SRC_INCR. ss.
    unfold concrete_mem_incr in MEM_SRC_INCR.
    ii. eapply MEM_SRC_INCR in H; des; eauto.
  }
Qed.

Lemma done_step_case
      inj lo b
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_src tview_src prm_src sc_src mem_src
      (MATCH: match_state_linv inj lo b
                               (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                               (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (DONE: Thread.is_done (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)):
  exists inj',
      Thread.is_done (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src) /\
      incr_inj inj inj' /\
      I_linv lo inj' (Build_Rss sc_tgt mem_tgt sc_src mem_src).
Proof.
  inv DONE; ss. des. subst.
  inv MATCH; ss. do 2 des1. subst.
  exists (spec_inj mem_tgt).
  splits; eauto.
  {
    econs; ss; eauto.
    unfold State.is_terminal in *; ss. des1; subst.
    inv MATCH_THRD_LOCAL; ss; subst; ss.
    inv MATCH_CONT; ss. inv MATCH_CUR; ss; eauto.
    destruct BLK_REL; ss.
    inv H.
  }
  {
    clear - ATM_BIT. des; subst; eauto.
    ii. eauto.
  }
Qed.
  
Lemma abort_step_case
      inj lo b
      state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
      state_src tview_src prm_src sc_src mem_src
      (MATCH: match_state_linv inj lo b
                               (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                               (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src))
      (ABORT: Thread.is_abort (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt) lo):
  Thread.is_abort (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src) lo.
Proof.
  inv MATCH; ss; subst. unfold Thread.is_abort in *; ss.
  do 2 des1. des1.
  splits.
  {
    clear - PROMISES TVIEW_LE.
    unfold Local.promise_consistent in *; ss. ii.
    inv TVIEW_LE; ss.
    eapply PROMISES in PROMISE.
    inv CUR; ss. unfold TimeMap.le in RLX.
    specialize (RLX loc).
    auto_solve_time_rel.
  }
  {
    destruct ABORT0 as [ABORT | ABORT].
    {
      left. ii. contradiction ABORT. clear ABORT.
      destruct H as [PROGRESS_SRC | TERMINAL_SRC].
      {
        do 2 des1. left. inv MATCH_THRD_LOCAL; ss.
        inv PROGRESS_SRC; ss.
        {
          (* skip *)
          inv MATCH_CUR; ss.
          eapply BBlock_cons in BLK_REL. do 2 des1. subst.
          do 2 eexists. econs; eauto.
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* assign *)
          inv MATCH_CUR; ss.
          eapply BBlock_cons in BLK_REL. do 2 des1. subst.
          do 2 eexists. eapply State.step_assign; eauto.
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* load *)
          inv MATCH_CUR; ss.
          eapply BBlock_cons in BLK_REL. do 2 des1. subst.
          do 2 eexists. eapply State.step_load; eauto.
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* store *)
          inv MATCH_CUR; ss.
          eapply BBlock_cons in BLK_REL. do 2 des1. subst.
          do 2 eexists. eapply State.step_store; eauto.
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* print *)
          inv MATCH_CUR; ss.
          eapply BBlock_cons in BLK_REL. do 2 des1. subst.
          do 2 eexists. eapply State.step_out; eauto.
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* cas same *)
          inv MATCH_CUR; ss.
          eapply BBlock_cons in BLK_REL. do 2 des1. subst.
          do 2 eexists. eapply State.step_cas_same; eauto.
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* cas flip *)
          inv MATCH_CUR; ss.
          eapply BBlock_cons in BLK_REL. do 2 des1. subst.
          assert (EVAL_EQ: RegFile.eval_expr er R_t = RegFile.eval_expr er R_s).
          {
            eapply expr_eval_eq; eauto.
            ii. eapply ORIGN_REGS; eauto. eapply SUBSET_REG; eauto.
            eapply RegSet.union_spec. left.
            eapply RegSet.add_spec. right. eapply RegSet.union_spec; eauto.
          }
          do 2 eexists. eapply State.step_cas_flip; eauto.
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* call *)
          inv MATCH_CUR; ss.
          destruct BLK_REL as [BLK_REL | BLK_REL]; subst.
          {
            exploit well_defined_preheader3; [eapply TRANSC | eapply STACK | eauto..].
            i. des1. renames H to TGT_RET.
            assert (TGT_CALL_FUNC: exists ch0' f0' b2',
                       prog_t ! f = Some (ch0', f0') /\ ch0' ! f0' = Some b2').
            {
              unfold LInv in *. inv OPT. rewrite PTree.gmap. 
              unfold option_map. rewrite FIND_FUNC.
              destruct ((det_loop_invs prog_s lo) ! f) eqn:Heqe; ss; eauto.
              destruct (TransC' ch0 (PTree.empty positive) l l (Pos.succ (max_labelled_node (PTree.elements ch0) 1)))
                       eqn:TRANSC'; ss.
              destruct p; ss.
              exploit well_defined_preheader3; [eapply TRANSC' | eapply ENTRY_BLK | eauto..].
              i. des1. destruct (t ! f0) eqn: PRE_HEADER_SRC; ss.
              eapply well_defined_preheader4 in TRANSC'; eauto.
              destruct TRANSC' as [TRANSC' | TRANSC']. rewrite PTree.gempty in TRANSC'. ss.
              des1. do 3 eexists. splits; eauto.
              do 3 eexists. splits; eauto.
            }
            destruct TGT_CALL_FUNC as (ch0' & f0' & b2' & PROG_TGT & CDHP_TGT).
            do 2 eexists.
            eapply State.step_call; eauto.
          }
          {
            inv BLK_REL; ss.
          }
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* ret *)
          inv MATCH_CONT; ss. inv MATCH_CUR; ss.
          destruct BLK_REL as [BLK_REL | BLK_REL]; subst.
          do 2 eexists. eapply State.step_ret; eauto.
          inv BLK_REL.
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* fence-rel *)
          inv MATCH_CUR; ss.
          eapply BBlock_cons in BLK_REL. do 2 des1. subst.
          do 2 eexists. eapply State.step_fence_rel; eauto.
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* fence-acq *)
          inv MATCH_CUR; ss.
          eapply BBlock_cons in BLK_REL. do 2 des1. subst.
          do 2 eexists. eapply State.step_fence_acq; eauto.
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* fence-sc *)
          inv MATCH_CUR; ss.
          eapply BBlock_cons in BLK_REL. do 2 des1. subst.
          do 2 eexists. eapply State.step_fence_sc; eauto.
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* jmp *)
          inv MATCH_CUR; ss.
          destruct BLK_REL as [BLK_REL | BLK_REL]; subst.
          {
            exploit well_defined_preheader3; [eapply TRANSC | eapply TGT | eauto..].
            i. des1. do 2 eexists. eapply State.step_jmp; eauto.
          }
          {
            inv BLK_REL. eapply well_defined_preheader4 in TRANSC; eauto.
            destruct TRANSC as [TRANSC | TRANSC]. rewrite PTree.gempty in TRANSC. tryfalse.
            des1.
            do 2 eexists. eapply State.step_jmp; eauto.
          }
          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
        {
          (* be *)
          inv MATCH_CUR; ss.
          assert (EVAL_EQ: RegFile.eval_expr e0 R_t = RegFile.eval_expr e0 R_s).
          {
            eapply expr_eval_eq; eauto.
          }
          
          destruct BLK_REL as [BLK_REL | BLK_REL]; subst.
          {
            destruct BRANCH as [BRANCH | BRANCH].

            des1.
            exploit well_defined_preheader3; [eapply TRANSC | eapply BRANCH | eauto..].
            i. des1. do 2 eexists. eapply State.step_be; eauto.
            des1.
            exploit well_defined_preheader3; [eapply TRANSC | eapply BRANCH | eauto..].
            i. des1. do 2 eexists. eapply State.step_be; eauto.
          }
          {
            inv BLK_REL.

            destruct BRANCH as [BRANCH | BRANCH].
            {
              des1.
              eapply well_defined_preheader4 in TRANSC; eauto.
              destruct TRANSC as [TRANSC | TRANSC]. rewrite PTree.gempty in TRANSC. tryfalse.
              des1.
              do 2 eexists. eapply State.step_be; eauto.
            }
            {
              des1.
              exploit well_defined_preheader3; [eapply TRANSC | eapply BRANCH | eauto..].
              i. des1. do 2 eexists. eapply State.step_be; eauto.
            }

            destruct BRANCH as [BRANCH | BRANCH].
            {
              des1.
              exploit well_defined_preheader3; [eapply TRANSC | eapply BRANCH | eauto..].
              i. des1. do 2 eexists. eapply State.step_be; eauto.
            }
            {
              des1.
              eapply well_defined_preheader4 in TRANSC; eauto.
              destruct TRANSC as [TRANSC | TRANSC]. rewrite PTree.gempty in TRANSC. tryfalse.
              des1.
              do 2 eexists. eapply State.step_be; eauto.
            }

            destruct BRANCH as [BRANCH | BRANCH].
            {
              des1.
              eapply well_defined_preheader4 in PT1; eauto.
              destruct PT1 as [PT1 | PT1]. rewrite PTree.gempty in PT1. tryfalse.
              des1.
              do 2 eexists. eapply State.step_be; eauto.
            }
            {
              des1.
              eapply well_defined_preheader4 in PT2; eauto.
              destruct PT2 as [PT2 | PT2]. rewrite PTree.gempty in PT2. tryfalse.
              des1.
              do 2 eexists. eapply State.step_be; eauto.
            }
          }

          eapply well_defined_preheader3 in TRANSC; eauto. des1.
          eapply wdph_implies_progress; eauto.
        }
      }
      {
        unfold State.is_terminal in *. des1; subst.
        inv MATCH_THRD_LOCAL; ss. subst. inv MATCH_CUR; ss.
        destruct BLK_REL as [BLK_REL | BLK_REL]; subst; eauto.
        inv MATCH_CONT; eauto.
        inv BLK_REL.
        left.
        eapply well_defined_preheader3 in TRANSC; eauto. des1.
        eapply wdph_implies_progress; eauto.
      }
    }
    {
      destruct ABORT as [ABORT | ABORT].
      {
        do 5 des1; subst.

        destruct ABORT as [ABORT_READ | ABORT_WRITE].

        (* abort read *)
        inv MATCH_THRD_LOCAL.
        inv ABORT_READ; ss.
        {
          (* load abort *)
          inv MATCH_CUR; ss. eapply BBlock_cons' in BLK_REL. do 2 des1; subst.
          right. left.
          do 4 eexists. split.
          left. eapply State.step_load; eauto. eauto.
          clear - ABORT0 WDPH. destruct o; ss. des.
          rewrite WDPH0 in ABORT0. ss.
        }
        {
          (* update abort *)
          inv MATCH_CUR. eapply BBlock_cons' in BLK_REL. do 2 des1; subst.
          right. left.
          assert (EVAL_REGS: RegFile.eval_expr er R_t = RegFile.eval_expr er R_s).
          {
            eapply expr_eval_eq; eauto.
            ii. eapply ORIGN_REGS; eauto. eapply SUBSET_REG; eauto. s.
            eapply RegSet.union_spec. left.
            eapply RegSet.add_spec. right.
            eapply RegSet.union_spec; eauto.
          }
          do 4 eexists. split.
          left. eapply State.step_cas_flip; eauto. s.
          rewrite <- EVAL_REGS; eauto.
          eauto.
          inv WDPH; ss.
        }

        (* abort write *)
        inv MATCH_THRD_LOCAL.
        inv ABORT_WRITE; ss. inv MATCH_CUR; ss.
        eapply BBlock_cons' in BLK_REL; eauto. do 2 des1. subst.
        right. left.
        do 4 eexists.
        split. right. eapply State.step_store; eauto.
        eauto.
      }
      {
        do 7 des1; subst. inv ABORT.
        inv MATCH_THRD_LOCAL. inv MATCH_CUR.
        eapply BBlock_cons' in BLK_REL; eauto. do 2 des1; subst.
        right. right.
        do 7 eexists.
        eapply State.step_cas_same; eauto. eauto.
        inv WDPH.
      }
    }
  }
  Unshelve. exact Int.zero.
  Unshelve. exact Int.zero.
Qed.
