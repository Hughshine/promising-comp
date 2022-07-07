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

Require Import WFConfig.
Require Import CompAuxDef.
Require Import MemoryProps.
Require Import promiseCertifiedAux.
Require Import Mem_at_eq_lemmas.
Require Import PromiseInjectionWeak.

(** * Well-formed state lemmas *)
Lemma concrete_incr_closed_tm_prsv
      tm mem mem'
      (CONCRETE_INCR: forall loc to from val R,
          Memory.get loc to mem = Some (from, Message.concrete val R) ->
          exists from' R', Memory.get loc to mem' = Some (from', Message.concrete val R'))
      (CLOSED_VIEW: Memory.closed_timemap tm mem):
  Memory.closed_timemap tm mem'.
Proof.
  unfold Memory.closed_timemap in *.
  ii. specialize (CLOSED_VIEW loc). des.
  eapply CONCRETE_INCR in CLOSED_VIEW. des.
  do 3 eexists. eauto.
Qed.

Lemma concrete_incr_closed_view_prsv
      view mem mem'
      (CONCRETE_INCR: forall loc to from val R,
          Memory.get loc to mem = Some (from, Message.concrete val R) ->
          exists from' R', Memory.get loc to mem' = Some (from', Message.concrete val R'))
      (CLOSED_VIEW: Memory.closed_view view mem):
  Memory.closed_view view mem'.
Proof.
  inv CLOSED_VIEW.
  econs; eauto.
  eapply concrete_incr_closed_tm_prsv; eauto.
  eapply concrete_incr_closed_tm_prsv; eauto.
Qed.

Lemma concrete_incr_local_wf_prsv
      mem mem' lc
      (CONCRETE_INCR: forall loc to from val R,
          Memory.get loc to mem = Some (from, Message.concrete val R) ->
          exists from' R', Memory.get loc to mem' = Some (from', Message.concrete val R'))
      (PRM_LESS: Memory.le (Local.promises lc) mem')
      (LOCAL_WF: Local.wf lc mem):
  Local.wf lc mem'.
Proof.
  inv LOCAL_WF.
  econs; eauto.
  inv TVIEW_CLOSED.
  econs; eauto.
  ii.
  eapply concrete_incr_closed_view_prsv; eauto.
  eapply concrete_incr_closed_view_prsv; eauto.
  eapply concrete_incr_closed_view_prsv; eauto.
Qed.

(** * Step lemmas *)
Lemma Thread_na_step_to_na_step_dset
      lang lo (e1 e2: Thread.t lang) index
      (NA_STEP: Thread.na_step lo e1 e2):
  na_step_dset lo (e1, @dset_init index) (e2, @dset_init index).
Proof.
  inv NA_STEP.
  eapply na_steps_dset_read; eauto.
  ii. rewrite dset_gempty in H. ss.
  eapply na_steps_dset_write; eauto.
  econs; eauto.
Qed.

Lemma Thread_na_steps_to_na_steps_dset
      lang lo (e1 e2: Thread.t lang) index
      (NA_STEPS: rtc (Thread.na_step lo) e1 e2):
  rtc (na_step_dset lo) (e1, @dset_init index) (e2, @dset_init index).
Proof.
  induction NA_STEPS; ii; eauto.
  econs; eauto.
  eapply Thread_na_step_to_na_step_dset; eauto.
Qed.

Lemma injection_read
      inj lo
      tview_tgt prm_tgt mem_tgt loc to v R or tview_tgt' prm_tgt'
      tview_src prm_src mem_src
      (LOCAL_READ: Local.read_step (Local.mk tview_tgt prm_tgt) mem_tgt loc to v R or
                                   (Local.mk tview_tgt' prm_tgt') lo)
      (MSG_INJ: MsgInj inj mem_tgt mem_src)
      (INJ_PLN: inj loc (View.pln (TView.cur tview_tgt) loc) = Some (View.pln (TView.cur tview_src) loc))
      (INJ_RLX: inj loc (View.rlx (TView.cur tview_tgt) loc) = Some (View.rlx (TView.cur tview_src) loc))
      (MEM_CLOSED: Memory.closed mem_tgt):
  exists tview_src' to' R',
    <<LOCAL_READ_SRC: Local.read_step (Local.mk tview_src prm_src) mem_src loc to' v R' or
                                      (Local.mk tview_src' prm_src) lo>> /\
    <<INJ_PLN': inj loc (View.pln (TView.cur tview_tgt') loc) = Some (View.pln (TView.cur tview_src') loc)>> /\
    <<INJ_RLX': inj loc (View.rlx (TView.cur tview_tgt') loc) = Some (View.rlx (TView.cur tview_src') loc)>> /\
    <<INJ_TO: inj loc to = Some to'>> /\
    <<VIEW_INJ: opt_ViewInj inj R R'>> /\ 
    <<CLOSED_VIEW: Memory.closed_opt_view R mem_tgt>>.
Proof.
  inv LOCAL_READ. inv LC2. inv MSG_INJ.
  exploit SOUND; eauto. ii; des.
  do 3 eexists.
  split. econs; eauto. ss. inv READABLE. econs; eauto.
  eapply monotonic_inj_implies_le_prsv; eauto.
  ii.
  exploit RLX; eauto. ii.
  eapply monotonic_inj_implies_le_prsv; eauto.
  
  ss. splits; eauto.
  {
    destruct (Ordering.le Ordering.acqrel or) eqn:ORD_ACQREL.
    {
      unfold View.singleton_ur_if. unfold TimeMap.join; ss.
      destruct (Ordering.le Ordering.relaxed or) eqn:ORD_RELAX; ss.
      
      unfold TimeMap.singleton; ss. do 2 (rewrite Loc_add_eq).
      exploit wf_msginj_implies_closed_view; [ | eapply MEM_CLOSED | eapply GET | eauto..].
      econs; eauto. ii; des; subst.
      {
        ss. destruct R'; ss. unfold TimeMap.bot. do 2 (rewrite Time_join_bot).
        eapply inj_join_comp; eauto.
      }
      {
        destruct R'; ss.
        eapply inj_join_comp; eauto.
        eapply inj_join_comp; eauto.
        clear - x2 x0. inv x2. unfold closed_TMapInj in H.
        specialize (H loc). des. unfold ViewInj in x0. destruct view, t; ss. des.
        unfold TMapInj in x0.
        exploit x0; eauto. ii; subst. eauto.
      }

      unfold TimeMap.bot. do 2 (rewrite Time_join_bot).
      exploit wf_msginj_implies_closed_view; [ | eapply MEM_CLOSED | eapply GET | eauto..].
      econs; eauto. ii; des; subst.
      {
        destruct R'; ss. unfold TimeMap.bot; ss.
        do 2 (rewrite Time_join_bot). eauto.
      }
      {
        destruct R'; ss.
        eapply inj_join_comp; eauto.
        clear - x2 x0. inv x2. unfold closed_TMapInj in H.
        specialize (H loc). des. unfold ViewInj in x0. destruct view, t; ss. des.
        unfold TMapInj in x0.
        exploit x0; eauto. ii; subst. eauto.
      }
    }
    {
      unfold View.singleton_ur_if. unfold TimeMap.join; ss.
      destruct (Ordering.le Ordering.relaxed or) eqn:ORD_RELAX; ss.

      unfold TimeMap.singleton; ss. do 2 (rewrite Loc_add_eq).
      unfold TimeMap.bot; ss. do 2 (rewrite Time_join_bot).
      eapply inj_join_comp; eauto.

      unfold TimeMap.bot; ss. do 4 (rewrite Time_join_bot). eauto.
    }
  }
  {
    destruct (Ordering.le Ordering.acqrel or) eqn:ORD_ACQREL.
    {
      unfold View.singleton_ur_if. unfold TimeMap.join; ss.
      destruct (Ordering.le Ordering.relaxed or) eqn:ORD_RELAX; ss.
      
      unfold TimeMap.singleton; ss. do 2 (rewrite Loc_add_eq).
      exploit wf_msginj_implies_closed_view; [ | eapply MEM_CLOSED | eapply GET | eauto..].
      econs; eauto. ii; des; subst.
      {
        ss. destruct R'; ss. unfold TimeMap.bot. do 2 (rewrite Time_join_bot).
        eapply inj_join_comp; eauto. 
      }
      {
        destruct R'; ss.
        eapply inj_join_comp; eauto.
        eapply inj_join_comp; eauto.
        clear - x2 x0. inv x2. unfold closed_TMapInj in H0.
        specialize (H0 loc). des. unfold ViewInj in x0. destruct view, t; ss. des.
        unfold TMapInj in x1.
        exploit x1; eauto. ii; subst. eauto.
      }

      unfold TimeMap.singleton; ss. do 2 (rewrite Loc_add_eq).
      exploit wf_msginj_implies_closed_view; [ | eapply MEM_CLOSED | eapply GET | eauto..].
      econs; eauto. ii; des; subst.
      {
        destruct R'; ss. unfold TimeMap.bot; ss.
        do 2 (rewrite Time_join_bot).
        eapply inj_join_comp; eauto. 
      }
      {
        destruct R'; ss.
        eapply inj_join_comp; eauto.
        eapply inj_join_comp; eauto.
        clear - x2 x0. inv x2. unfold closed_TMapInj in H0.
        specialize (H0 loc). des. unfold ViewInj in x0. destruct view, t; ss. des.
        unfold TMapInj in x1.
        exploit x1; eauto. ii; subst. eauto.
      }
    }
    {
      unfold View.singleton_ur_if. unfold TimeMap.join; ss.
      destruct (Ordering.le Ordering.relaxed or) eqn:ORD_RELAX; ss.

      unfold TimeMap.singleton; ss. do 2 (rewrite Loc_add_eq).
      unfold TimeMap.bot; ss. do 2 (rewrite Time_join_bot).
      eapply inj_join_comp; eauto.

      unfold TimeMap.bot; ss. do 2 (rewrite Time_join_bot).
      unfold TimeMap.singleton; ss. do 2 (rewrite Loc_add_eq).
      eapply inj_join_comp; eauto.
    }
  }
  {
    clear - GET MEM_CLOSED.
    eapply closed_mem_implies_closed_msg; eauto.
  }
Qed.
