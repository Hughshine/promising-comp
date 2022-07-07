Require Import sflib.   
Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.
Require Import Coqlib.
Require Import Language. 

Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import NPThread.
Require Import Configuration.
Require Import MsgMapping.
Require Import DelaySet.
Require Import NPConfiguration.
Require Import ww_RF.

Require Import LibTactics.
Require Import Reordering.
Require Import np_to_ps_thread.
Require Import ps_to_np_thread.

Lemma not_abort_implies_thread_safe
  ths ctid sc mem lang st lc lo
  (SAFE: ~ (exists npc, rtc (NPConfiguration.all_step lo)
                       (NPConfiguration.mk (Configuration.mk ths ctid sc mem) true) npc /\
                   Configuration.is_abort (NPConfiguration.cfg npc) lo))
  (TH: IdentMap.find ctid ths = Some (existT _ lang st, lc)):
  (~ exists e, rtc (@Thread.all_step lang lo)
              (Thread.mk lang st lc sc mem) e /\ Thread.is_abort e lo).
Proof.
  ii. des.
  eapply rtc_rtcn in H. des.
  eapply Thread_all_steps_to_out_trans in H; eauto.
  des.
  eapply rtc_rtcn in H. des. destruct e0.
  eapply multi_out_trans_to_np_configuration_steps in H; eauto.
  contradiction SAFE.
  eexists.
  split.
  eapply H. ss.
  econs; ss.
  do 3 eexists.
  split.
  rewrite IdentMap.gss. eauto.
  split. eapply H1. eauto.
Qed.

Lemma Memory_promise_not_prm_msg_prsv
      prom mem loc from to msg prom' mem' kind
      loc0 to0 from0 val0 released0
      (PROMISE: Memory.promise prom mem loc from to msg prom' mem' kind)
      (MEM_GET: Memory.get loc0 to0 mem' = Some (from0, Message.concrete val0 released0))
      (PROM_GET: Memory.get loc0 to0 prom' = None):
  Memory.get loc0 to0 mem = Some (from0, Message.concrete val0 released0) /\
  Memory.get loc0 to0 prom = None.
Proof.
  inv PROMISE; ss.
  {
    (* promise add *)
    erewrite Memory.add_o in PROM_GET; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.add_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.add_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
  }
  {
    (* promise split *)
    des; subst; ss.
    erewrite Memory.split_o in PROM_GET; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.split_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.split_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.split_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
  }
  {
    (* promise lower *)
    des; subst.
    erewrite Memory.lower_o in PROM_GET; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.lower_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
  }
  {
    (* promise cancel *)
    erewrite Memory.remove_o in MEM_GET; eauto.
    des_ifH MEM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o in PROM_GET; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
    erewrite Memory.remove_o in PROM_GET; eauto.
    des_ifH PROM_GET; ss; des; subst; ss; eauto.
  }
Qed.

Lemma Memory_promise_not_prm_msg_stable
      prom mem loc from to msg prom' mem' kind
      loc0 to0 from0 val0 released0
      (PROMISE: Memory.promise prom mem loc from to msg prom' mem' kind)
      (MEM_GET: Memory.get loc0 to0 mem = Some (from0, Message.concrete val0 released0))
      (PROM_GET: Memory.get loc0 to0 prom = None):
  Memory.get loc0 to0 mem' = Some (from0, Message.concrete val0 released0) /\
  Memory.get loc0 to0 prom' = None.
Proof.
  inv PROMISE; ss.
  {
    (* promise add *)
    exploit Memory.add_get1; eauto. ii.
    split; eauto.
    erewrite Memory.add_o; eauto.
    des_if; ss; eauto. des; subst.
    exploit Memory.add_get0; eauto. ii; des.
    rewrite MEM_GET in GET. ss.
  }
  {
    (* promise split *)
    des; subst.
    split.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss.
    exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
    rewrite MEM_GET in GET. ss.
    des_if; ss; des; subst; ss.
    des_if; ss; des; subst; ss.
    exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
    rewrite PROM_GET in GET0. ss.
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss.
    exploit Memory.split_get0; [eapply MEM | eauto..]. ii; des.
    rewrite MEM_GET in GET. ss.
    des_if; ss; des; subst; ss.
    des_if; ss; des; subst; ss.
    exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
    rewrite PROM_GET in GET0. ss.
  }
  {
    (* promise lower *)
    des; subst.
    split.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
    rewrite PROM_GET in GET. ss.
    erewrite Memory.lower_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
    rewrite PROM_GET in GET. ss.
  }
  {
    (* promise cancel *)
    split.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    exploit Memory.remove_get0; eauto. ii; des.
    rewrite PROM_GET in GET. ss.
    erewrite Memory.remove_o; eauto.
    des_if; ss; des; subst; ss; eauto.
  }
Qed.

Lemma race_message_in_starting_mem':
  forall n lang st lc sc mem st' lc' sc' mem' lo loc to from val released
    (STEPS: rtcn (@Thread.all_step lang lo) n
                 (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (MSG: Memory.get loc to mem' = Some (from, Message.concrete val released))
    (NOT_PROM: Memory.get loc to (Local.promises lc') = None)
    (RACE: Time.lt (View.rlx (TView.cur (Local.tview lc')) loc) to)
    (LOCAL_WF: Local.wf lc mem)
    (SC_CLOSED: Memory.closed_timemap sc mem)
    (CLOSED_MEM: Memory.closed mem),
    Memory.get loc to mem = Some (from, Message.concrete val released) /\
    Memory.get loc to (Local.promises lc) = None /\
    Time.lt (View.rlx (TView.cur (Local.tview lc)) loc) to.
Proof.
  induction n; ii.
  - inv STEPS. eauto.
  - inv STEPS. destruct a2.
    inv A12. inv USTEP.
    exploit Thread.step_future; eauto; ss. ii; des.
    eapply IHn in A23; eauto. des.
    inv STEP.
    + inv STEP0. inv LOCAL. ss.
      exploit Memory_promise_not_prm_msg_prsv; [eapply PROMISE | eapply A23 | eapply A0 | eauto..].
      ii; des; eauto.
    + inv STEP0. inv LOCAL; ss; eauto.
      {
        (* read *)
        inv LOCAL0; ss; eauto.
        split; eauto. split; eauto.
        eapply Time_lt_join in A1. des.
        eapply Time_lt_join in A1. des. eauto.
      }
      {
        (* write *)
        inv LOCAL0; ss. inv WRITE; ss. 
        assert ((loc0, to0) <> (loc, to)).
        {
          ii. inv H.
          clear - A1.
          eapply Time_lt_join in A1. des.
          unfold TimeMap.singleton in A0; ss.
          rewrite Loc_add_eq in A0.
          auto_solve_time_rel.
        }
        erewrite Memory.remove_o in A0; eauto.
        des_ifH A0; ss. contradiction H; eauto. des; subst. eauto.
        exploit Memory_promise_not_prm_msg_prsv; [eapply PROMISE | eapply A23 | eapply A0 | eauto..].
        introv MEM_PROM_GET. destruct MEM_PROM_GET.
        split; eauto. split; eauto.
        eapply Time_lt_join in A1. des; eauto.
      }
      {
        (* update *)
        inv LOCAL1.
        inv READABLE.
        inv LOCAL2; ss. inv WRITABLE. inv WRITE.
        assert ((loc0, tsw) <> (loc, to)).
        {
          ii; subst. inv H.
          eapply Time_lt_join in A1. des.
          unfold TimeMap.singleton in A2.
          rewrite Loc_add_eq in A2.
          auto_solve_time_rel.
        }
        erewrite Memory.remove_o in A0; eauto.
        des_ifH A0; ss. contradiction H. des; subst; ss; eauto.
        exploit Memory_promise_not_prm_msg_prsv; [eapply PROMISE | eapply A23 | eapply A0 | eauto..].
        introv MEM_PROM_GET. destruct MEM_PROM_GET.
        split; eauto. split; eauto.
        eapply Time_lt_join in A1. destruct A1.
        eapply Time_lt_join in H2. destruct H2.
        eapply Time_lt_join in H2. destruct H2.
        eauto.
      }
      {
        (* fence *) 
        inv LOCAL0; ss.
        split; eauto. split; eauto. 
        destruct (Ordering.le Ordering.seqcst ordw) eqn:ORDER.
        {
          ss. 
          unfold TView.write_fence_sc in A1.
          unfold TView.read_fence_tview in A1; ss.
          des_ifH A1; ss; des; subst; ss.
          des_ifH A1; ss; des; subst; ss; eauto.
          eapply Time_lt_join in A1. des.
          inv LOCAL_WF. inv TVIEW_WF. inv CUR_ACQ.
          unfold TimeMap.le in RLX. specialize (RLX loc).
          cut (Time.lt (View.rlx (TView.cur (Local.tview lc)) loc) to).
          ii.
          inv CUR.
          unfold TimeMap.le in PLN_RLX. specialize (PLN_RLX loc).
          auto_solve_time_rel.
          auto_solve_time_rel.
          
          eapply Time_lt_join in A1; des; eauto.
        }
        des_ifH A1; ss; eauto.
        inv LOCAL_WF. inv TVIEW_WF. inv CUR_ACQ.
        unfold TimeMap.le in RLX.
        specialize (RLX loc).
        auto_solve_time_rel.
      }
      {
        (* out put *)
        inv LOCAL0; ss. split; eauto. split; eauto.
        assert (ORDER_LE: Ordering.le Ordering.seqcst Ordering.seqcst).
        eauto.
        rewrite ORDER_LE in A1. ss.
        unfold TView.write_fence_sc, TView.read_fence_tview in A1; ss.
        des_ifH A1; ss.
        eapply Time_lt_join in A1. des.
        des_ifH A2; ss; eauto.
        inv LOCAL_WF. inv TVIEW_WF. inv CUR_ACQ.
        unfold TimeMap.le in RLX. 
        specialize (RLX loc).
        cut (Time.lt (View.rlx (TView.acq (Local.tview lc)) loc) to). ii.
        auto_solve_time_rel. eauto.
      }
Qed.

Lemma race_message_in_starting_mem
    lang st lc sc mem st' lc' sc' mem' lo loc to from val released
    (STEPS: rtc (@Thread.all_step lang lo)
                (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (MSG: Memory.get loc to mem' = Some (from, Message.concrete val released))
    (NOT_PROM: Memory.get loc to (Local.promises lc') = None)
    (RACE: Time.lt (View.rlx (TView.cur (Local.tview lc')) loc) to)
    (LOCAL_WF: Local.wf lc mem)
    (SC_CLOSED: Memory.closed_timemap sc mem)
    (CLOSED_MEM: Memory.closed mem):
    Memory.get loc to mem = Some (from, Message.concrete val released) /\
    Memory.get loc to (Local.promises lc) = None.
Proof.
  eapply rtc_rtcn in STEPS. des.
  eapply race_message_in_starting_mem' in STEPS; eauto.
  des; eauto.
Qed.

Lemma race_message_stable':
  forall n lang st lc sc mem st' lc' sc' mem' lo loc from to val released
    (STEPS: rtcn (@Thread.all_step lang lo) n
                 (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
    (MSG: Memory.get loc to mem = Some (from, Message.concrete val released))
    (NOT_PROM: Memory.get loc to (Local.promises lc) = None),
    Memory.get loc to mem' = Some (from, Message.concrete val released) /\
    Memory.get loc to (Local.promises lc') = None.
Proof.
  induction n; ii.
  - inv STEPS. eauto.
  - inv STEPS.
    inv A12. inv USTEP. inv STEP; ss.
    + inv STEP0. inv LOCAL; ss.
      exploit Memory_promise_not_prm_msg_stable;
        [eapply PROMISE | eapply MSG | eapply NOT_PROM | eauto..].
      ii; des.
      eapply IHn in A23; eauto.
    + inv STEP0. inv LOCAL; eauto.
      {
        (* read *)
        inv LOCAL0; ss. eauto.
      }
      {
        (* write *)
        inv LOCAL0. inv WRITE.
        eapply Memory_promise_not_prm_msg_stable in PROMISE; eauto. des.
        assert ((loc, to) <> (loc0, to0)).
        {
          ii. inv H.
          exploit Memory.remove_get0; [eapply REMOVE | eauto..]. ii; des.
          rewrite PROMISE0 in GET. ss.
        }

        eapply IHn in A23; eauto.
        ss. erewrite Memory.remove_o; eauto.
        des_if; eauto.
      }
      {
        (* update *)
        inv LOCAL1. inv LOCAL2; ss. inv WRITE.
        eapply Memory_promise_not_prm_msg_stable with (loc0 := loc) (to0 := to) in PROMISE; eauto. des.
        assert ((loc, to) <> (loc0, tsw)).
        {
          ii. inv H.
          exploit Memory.remove_get0; [eapply REMOVE | eauto..]. ii; des.
          rewrite PROMISE0 in GET0. ss.
        }

        eapply IHn in A23; eauto.
        ss. erewrite Memory.remove_o; eauto.
        des_if; eauto.
      }
      {
        (* fence *)
        inv LOCAL0.
        eapply IHn in A23; eauto.
      }
      {
        (* out put *)
        eapply IHn in A23; eauto.
        inv LOCAL0; eauto.
      }
Qed.

Lemma race_message_stable
  lang st lc sc mem st' lc' sc' mem' lo loc from to val released
  (STEPS: rtc (@Thread.all_step lang lo) 
               (Thread.mk lang st lc sc mem) (Thread.mk lang st' lc' sc' mem'))
  (MSG: Memory.get loc to mem = Some (from, Message.concrete val released))
  (NOT_PROM: Memory.get loc to (Local.promises lc) = None):
  Memory.get loc to mem' = Some (from, Message.concrete val released) /\
  Memory.get loc to (Local.promises lc') = None.
Proof.
  eapply rtc_rtcn in STEPS. des.
  eapply race_message_stable'; eauto.
Qed.

Lemma na_steps_dset_race_or_not':
  forall n lo lang (e e': Thread.t lang) loc from to val R index (dset dset': @DelaySet index) i t 
    (NA_STEPS_DSET: rtcn (na_step_dset lo) n (e, dset) (e', dset'))
    (RACE_MSG: Memory.get loc to (Thread.memory e) = Some (from, Message.concrete val R))
    (NOT_PROM: Memory.get loc to (Local.promises (Thread.local e)) = None)
    (LT: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e))) loc) to)
    (IN_DSET: dset_get loc t dset = Some i),
  <<RACE: exists e0 e1 f' t' v,
    rtc (Thread.na_step lo) e e0 /\
    Thread.program_step (ThreadEvent.write loc f' t' v None Ordering.plain) lo e0 e1 /\
    Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e0))) loc) to /\
    rtc (Thread.na_step lo) e1 e' >> \/
  <<NOT_RACE: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e'))) loc) to /\
              dset_get loc t dset' = Some i>>.
Proof.
  induction n; ii.
  - inv NA_STEPS_DSET. eauto.
  - inv NA_STEPS_DSET. destruct a2. 
    renames t0 to e0, d to dset0.
    inv A12.
    + (* silent step *)
      eapply IHn in A23; eauto.
      des.
      {
        left.
        exists e1 e2 f' t' v.
        split; eauto.
        eapply Relation_Operators.rt1n_trans. 2: eauto.
        eapply Thread.na_tau_step_intro; eauto.
      }
      {
        right; eauto.
      }

      inv STEP; ss. inv LOCAL; ss. eauto.
      inv STEP; ss. inv LOCAL; ss.
      inv STEP; ss. inv LOCAL; ss.
    + (* read step *)
      eapply IHn in A23; eauto.
      des.
      {
        left.
        exists e1 e2 f' t' v0.
        split; eauto.
        eapply Relation_Operators.rt1n_trans. 2: eauto.
        eapply Thread.na_plain_read_step_intro; eauto.
      }
      {
        right.
        split; eauto.
      }

      inv STEP; ss. inv LOCAL; ss. eauto.
      inv STEP; ss. inv LOCAL; ss. inv LOCAL0; ss.
      erewrite <- RLX; eauto.
    + (* write step *)
      destruct (Loc.eq_dec loc loc0); subst.
      {
        (* race in the current step *)
        left.
        exists e e0 from0 to0 v.
        assert (R0 = None).
        {
          inv STEP; ss. inv LOCAL; ss. inv LOCAL0; ss.
        }
        subst R0.
        split; eauto.
        split; eauto.
        split; eauto.
        eapply na_steps_dset_to_Thread_na_steps' in A23. eauto.
      }
      {
        (* race not in the current step *)  
        assert (DSET0: dset_get loc t dset0 = Some i).
        {
          clear - DSET_REMOVE IN_DSET n0. des; subst; eauto.
          unfold dset_get, dset_remove in *; ss. des_if; subst; ss.
        } 
        clear DSET_REMOVE. destruct e, e0; ss. 
        exploit race_message_stable; [ | eapply RACE_MSG | eapply NOT_PROM | eauto..].
        {      
          eapply Relation_Operators.rt1n_trans. 2: eauto.
          econs. econs. eapply Thread.step_program. eauto.
        }
        ii; des.
        eapply IHn with (loc := loc) (to := to) (i := i) in A23; eauto.

        des; ss.
        {
          left.
          exists e0 e1 f' t' v0.
          split; eauto.
          eapply Relation_Operators.rt1n_trans. 2: eauto.
          eapply Thread.na_plain_write_step_intro; eauto.
        }
        {
          right. eauto.
        }

        ss.
        inv STEP; ss. inv LOCAL; ss. inv LOCAL0; ss.
        unfold TimeMap.join; ss.
        unfold TimeMap.singleton.
        rewrite Loc_add_neq; eauto.
        unfold LocFun.init; ss.
        rewrite Time_join_bot; eauto.
      }
Qed.

Lemma na_steps_dset_race_or_not
      lo lang (e e': Thread.t lang) loc from to val R index (dset dset': @DelaySet index) i t
      (NA_STEPS_DSET: rtc (na_step_dset lo) (e, dset) (e', dset'))
      (RACE_MSG: Memory.get loc to (Thread.memory e) = Some (from, Message.concrete val R))
      (NOT_PROM: Memory.get loc to (Local.promises (Thread.local e)) = None)
      (LT: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e))) loc) to)
      (IN_DSET: dset_get loc t dset = Some i):
  <<RACE: exists e0 e1 f' t' v,
    rtc (Thread.na_step lo) e e0 /\
    Thread.program_step (ThreadEvent.write loc f' t' v None Ordering.plain) lo e0 e1 /\
    Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e0))) loc) to /\
    rtc (Thread.na_step lo) e1 e' >> \/
  <<NOT_RACE: Time.lt (View.rlx (TView.cur (Local.tview (Thread.local e'))) loc) to /\
              dset_get loc t dset' = Some i>>.
Proof.
  eapply rtc_rtcn in NA_STEPS_DSET. des.
  eapply na_steps_dset_race_or_not'; eauto.
Qed.
