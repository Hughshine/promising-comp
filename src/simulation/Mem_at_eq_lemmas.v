Require Import sflib.  

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.
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

Require Import LocalSim.
Require Import MsgMapping.
Require Import MemoryProps.
Require Import DelaySet.
Require Import ConsistentStableEnv.

Lemma Memory_add_disj_loc_stable
      mem1 mem2 loc from to msg loc0
      (ADD: Memory.add mem1 loc from to msg mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  inv ADD. rewrite Loc_add_neq; eauto.
Qed.

Lemma Memory_split_disj_loc_stable
      mem1 mem2 loc from to ts msg1 msg2 loc0
      (SPLIT: Memory.split mem1 loc from to ts msg1 msg2 mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  inv SPLIT. rewrite Loc_add_neq; eauto.
Qed.

Lemma Memory_remove_disj_loc_stable
      mem1 mem2 loc from to msg loc0
      (REMOVE: Memory.remove mem1 loc from to msg mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  inv REMOVE. rewrite Loc_add_neq; eauto.
Qed.

Lemma Memory_lower_disj_loc_stable
      mem1 mem2 loc from to msg1 msg2 loc0
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
      (DISJ_LOC: loc <> loc0):
  mem1 loc0 = mem2 loc0.
Proof.
  eapply Cell.ext. ii.
  inv LOWER. rewrite Loc_add_neq; eauto.
Qed.  
  
Lemma Memory_write_disj_loc_stable
      promises1 mem1 loc from to val released promises2 mem2 kind loc0
      (WRITE: Memory.write promises1 mem1 loc from to val released promises2 mem2 kind)
      (DISJ_LOC: loc <> loc0):
  promises1 loc0 = promises2 loc0 /\ mem1 loc0 = mem2 loc0. 
Proof.
  inv WRITE. inv PROMISE.
  - (* add *)
    split.
    {
      exploit Memory_remove_disj_loc_stable; eauto. ii.
      exploit Memory_add_disj_loc_stable; [eapply PROMISES | eauto..]. ii.
      rewrite x1. rewrite <- x0. eauto.
    }
    {
      eapply Memory_add_disj_loc_stable; eauto.
    }
  - (* split *)
    des. subst. inv RESERVE.
    split.
    {
      exploit Memory_remove_disj_loc_stable; eauto. ii.
      exploit Memory_split_disj_loc_stable; [eapply PROMISES | eauto..]. ii.
      rewrite x1. rewrite <- x0. eauto.
    }
    {
      eapply Memory_split_disj_loc_stable; eauto.
    }
  - (* lower *)
    des. subst.
    split.
    {
      exploit Memory_remove_disj_loc_stable; eauto. ii.
      exploit Memory_lower_disj_loc_stable; [eapply PROMISES | eauto..]. ii.
      rewrite x1. rewrite <- x0. eauto.
    }
    {
      eapply Memory_lower_disj_loc_stable; eauto.
    }
  - (* cancel *)
    des. subst. ss.
Qed.

Lemma Mem_at_eq_na_step_prsv
      lang lo e1 e2 m
      (NA_STEP: @Thread.na_step lang lo e1 e2)
      (ATOMIC_COVER: Mem_at_eq lo (Thread.memory e1) m):
    Mem_at_eq lo (Thread.memory e2) m.
Proof.
  unfold Mem_at_eq in *. ii.
  exploit ATOMIC_COVER; eauto. ii.
  inv NA_STEP.
  - (* na read *)
    inv STEP; ss. inv LOCAL; ss.
  - (* na write *)
    unfold Mem_approxEq_loc in *. des.
    inv STEP; ss. inv LOCAL; ss.
    inv LOCAL0.
    assert(loc0 <> loc).
    {
      ii; subst.
      clear - H LO. rewrite H in LO. ss.
      des; ss.
    }
    unfold Memory.get in *.
    exploit Memory_write_disj_loc_stable; eauto. ii. des.
    rewrite <- x1. eauto.
  - (* na silent *)
    inv STEP; ss. inv LOCAL; ss.
Qed.

Lemma Mem_at_eq_na_steps_prsv':
  forall n lang lo e1 e2 m
    (NA_STEPS: rtcn (@Thread.na_step lang lo) n e1 e2)
    (ATOMIC_COVER: Mem_at_eq lo (Thread.memory e1) m),
    Mem_at_eq lo (Thread.memory e2) m.
Proof.
  induction n; ii.
  - inv NA_STEPS. eauto.
  - inv NA_STEPS. eapply IHn in A23; eauto.
    eapply Mem_at_eq_na_step_prsv; eauto.
Qed.

Lemma Mem_at_eq_na_steps_prsv
      lang lo e1 e2 m
      (NA_STEPS: rtc (@Thread.na_step lang lo) e1 e2)
      (ATOMIC_COVER: Mem_at_eq lo (Thread.memory e1) m):
  Mem_at_eq lo (Thread.memory e2) m.
Proof.
  eapply rtc_rtcn in NA_STEPS. des.
  eapply Mem_at_eq_na_steps_prsv'; eauto.
Qed.

Lemma Mem_approxEq_loc_reflexive
      mem1 mem2 loc
      (MEM_APPROX_EQ: Mem_approxEq_loc loc mem1 mem2):
  Mem_approxEq_loc loc mem2 mem1.
Proof.
  unfold Mem_approxEq_loc in *.
  des.
  split; ii.
  specialize (MEM_APPROX_EQ f t val). des.
  split. eauto. eauto.
  specialize (MEM_APPROX_EQ0 f t).
  des.
  split; eauto.
Qed.
  
Lemma Mem_at_eq_reflexive
      mem1 mem2 lo
      (ATOMIC_COVER: Mem_at_eq lo mem1 mem2):
  Mem_at_eq lo mem2 mem1.
Proof.
  unfold Mem_at_eq in *; ii.
  exploit ATOMIC_COVER; eauto.
  ii.
  eapply Mem_approxEq_loc_reflexive in x; eauto.
Qed.

Lemma Mem_at_eq_init
      lo:
  Mem_at_eq lo Memory.init Memory.init.
Proof.
  unfold Mem_at_eq. ii.
  unfold Memory.init.
  unfold Mem_approxEq_loc.
  unfold Memory.get.
  split.
  ii.
  split; ii; des.
  erewrite Cell.init_get in *.
  des_ifH H0; ss. inv H0.
  unfold Message.elt. eauto.
  erewrite Cell.init_get in *.
  des_ifH H0; ss. inv H0.
  unfold Message.elt. eauto.
  ii; split; ii.
  erewrite Cell.init_get in *.
  des_ifH H0; ss.
  erewrite Cell.init_get in *.
  des_ifH H0; ss.
Qed.

Lemma Mem_approxEq_loc_adjacent
      mem1 mem2 loc from f t to
      (ADJ: Memory.adjacent loc from f t to mem1)
      (MEM_APPROX_EQ: Mem_approxEq_loc loc mem1 mem2):
  Memory.adjacent loc from f t to mem2.
Proof.
  inv MEM_APPROX_EQ.
  inv ADJ.
  destruct m1.
  {
    dup H. specialize (H1 from f val).
    des. clear H2. exploit H1; eauto. ii; des. clear H1.
    destruct m2.
    {
      dup H. specialize (H1 t to val0).
      des. clear H2. exploit H1; eauto. ii; des. clear H1.
      econs; eauto.
      ii.
      destruct(Memory.get loc ts mem2) eqn: GET2'; eauto.
      destruct p. exploit EMPTY; eauto; ii.
      destruct t1.
      specialize (H t0 ts val1). des.
      exploit H1; eauto. ii; des. rewrite x1 in x2; ss.
      specialize (H0 t0 ts). des.
      eapply H1 in GET2'. rewrite x1 in GET2'; ss.
    }
    {
      dup H0. specialize (H1 t to).
      des. clear H2. exploit H1; eauto. ii; des. clear H1.
      econs; eauto.
      ii.
      destruct(Memory.get loc ts mem2) eqn: GET2'; eauto.
      destruct p. exploit EMPTY; eauto; ii.
      destruct t1.
      specialize (H t0 ts val0). des.
      exploit H1; eauto. ii; des. rewrite x1 in x2; ss.
      specialize (H0 t0 ts). des.
      eapply H1 in GET2'. rewrite x1 in GET2'; ss.
    }
  }
  {
    dup H0. specialize (H1 from f).
    des. clear H2. exploit H1; eauto. ii; des. clear H1.
    destruct m2.
    {
      dup H. specialize (H1 t to val).
      des. clear H2. exploit H1; eauto. ii; des. clear H1.
      econs; eauto.
      ii.
      destruct(Memory.get loc ts mem2) eqn: GET2'; eauto.
      destruct p. exploit EMPTY; eauto; ii.
      destruct t1.
      specialize (H t0 ts val0). des.
      exploit H1; eauto. ii; des. rewrite x1 in x2; ss.
      specialize (H0 t0 ts). des.
      eapply H1 in GET2'. rewrite x1 in GET2'; ss.
    }
    {
      dup H0. specialize (H1 t to).
      des. clear H2. exploit H1; eauto. ii; des. clear H1.
      econs; eauto.
      ii.
      destruct(Memory.get loc ts mem2) eqn: GET2'; eauto.
      destruct p. exploit EMPTY; eauto; ii.
      destruct t1.
      specialize (H t0 ts val). des.
      exploit H1; eauto. ii; des. rewrite x1 in x2; ss.
      specialize (H0 t0 ts). des.
      eapply H1 in GET2'. rewrite x1 in GET2'; ss.
    }
  }
Qed.

Lemma Mem_approxEq_loc_Mem_max_ts
      mem1 mem2 loc
      (MEM_APPROX_EQ: Mem_approxEq_loc loc mem1 mem2)
      (MEM_CLOSED1: Memory.closed mem1)
      (MEM_CLOSED2: Memory.closed mem2):
  Memory.max_ts loc mem1 = Memory.max_ts loc mem2.
Proof.
  unfold Mem_approxEq_loc in *. des.
  destruct (Time.le_lt_dec (Memory.max_ts loc mem1) (Memory.max_ts loc mem2)).
  {
    eapply Time.le_lteq in l; des; eauto.
    inv MEM_CLOSED1. clear CLOSED.
    inv MEM_CLOSED2. clear CLOSED.
    unfold Memory.inhabited in *.
    specialize (INHABITED loc). specialize (INHABITED0 loc).
    exploit Memory.max_ts_spec; [eapply INHABITED | eauto..]. ii; des.
    exploit Memory.max_ts_spec; [eapply INHABITED0 | eauto..]. ii; des.
    destruct msg0.
    {
      specialize (MEM_APPROX_EQ from0 (Memory.max_ts loc mem2) val). des.
      exploit MEM_APPROX_EQ1; eauto. ii; des.
      exploit Memory.max_ts_spec; [eapply x | eauto..]. ii; des.
      auto_solve_time_rel.
    }
    {
      specialize (MEM_APPROX_EQ0 from0 (Memory.max_ts loc mem2)). des.
      exploit MEM_APPROX_EQ1; eauto. ii; des.
      exploit Memory.max_ts_spec; [eapply x | eauto..]. ii; des.
      auto_solve_time_rel.
    }
  }
  {
    inv MEM_CLOSED1. clear CLOSED.
    inv MEM_CLOSED2. clear CLOSED.
    unfold Memory.inhabited in *.
    specialize (INHABITED loc). specialize (INHABITED0 loc).
    exploit Memory.max_ts_spec; [eapply INHABITED | eauto..]. ii; des.
    exploit Memory.max_ts_spec; [eapply INHABITED0 | eauto..]. ii; des.
    destruct msg.
    {
      specialize (MEM_APPROX_EQ from (Memory.max_ts loc mem1) val). des.
      exploit MEM_APPROX_EQ; eauto. ii; des.
      exploit Memory.max_ts_spec; [eapply x | eauto..]. ii; des.
      auto_solve_time_rel.
    }
    {
      specialize (MEM_APPROX_EQ0 from (Memory.max_ts loc mem1)). des.
      exploit MEM_APPROX_EQ0; eauto. ii; des.
      exploit Memory.max_ts_spec; [eapply x | eauto..]. ii; des.
      auto_solve_time_rel.
    }
  }
Qed.
  
Lemma Mem_at_eq_cap
      lo mem1 mem2 mem_c1 mem_c2
      (MEM_AT_EQ: Mem_at_eq lo mem1 mem2)
      (CAP1: Memory.cap mem1 mem_c1)
      (CAP2: Memory.cap mem2 mem_c2)
      (CLOSED_MEM1: Memory.closed mem1)
      (CLOSED_MEM2: Memory.closed mem2):
  Mem_at_eq lo mem_c1 mem_c2.
Proof.
  unfold Mem_at_eq in *. ii.
  exploit MEM_AT_EQ; eauto. ii.
  clear - CAP1 CAP2 x CLOSED_MEM1 CLOSED_MEM2.
  unfold Mem_approxEq_loc in *.
  des.
  split; ii.
  {
    split; ii; des.
    {
      exploit Memory.cap_inv; [eapply CLOSED_MEM1| eapply CAP1 | eapply H | eauto..]; eauto.
      ii; des; ss.
      specialize (x f t val). des.
      exploit x; eauto. ii; des.
      inv CAP2.
      eapply SOUND in x4; eauto.
    }
    {
      exploit Memory.cap_inv; [eapply CLOSED_MEM2| eapply CAP2 | eapply H | eauto..]; eauto.
      ii; des; ss.
      specialize (x f t val). des.
      exploit x1; eauto. ii; des.
      inv CAP1.
      eapply SOUND in x4; eauto.
    }
  }
  { 
    split; ii. 
    { 
      exploit Memory.cap_inv; [eapply CLOSED_MEM1| eapply CAP1 | eapply H | eauto..]; eauto.
      ii; des; ss.
      {
        dup x0. specialize (x1 f t). des.
        exploit x1; eauto. ii.
        inv CAP2; eauto.
      }
      {
        destruct(Memory.get loc t mem_c2) eqn: GET_MEM2_CAP; eauto.
        destruct p. destruct t1; eauto.
        exploit Memory.cap_inv; [eapply CLOSED_MEM2 | eapply CAP2 | eapply GET_MEM2_CAP | eauto..]; eauto.
        ii; des; subst; ss.
        specialize (x t0 t val). des.
        exploit x5; eauto. ii; des. rewrite x2 in x8; ss.
        exploit Memory.cap_inv; [eapply CLOSED_MEM2 | eapply CAP2 | eapply GET_MEM2_CAP | eauto..]; eauto.
        ii; des; subst; ss.
        specialize (x0 t0 t). des.
        eapply x5 in x6. rewrite x2 in x6. ss.
        assert (Time.le f t).
        {
          exploit Memory.get_ts; [eapply H | eauto..]. ii; des; subst.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        assert (Time.le t0 t).
        {
          exploit Memory.get_ts; [eapply H | eauto..]. ii; des; subst.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        assert (t0 = f).
        {
          destruct (Time.le_lt_dec t0 f).
          eapply Time.le_lteq in l. des; subst; eauto.
          inv x1. inv x5.
          specialize (EMPTY0 f). exploit EMPTY0; eauto. ii.
          destruct m1.
          {
            specialize (x from1 f val). des.
            exploit x; eauto. ii; des. rewrite x1 in x10; ss.
          }
          {
            specialize (x0 from1 f). des.
            exploit x0; eauto. ii. rewrite x1 in x10. ss.
          }
          inv x1. inv x5.
          specialize (EMPTY t0). exploit EMPTY; eauto. ii.
          destruct m0.
          {
            specialize (x from0 t0 val). des.
            exploit x5; eauto. ii; des. rewrite x1 in x10; ss.
          }
          {
            specialize (x0 from0 t0). des.
            exploit x5; eauto. ii. rewrite x1 in x10; ss.
          }
        }
        subst; eauto.
        inv x1.
        assert (Time.le (Time.incr (Memory.max_ts loc mem2)) to2).
        {
          exploit Memory.get_ts; [eapply GET2 | eauto..]. ii; des; subst; eauto.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        destruct m2.
        {          
          specialize (x (Time.incr (Memory.max_ts loc mem2)) to2 val).
          des.
          exploit x; eauto. ii; des.
          eapply Memory.max_ts_spec in x7; eauto. des.
          clear - H0 MAX.
          cut (Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))).
          ii.
          cut (Time.lt to2 (Time.incr (Memory.max_ts loc mem2))).
          ii.
          clear - H0 H1. auto_solve_time_rel.
          auto_solve_time_rel.
          auto_solve_time_rel.
        }
        {
          specialize (x0 (Time.incr (Memory.max_ts loc mem2)) to2).
          des.
          exploit x0; eauto. ii; des.
          eapply Memory.max_ts_spec in x7; eauto. des.
          clear - H0 MAX.
          cut (Time.lt (Memory.max_ts loc mem2) (Time.incr (Memory.max_ts loc mem2))).
          ii.
          cut (Time.lt to2 (Time.incr (Memory.max_ts loc mem2))).
          ii.
          clear - H0 H1. auto_solve_time_rel.
          auto_solve_time_rel.
          auto_solve_time_rel.
        }

        exploit Mem_approxEq_loc_adjacent; eauto.
        instantiate (1 := mem2).
        unfold Mem_approxEq_loc; eauto. ii.
        inv CAP2.
        eapply MIDDLE in x6; eauto.
        rewrite GET_MEM2_CAP in x6; ss.
      }
      {
        subst. 
        exploit Mem_approxEq_loc_Mem_max_ts; [ | eapply CLOSED_MEM1 | eapply CLOSED_MEM2 | eauto..]; eauto.
        instantiate (1 := loc). unfold Mem_approxEq_loc; eauto.
        ii. rewrite x3.
        inv CAP2. eapply BACK; eauto.
      }
    }
    {
      exploit Memory.cap_inv; [eapply CLOSED_MEM2| eapply CAP2 | eapply H | eauto..]; eauto.
      ii; des; ss.
      {
        dup x0. specialize (x1 f t). des.
        exploit x1; eauto. ii.
        inv CAP1; eauto.
      }
      {
        destruct(Memory.get loc t mem_c1) eqn: GET_MEM1_CAP; eauto.
        destruct p. destruct t1; eauto.
        exploit Memory.cap_inv; [eapply CLOSED_MEM1 | eapply CAP1 | eapply GET_MEM1_CAP | eauto..]; eauto.
        ii; des; subst; ss.
        specialize (x t0 t val). des.
        exploit x; eauto. ii; des. rewrite x2 in x8; ss.
        exploit Memory.cap_inv; [eapply CLOSED_MEM1 | eapply CAP1 | eapply GET_MEM1_CAP | eauto..]; eauto.
        ii; des; subst; ss.
        specialize (x0 t0 t). des.
        eapply x0 in x6. rewrite x2 in x6. ss.
        assert (Time.le f t).
        {
          exploit Memory.get_ts; [eapply H | eauto..]. ii; des; subst.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        assert (Time.le t0 t).
        {
          exploit Memory.get_ts; [eapply H | eauto..]. ii; des; subst.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        assert (t0 = f).
        {
          destruct (Time.le_lt_dec t0 f).
          eapply Time.le_lteq in l. des; subst; eauto.
          inv x1. inv x5.
          specialize (EMPTY0 f). exploit EMPTY0; eauto. ii.
          destruct m1.
          {
            specialize (x from1 f val). des.
            exploit x5; eauto. ii; des. rewrite x1 in x10; ss.
          }
          {
            specialize (x0 from1 f). des.
            exploit x5; eauto. ii. rewrite x1 in x10. ss.
          }
          inv x1. inv x5.
          specialize (EMPTY t0). exploit EMPTY; eauto. ii.
          destruct m0.
          {
            specialize (x from0 t0 val). des.
            exploit x; eauto. ii; des. rewrite x1 in x10; ss.
          }
          {
            specialize (x0 from0 t0). des.
            exploit x0; eauto. ii. rewrite x1 in x10; ss.
          }
        }
        subst; eauto.
        inv x1.
        assert (Time.le (Time.incr (Memory.max_ts loc mem1)) to2).
        {
          exploit Memory.get_ts; [eapply GET2 | eauto..]. ii; des; subst; eauto.
          auto_solve_time_rel.
          eapply Time.le_lteq; eauto.
        }
        destruct m2.
        {           
          specialize (x (Time.incr (Memory.max_ts loc mem1)) to2 val).
          des.
          exploit x1; eauto. ii; des.
          eapply Memory.max_ts_spec in x7; eauto. des.
          clear - H0 MAX.
          cut (Time.lt (Memory.max_ts loc mem1) (Time.incr (Memory.max_ts loc mem1))).
          ii.
          cut (Time.lt to2 (Time.incr (Memory.max_ts loc mem1))).
          ii.
          clear - H0 H1. auto_solve_time_rel.
          auto_solve_time_rel.
          auto_solve_time_rel.
        }
        {
          specialize (x0 (Time.incr (Memory.max_ts loc mem1)) to2).
          des.
          exploit x1; eauto. ii; des.
          eapply Memory.max_ts_spec in x7; eauto. des.
          clear - H0 MAX.
          cut (Time.lt (Memory.max_ts loc mem1) (Time.incr (Memory.max_ts loc mem1))).
          ii.
          cut (Time.lt to2 (Time.incr (Memory.max_ts loc mem1))).
          ii.
          clear - H0 H1. auto_solve_time_rel.
          auto_solve_time_rel.
          auto_solve_time_rel.
        }

        exploit Mem_approxEq_loc_adjacent; eauto.
        instantiate (1 := mem1).
        eapply Mem_approxEq_loc_reflexive; eauto.
        unfold Mem_approxEq_loc; eauto. ii.
        inv CAP1.
        eapply MIDDLE in x6; eauto.
        rewrite GET_MEM1_CAP in x6; ss.
      }
      {
        subst. 
        exploit Mem_approxEq_loc_Mem_max_ts; [ | eapply CLOSED_MEM1 | eapply CLOSED_MEM2 | eauto..]; eauto.
        instantiate (1 := loc). unfold Mem_approxEq_loc; eauto.
        ii. rewrite <- x3.
        inv CAP1. eapply BACK; eauto.
      }
    }
  }
Qed.

Lemma memory_add_split_at_eq_prsv_contr
      loc from to lo
      mem1 mem1'
      mem2 msg2 mem2' ts
      val1 R1 val2 R2
      (MEM_AR_EQ: Mem_at_eq lo mem1 mem2)
      (ADD: Memory.add mem1 loc from to (Message.concrete val1 R1) mem1')
      (SPLIT: Memory.split mem2 loc from to ts msg2 (Message.concrete val2 R2) mem2')
      (MEM_AR_EQ': Mem_at_eq lo mem1' mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  False.
Proof.
  exploit Memory.split_get0; [eapply SPLIT | eauto..]. ii; des.
  exploit split_succeed_wf; [eapply SPLIT | eauto..]. ii; des. clear GET3.
  exploit Memory.add_get0; [eapply ADD | eauto..]. ii; des.
  exploit add_succeed_wf; [eapply ADD | eauto..]. ii; des.
  unfold Mem_at_eq in MEM_AR_EQ.
  exploit MEM_AR_EQ; eauto. ii.
  unfold Mem_approxEq_loc in x. des.
  specialize (x from ts val2). des.
  exploit x1; eauto. ii; des.
  eapply DISJOINT in x3.
  unfold Interval.disjoint in x3.
  specialize (x3 to). eapply x3; eauto.
  econs; ss. eapply Time.le_lteq; eauto.
  econs; ss. clear - TS23. eapply Time.le_lteq; eauto.
Qed.

Lemma memory_split_split_at_eq_prsv_contr
      loc from to lo
      mem1 mem1' msg1 val1 R1 ts1
      mem2 mem2' msg2 val2 R2 ts2
      (MEM_AR_EQ: Mem_at_eq lo mem1 mem2)
      (SPLIT1: Memory.split mem1 loc from to ts1 msg1 (Message.concrete val1 R1) mem1')
      (SPLIT2: Memory.split mem2 loc from to ts2 msg2 (Message.concrete val2 R2) mem2')
      (MEM_AR_EQ': Mem_at_eq lo mem1' mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  ts1 = ts2 /\ val1 = val2.
Proof.
  exploit Memory.split_get0; [eapply SPLIT1 | eauto..]. ii; des.
  exploit split_succeed_wf; [eapply SPLIT1 | eauto..]. ii; des. clear GET3.
  exploit Memory.split_get0; [eapply SPLIT2 | eauto..]. ii; des.
  exploit split_succeed_wf; [eapply SPLIT2 | eauto..]. ii; des. clear GET7.
  assert(ts1 = ts2).
  {
    destruct (Time.le_lt_dec ts1 ts2).
    {
      eapply Time.le_lteq in l. des; subst; ss.
      unfold Mem_at_eq in MEM_AR_EQ.
      exploit MEM_AR_EQ; eauto. ii.
      unfold Mem_approxEq_loc in x.
      des.
      specialize (x from ts1 val1). des.
      exploit x2; eauto. ii; des.
      exploit Memory.get_disjoint; [eapply GET4 | eapply x3 | eauto..]. ii; des; subst; eauto.
      unfold Interval.disjoint in x4.
      specialize (x4 ts1).
      exploit x4; eauto; ss.
      econs; ss; eauto. auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
      econs; ss; eauto.
      auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
    }
    {
      unfold Mem_at_eq in MEM_AR_EQ.
      exploit MEM_AR_EQ; eauto. ii.
      unfold Mem_approxEq_loc in x.
      des.
      specialize (x from ts1 val1). des.
      exploit x; eauto. ii; des.
      exploit Memory.get_disjoint; [eapply GET4 | eapply x3 | eauto..]. ii; des; subst; eauto.
      unfold Interval.disjoint in x4.
      specialize (x4 ts2).
      exploit x4; eauto; ss.
      econs; ss; eauto. auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
      econs; ss; eauto.
      auto_solve_time_rel.
      eapply Time.le_lteq; eauto.
    }
  }
  subst.
  split; eauto.
  unfold Mem_at_eq in MEM_AR_EQ.
  exploit MEM_AR_EQ; eauto. ii.
  unfold Mem_approxEq_loc in x.
  des.
  specialize (x from ts2 val2). des.
  exploit x1; eauto. ii; des.
  rewrite GET0 in x3. inv x3; eauto.
Qed.

Lemma memory_add_lower_at_eq_prsv_contr
      loc from to lo
      mem1 mem1'
      mem2 msg2 mem2'
      val1 R1 val2 R2
      (MEM_AR_EQ: Mem_at_eq lo mem1 mem2)
      (ADD: Memory.add mem1 loc from to (Message.concrete val1 R1) mem1')
      (LOWER: Memory.lower mem2 loc from to (Message.concrete val2 R2) msg2 mem2')
      (MEM_AR_EQ': Mem_at_eq lo mem1' mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  False.
Proof.
  exploit Memory.lower_get0; [eapply LOWER | eauto..]. ii; des.
  exploit lower_succeed_wf; [eapply LOWER | eauto..]. ii; des.
  inv MSG_LE0.
  exploit Memory.add_get0; [eapply ADD | eauto..]. ii; des.
  exploit add_succeed_wf; [eapply ADD | eauto..]. ii; des.
  unfold Mem_at_eq in MEM_AR_EQ.
  exploit MEM_AR_EQ; eauto. ii.
  unfold Mem_approxEq_loc in x. des.
  specialize (x from to val2). des.
  exploit x1; eauto. ii; des.
  rewrite GET2 in x3. ss.
Qed.

Lemma memory_split_lower_at_eq_prsv_contr
      loc from to lo
      mem1 mem1' msg1 val1 R1 ts1
      mem2 mem2' msg2 val2 R2
      (MEM_AR_EQ: Mem_at_eq lo mem1 mem2)
      (SPLIT: Memory.split mem1 loc from to ts1 msg1 (Message.concrete val1 R1) mem1')
      (LOWER: Memory.lower mem2 loc from to (Message.concrete val2 R2) msg2 mem2')
      (MEM_AR_EQ': Mem_at_eq lo mem1' mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  False.
Proof.
  exploit Memory.split_get0; [eapply SPLIT | eauto..]. ii; des.
  exploit split_succeed_wf; [eapply SPLIT | eauto..]. ii; des. clear GET3.
  exploit Memory.lower_get0; [eapply LOWER | eauto..]. ii; des.
  inv MSG_LE.
  exploit lower_succeed_wf; [eapply LOWER | eauto..]. ii; des.
  unfold Mem_at_eq in MEM_AR_EQ.
  exploit MEM_AR_EQ; eauto. ii.
  unfold Mem_approxEq_loc in x. des.
  specialize (x from to val2). des.
  exploit x1; eauto. ii; des.
  rewrite GET in x3. ss.
Qed.
  
Lemma local_write_Mem_at_eq_prsv_kind_match
      loc from to val lo ord 
      lc1 sc1 mem1 releasedr1 releasedw1 lc1' sc1' mem1' kind1
      lc2 sc2 mem2 releasedr2 releasedw2 lc2' sc2' mem2' kind2
      (MEM_AT_EQ: Mem_at_eq lo mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from to val releasedr1 releasedw1 ord lc1' sc1' mem1' kind1 lo)
      (WRITE2: Local.write_step lc2 sc2 mem2 loc from to val releasedr2 releasedw2 ord lc2' sc2' mem2' kind2 lo)
      (MEM_AT_EQ': Mem_at_eq lo mem1' mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  kind_match kind1 kind2.
Proof.
  destruct kind1.
  - (* kind1 = add *)
    destruct kind2; ss.
    + (* kind2 = split *)
      inv WRITE2. inv WRITE. inv PROMISE.
      des; subst; ss. inv RESERVE.
      inv WRITE1. inv WRITE. inv PROMISE.
      exploit memory_add_split_at_eq_prsv_contr;
        [eapply MEM_AT_EQ | eapply MEM0 | eapply MEM | eauto..].      
    + (* kind2 = lower *)
      inv WRITE1. inv WRITE. inv PROMISE.
      inv WRITE2. inv WRITE. inv PROMISE.
      des; subst.
      exploit memory_add_lower_at_eq_prsv_contr;
        [eapply MEM_AT_EQ | eapply MEM | eapply MEM0 | eauto..].
    + (* kind2 = cancel *)
      inv WRITE2. inv WRITE. inv PROMISE; ss.
  - (* kind1 = split *)
    destruct kind2; ss.
    + (* kind2 = add *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
      inv WRITE2. inv WRITE. inv PROMISE.
      exploit memory_add_split_at_eq_prsv_contr;
        [ | eapply MEM0 | eapply MEM | eauto..].
      eapply Mem_at_eq_reflexive; eauto.
      eapply Mem_at_eq_reflexive; eauto.
    + (* kind2 = split *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
      inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
      exploit memory_split_split_at_eq_prsv_contr; [eapply MEM_AT_EQ | eapply MEM | eapply MEM0 | eauto..].
    + (* kind2 = lower *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
      inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss.
      eapply memory_split_lower_at_eq_prsv_contr;
        [eapply MEM_AT_EQ | eapply MEM | eapply MEM0 | eauto..].
    + (* kind2 = cancel *)
      inv WRITE2. inv WRITE. inv PROMISE. ss.
  - (* kind1 = lower *)
    destruct kind2; ss.
    + (* kind2 = add *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss.
      inv WRITE2. inv WRITE. inv PROMISE.
      exploit memory_add_lower_at_eq_prsv_contr;
        [ | eapply MEM0 | eapply MEM | eauto..].
      eapply Mem_at_eq_reflexive; eauto.
      eapply Mem_at_eq_reflexive; eauto.
    + (* kind2 = split *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss.
      inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss. inv RESERVE.
      exploit memory_split_lower_at_eq_prsv_contr;
        [ | eapply MEM0 | eapply MEM | eauto..].
      eapply Mem_at_eq_reflexive; eauto.
      eapply Mem_at_eq_reflexive; eauto.
    + (* kind2 = lower *)
      inv WRITE1. inv WRITE. inv PROMISE. des; subst; ss.
      inv WRITE2. inv WRITE. inv PROMISE. des; subst; ss.
      exploit lower_succeed_wf; [eapply MEM | eauto..]. ii; des.
      inv MSG_LE.
      exploit lower_succeed_wf; [eapply MEM0 | eauto..]. ii; des.
      inv MSG_LE.
      eauto.
    + (* kind2 = cancel *)
      inv WRITE2. inv WRITE. inv PROMISE; ss.
  - (* kind1 = cancel *)
    inv WRITE1. inv WRITE. inv PROMISE; ss.
Qed.

Lemma Mem_at_eq_add_concrete_prsv
      mem1 loc from to val R mem1' lo
      mem2 R' mem2'
      (MEM_AT_EQ: Mem_at_eq lo mem1 mem2)
      (ADD1: Memory.add mem1 loc from to (Message.concrete val R) mem1')
      (ADD2: Memory.add mem2 loc from to (Message.concrete val R') mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  Mem_at_eq lo mem1' mem2'.
Proof.
  unfold Mem_at_eq in *. ii. exploit MEM_AT_EQ; eauto. ii.
  clear MEM_AT_EQ. unfold Mem_approxEq_loc in *. des.
  split; ii.
  {
    split; ii; des.
    erewrite Memory.add_o in H0; eauto. des_ifH H0; ss.
    des1; subst. inv H0.
    exploit Memory.add_get0; [eapply ADD2 | eauto..]. ii; des.
    eauto.
    specialize (x f t val0). destruct x. exploit H1; eauto.
    ii; des1.
    eapply Memory.add_get1 in x; eauto.
    erewrite Memory.add_o in H0; eauto. des_ifH H0; ss.
    des1; subst. inv H0. 
    exploit Memory.add_get0; [eapply ADD1 | eauto..]. ii; des.
    eauto.
    specialize (x f t val0). destruct x. exploit H2; eauto.
    ii. des1.
    eapply Memory.add_get1 in x; eauto.
  }
  {
    split; ii.
    erewrite Memory.add_o in H0; eauto. des_ifH H0; ss.
    erewrite Memory.add_o; eauto. des_if; eauto.
    simpl in a. des1; subst. des; ss.
    eapply x0; eauto.
    erewrite Memory.add_o in H0; eauto. des_ifH H0; ss.
    erewrite Memory.add_o; eauto. des_if; eauto.
    simpl in a. des; subst; ss.
    eapply x0; eauto.
  }
Qed.

Lemma Mem_at_eq_add_reserve_prsv
      mem1 loc from to mem1' lo
      mem2 mem2'
      (MEM_AT_EQ: Mem_at_eq lo mem1 mem2)
      (ADD1: Memory.add mem1 loc from to Message.reserve mem1')
      (ADD2: Memory.add mem2 loc from to Message.reserve mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  Mem_at_eq lo mem1' mem2'.
Proof.
  unfold Mem_at_eq in *. ii. exploit MEM_AT_EQ; eauto. ii.
  clear MEM_AT_EQ. unfold Mem_approxEq_loc in *. des.
  split; ii. split; ii; des.
  erewrite Memory.add_o in H0; eauto.
  des_ifH H0; ss; eauto.
  specialize (x f t val). des.
  erewrite Memory.add_o; eauto.
  des_if; eauto. simpl in a. des1; subst; ss.
  erewrite Memory.add_o; eauto.
  des_if; eauto. simpl in a. des1; subst; ss.
  erewrite Memory.add_o in H0; eauto.
  des_ifH H0; ss.
  specialize (x f t val). des.
  erewrite Memory.add_o; eauto.
  des_if; eauto. simpl in a. des1; subst. ss.
  erewrite Memory.add_o; eauto.
  des_if; eauto. simpl in a. des1; subst. ss.
  split; ii.
  erewrite Memory.add_o in H0; eauto.
  des_ifH H0; ss. des1; subst. inv H0.
  exploit Memory.add_get0; [eapply ADD2 | eauto..]. ii; des; eauto.
  erewrite Memory.add_o; eauto.
  des_if; eauto. simpl in a. des1; subst. des1; ss.
  simpl in o0. eapply x0; eauto.
  erewrite Memory.add_o in H0; eauto.
  des_ifH H0; eauto. simpl in a. des1; subst. inv H0.
  exploit Memory.add_get0; eauto. ii; des; eauto.
  simpl in o.
  erewrite Memory.add_o; eauto.
  des_if; eauto.
  simpl in a. des1; subst; ss. des1; ss.
  eapply x0; eauto.
Qed.
  
Lemma Mem_at_eq_split_concrete_prsv
      mem1 loc from to ts val R1 val' R1' mem1' lo
      mem2 R2 R2' mem2'
      (MEM_AT_EQ: Mem_at_eq lo mem1 mem2)
      (SPLIT1: Memory.split mem1 loc from to ts (Message.concrete val R1)
                            (Message.concrete val' R1') mem1')
      (SPLIT2: Memory.split mem2 loc from to ts (Message.concrete val R2)
                            (Message.concrete val' R2') mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  Mem_at_eq lo mem1' mem2'.
Proof.
  unfold Mem_at_eq in *. ii. exploit MEM_AT_EQ; eauto. ii.
  clear MEM_AT_EQ. unfold Mem_approxEq_loc in *. des.
  split; ii.
  - split; ii; des.
    {
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; eauto. simpl in a. des1; subst.
      inv H0. exploit Memory.split_get0; [eapply SPLIT2 | eauto..].
      ii; do 3 des1. eauto.
      simpl in o. des_ifH H0. 
      simpl in a. des1; subst. des; ss. 
      inv H0. 
      exploit Memory.split_get0; [eapply SPLIT2 | eauto..].
      ii; do 3 des1. eauto.
      simpl in o0.
      specialize (x f t val0). destruct x.
      exploit H1; eauto. ii. des1.
      erewrite Memory.split_o; eauto.
      des_if; eauto. simpl in a. des1; subst; ss. des1; ss. des1; ss.
      des_if; eauto. simpl in a. des1; subst. des1; ss. des1; ss.
    }
    {
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; eauto. simpl in a. des1; subst.
      inv H0. exploit Memory.split_get0; [eapply SPLIT1 | eauto..].
      ii; do 3 des1. eauto.
      simpl in o. des_ifH H0. 
      simpl in a. des1; subst. des; ss. 
      inv H0. 
      exploit Memory.split_get0; [eapply SPLIT1 | eauto..].
      ii; do 3 des1. eauto.
      simpl in o0.
      specialize (x f t val0). destruct x.
      exploit H1; eauto. ii. des1.
      erewrite Memory.split_o; eauto.
      des_if; eauto. simpl in a. des1; subst; ss. des1; ss. des1; ss.
      des_if; eauto. simpl in a. des1; subst. des1; ss. des1; ss.
    }
  - split; ii; des.
    {
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; eauto. ss.
      des_ifH H0; eauto; ss.
      erewrite Memory.split_o; eauto.
      des_if; ss. des1; subst. des1; ss. des1; ss.
      des_if; ss. des1; subst. des1; ss. des1; ss.
      eapply x0; eauto.
    }
    {
      erewrite Memory.split_o in H0; eauto.
      des_ifH H0; eauto. ss.
      des_ifH H0; eauto; ss.
      erewrite Memory.split_o; eauto.
      des_if; ss. des1; subst. des1; ss. des1; ss.
      des_if; ss. des1; subst. des1; ss. des1; ss.
      eapply x0; eauto.
    }
Qed.

Lemma Mem_at_eq_lower_concrete_prsv
      mem1 loc from to val R1 val' R1' mem1' lo
      mem2 R2 R2' mem2'
      (MEM_AT_EQ: Mem_at_eq lo mem1 mem2)
      (LOWER1: Memory.lower mem1 loc from to (Message.concrete val R1)
                            (Message.concrete val' R1') mem1')
      (LOWER2: Memory.lower mem2 loc from to (Message.concrete val R2)
                            (Message.concrete val' R2') mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  Mem_at_eq lo mem1' mem2'.
Proof.
  unfold Mem_at_eq in *. ii. exploit MEM_AT_EQ; eauto. ii.
  clear MEM_AT_EQ. unfold Mem_approxEq_loc in *. des.
  split; ii.
  - split; ii; des.
    {
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; eauto. simpl in a. des1; subst.
      inv H0. exploit Memory.lower_get0; [eapply LOWER2 | eauto..].
      ii; do 2 des1. eauto.
      simpl in o.
      specialize (x f t val0). destruct x.
      exploit H1; eauto. ii. des1.
      erewrite Memory.lower_o; eauto.
      des_if; eauto. simpl in a. des1; subst; ss. des1; ss.
    }
    {
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; eauto. simpl in a. des1; subst.
      inv H0. exploit Memory.lower_get0; [eapply LOWER1 | eauto..].
      ii; do 2 des1. eauto.
      simpl in o. 
      specialize (x f t val0). destruct x.
      exploit H1; eauto. ii. des1.
      erewrite Memory.lower_o; eauto.
      des_if; eauto. simpl in a. des1; subst; ss. des1; ss. 
    }
  - split; ii; des.
    {
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; eauto. ss.
      erewrite Memory.lower_o; eauto.
      des_if; ss. des1; subst. des1; ss.
      eapply x0; eauto.
    }
    {
      erewrite Memory.lower_o in H0; eauto.
      des_ifH H0; eauto. ss.
      erewrite Memory.lower_o; eauto.
      des_if; ss. des1; subst. des1; ss. 
      eapply x0; eauto.
    }
Qed.

Lemma Mem_at_eq_cancel_prsv
      mem1 loc from to mem1' lo
      mem2 mem2'
      (MEM_AT_EQ: Mem_at_eq lo mem1 mem2)
      (CCL1: Memory.remove mem1 loc from to Message.reserve mem1')
      (CCL2: Memory.remove mem2 loc from to Message.reserve mem2')
      (AT_LOC: lo loc = Ordering.atomic):
  Mem_at_eq lo mem1' mem2'.
Proof.
  unfold Mem_at_eq in *. ii. exploit MEM_AT_EQ; eauto. ii.
  clear MEM_AT_EQ. unfold Mem_approxEq_loc in *. des.
  split; ii.
  - split; ii; des.
    {
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss. 
      erewrite Memory.remove_o; eauto.
      des_if; eauto. simpl in a. des1; subst; ss. des1; ss.
      specialize (x f t val). des; eauto.
    }
    {
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss. 
      erewrite Memory.remove_o; eauto.
      des_if; eauto. simpl in a. des1; subst; ss. des1; ss.
      specialize (x f t val). destruct x. eauto.
    }
  - split; ii; des.
    {
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss.
      erewrite Memory.remove_o; eauto.
      des_if; ss. des1; subst. des1; ss.
      eapply x0; eauto.
    }
    {
      erewrite Memory.remove_o in H0; eauto.
      des_ifH H0; ss.
      erewrite Memory.remove_o; eauto.
      des_if; ss. des1; subst. des1; ss. 
      eapply x0; eauto.
    }
Qed.
    
Lemma Mem_at_eq_local_write_prsv_general
      loc from to val lo ord 
      lc1 sc1 mem1 releasedr1 releasedw1 lc1' sc1' mem1' kind inj
      lc2 sc2 mem2 releasedr2
      (MEM_AT_EQ: Mem_at_eq lo mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from to val releasedr1 releasedw1 ord lc1' sc1' mem1' kind lo)
      (ATM_ID: forall loc0 to0 to0', lo loc0 = Ordering.atomic -> inj loc0 to0 = Some to0' -> to0 = to0')
      (WRITEABLE: inj loc (View.rlx (TView.cur (Local.tview lc1)) loc) =
                  Some (View.rlx (TView.cur (Local.tview lc2)) loc))
      (PRM: forall ts f v R l, Memory.get l ts (Local.promises lc1) = Some (f, Message.concrete v R) ->
                          exists ts' f' v' R', Memory.get l ts' (Local.promises lc2) = Some (f', Message.concrete v' R')
                                          /\ inj l ts = Some ts')
      (PRM_NONSYNC: 
         forall ts' f' v' R' l, Memory.get l ts' (Local.promises lc2) = Some (f', Message.concrete v' (Some R')) ->
                           exists ts f v R, Memory.get l ts (Local.promises lc1) = Some (f, Message.concrete v (Some R)))
      (COMPLETE_INJ: forall ts f v R l, Memory.get l ts mem1 = Some (f, Message.concrete v R) ->
                                   exists ts', inj l ts = Some ts')
      (SOUND_INJ: forall ts ts' l, inj l ts = Some ts' ->
                              exists f v R, Memory.get l ts mem1 = Some (f, Message.concrete v R))
      (LOCAL_WF1: Local.wf lc1 mem1)
      (LOCAL_WF2: Local.wf lc2 mem2)
      (AT_LOC: lo loc = Ordering.atomic)
      (VIEW_INJ: opt_ViewInj inj releasedr1 releasedr2)
      (MON_INJ: monotonic_inj inj)
      (REL_VIEWINJ: ViewInj inj (TView.rel (Local.tview lc1) loc) (TView.rel (Local.tview lc2) loc))
      (CUR_VIEWINJ: Ordering.le Ordering.acqrel ord ->
                    ViewInj inj (TView.cur (Local.tview lc1)) (TView.cur (Local.tview lc2)))
      (CLOSED_TVIEW: closed_tviewInj inj (Local.tview lc1))
      (CLOSED_OPT_VIEW: closed_opt_viewinj inj releasedr1)
      (MSG_VIEW_REL: forall f v R R',
          Memory.get loc to mem1 = Some (f, Message.concrete v R) ->
          Memory.get loc to mem2 = Some (f, Message.concrete v R') ->
          (opt_ViewInj inj R R' /\ closed_opt_viewinj inj R)):
  exists releasedw2 lc2' mem2' inj' kind',
    <<WRITE2: Local.write_step lc2 sc2 mem2 loc from to val releasedr2 releasedw2 ord lc2' sc2 mem2' kind' lo>> /\
    <<MEM_AT_EQ2: Mem_at_eq lo mem1' mem2'>> /\
    <<NEW_INJ: inj' = fun loc0 to0 => if loc_ts_eq_dec (loc0, to0) (loc, to) then Some to else inj loc0 to0 >> /\
    <<INCR_INJ: incr_inj inj inj'>> /\
    <<COMPLETE_INJ': forall ts f v R l, Memory.get l ts mem1' = Some (f, Message.concrete v R) ->
                                   exists ts', inj' l ts = Some ts'>> /\
    <<SOUND_INJ: forall ts ts' l, inj' l ts = Some ts' ->
                             exists f v R, Memory.get l ts mem1' = Some (f, Message.concrete v R)>> /\
    <<KIND_MATCH: kind_match kind kind'>> /\
    <<MON_INJ': monotonic_inj inj'>>.
Proof.
  inv WRITE1. inv WRITE; ss. inv PROMISE; ss.
  - (* add *)
    assert (NOT_COVER: forall t : Time.t, Cover.covered loc t mem2 -> ~ Interval.mem (from, to) t).
    {
      ii. eapply memory_add_cover_disjoint; eauto.
      clear - H H0 MEM_AT_EQ AT_LOC. inv H; ss.
      unfold Mem_at_eq in MEM_AT_EQ. exploit MEM_AT_EQ; eauto.
      ii. unfold Mem_approxEq_loc in x. des.
      dup GET.
      destruct msg.
      specialize (x from0 to0 val).
      des. exploit x1; eauto. ii; des.
      econs; eauto.
      eapply x0 in GET0. econs; eauto.
    }
    assert (INJ_NONE: inj loc to = None).
    {
      clear - SOUND_INJ MEM. destruct (inj loc to) eqn:INJ; eauto.
      exploit SOUND_INJ; eauto. ii; des.
      exploit Memory.add_get0; eauto. ii; des. rewrite x in GET. ss.
    }
    pose proof (identity_inj_incr) as NEW_INJ.
    specialize (NEW_INJ inj loc to). exploit NEW_INJ; eauto.
    clear NEW_INJ. intro NEW_INJ. des.
    assert (INCR_INJ: incr_inj inj inj').
    {
      clear - NEW_INJ0 INJ_NONE.
      subst. unfold incr_inj. ii. des_if; eauto.
      ss. des; subst. rewrite INJ_NONE in H; ss.
    }
    
    exploit write_succeed_valid; eauto.
    {
      instantiate (1 := Local.promises lc2). inv LOCAL_WF2; eauto.
    }
    {
      instantiate (1 := (TView.write_released (Local.tview lc2) sc2 loc to releasedr2 ord)).
      eapply TLE_write_prs_general with (inj := inj'); eauto.
      inv TS; eauto.
      rewrite NEW_INJ0. des_if; eauto. simpl in o. des; ss.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply incr_inj_ViewInj; eauto. clear - CLOSED_TVIEW. unfold closed_tviewInj in CLOSED_TVIEW.
      des; eauto.
      ii. exploit CUR_VIEWINJ; eauto. ii.
      eapply incr_inj_ViewInj; eauto. clear - CLOSED_TVIEW. unfold closed_tviewInj in CLOSED_TVIEW.
      des; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
    }
    {
      clear - MEM. eapply add_succeed_wf in MEM. des; eauto.
    }
    {
      clear - ATTACH MEM_AT_EQ AT_LOC.
      unfold attatched_time. ii; des.
      unfold Mem_at_eq in MEM_AT_EQ. exploit MEM_AT_EQ; eauto. ii. clear MEM_AT_EQ.
      unfold Mem_approxEq_loc in x. des.
      destruct msg.
      specialize (x to to' val0). des.
      exploit x1; eauto. ii; des. eauto.
      eapply x0 in GET. eauto.
    }
    {
      instantiate (1 := val).
      exploit add_succeed_wf; eauto. ii; des.
      inv MSG_WF. econs.
      eapply View_opt_wf_inj_general with
          (inj := fun loc1 to1 => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else inj loc1 to1); eauto.
      eapply incr_inj_ViewInj; eauto. clear - CLOSED_TVIEW. unfold closed_tviewInj in CLOSED_TVIEW.
      des; eauto.
      ii. eapply incr_inj_ViewInj; eauto. clear - CLOSED_TVIEW. unfold closed_tviewInj in CLOSED_TVIEW.
      des; eauto.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
      des_if; eauto.
      simpl in o. des; ss.
    }

    ii. des1.
    do 3 eexists. exists inj', Memory.op_kind_add.
    splits.
    {
      econs; eauto.
      clear - WRITEABLE AT_LOC WRITABLE ATM_ID.
      exploit ATM_ID; eauto. ii. inv WRITABLE. econs; eauto.
      rewrite <- x. eauto.
      intro ORD. eapply RELEASE in ORD.
      clear - PRM_NONSYNC ORD. unfold Memory.nonsynch_loc in *. ii.
      destruct msg; eauto.
      destruct released; eauto.
      eapply PRM_NONSYNC in GET; eauto. des.
      eapply ORD in GET. ss.
    }
    {
      inv WRITE. inv PROMISE.
      eapply Mem_at_eq_add_concrete_prsv; eauto.
    }
    {
      rewrite NEW_INJ0.
      eapply functional_extensionality. ii. eapply functional_extensionality. ii.
      des_if; eauto; ss. des_if; ss; eauto. des; subst; ss.
      des_if; eauto. ss. des; subst; ss.
    }
    eauto.
    {
      ii. subst. clear - H COMPLETE_INJ SOUND_INJ MEM.
      des_if; eauto. ss.
      erewrite Memory.add_o in H; eauto. des_ifH H; eauto.
      simpl in a. des; subst; ss.
    }
    {
      ii. subst. des_ifH H; eauto.
      simpl in a. des; subst. inv H.
      clear - MEM. exploit Memory.add_get0; eauto. ii; des. eauto.
      simpl in o.
      eapply SOUND_INJ in H. do 3 des1.
      erewrite Memory.add_o; eauto. des_if; eauto.
    }
    eauto.
    eauto.
  - des; subst. inv RESERVE. 
    assert (SRC_SPLIT_MSG: exists R2,
               Memory.get loc ts3 (Local.promises lc2) = Some (from, Message.concrete val' R2)).
    {
      exploit Memory.split_get0; [eapply PROMISES | eauto..]. ii; des.
      exploit PRM; eauto. ii; do 5 des1.
      exploit ATM_ID; eauto. ii; subst.
      clear - GET0 x LOCAL_WF1 LOCAL_WF2 MEM_AT_EQ AT_LOC.
      inv LOCAL_WF1. inv LOCAL_WF2.
      exploit PROMISES; eauto. exploit PROMISES0; eauto. ii.
      unfold Mem_at_eq in MEM_AT_EQ. exploit MEM_AT_EQ; eauto. ii. clear MEM_AT_EQ.
      unfold Mem_approxEq_loc in x2. des.
      specialize (x2 from ts' val'). des. exploit x2; eauto.
      ii; des. rewrite x0 in x6. inv x6. eauto.
    }
    des1.
    assert (SRC_SPLIT_MEM: Memory.get loc ts3 mem2 = Some (from, Message.concrete val' R2)).
    {
      clear - LOCAL_WF2 SRC_SPLIT_MSG. inv LOCAL_WF2.
      eapply PROMISES; eauto.
    }

    exploit split_succeed_wf; [eapply PROMISES | eauto..].
    ii; do 3 des1. inv MSG_WF.

    assert (INJ_NONE: inj loc to = None).
    {
      clear - SOUND_INJ MEM. destruct (inj loc to) eqn:INJ; eauto.
      exploit SOUND_INJ; eauto. ii; des.
      exploit Memory.split_get0; eauto. ii; des. rewrite x in GET. ss.
    }
    pose proof (identity_inj_incr) as NEW_INJ.
    specialize (NEW_INJ inj loc to). exploit NEW_INJ; eauto.
    clear NEW_INJ. intro NEW_INJ. des.
    assert (INCR_INJ: incr_inj inj inj').
    {
      clear - NEW_INJ0 INJ_NONE.
      subst. unfold incr_inj. ii. des_if; eauto.
      ss. des; subst. rewrite INJ_NONE in H; ss.
    } 

    exploit Memory.split_exists; [eapply SRC_SPLIT_MSG | eauto | eauto | idtac..].
    {
      instantiate (1 := Message.concrete val'0 (TView.write_released (Local.tview lc2) sc2 loc to releasedr2 ord)).
      econs. eapply View_opt_wf_inj_general with (inj := inj'); eauto.
      eapply incr_inj_ViewInj; eauto. clear - CLOSED_TVIEW. unfold closed_tviewInj in CLOSED_TVIEW.
      des; eauto.
      ii. eapply incr_inj_ViewInj; eauto. clear - CLOSED_TVIEW. unfold closed_tviewInj in CLOSED_TVIEW.
      des; eauto.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
      subst. des_if; eauto.
      simpl in o. des; ss.
    }
    ii. des1.
    exploit Memory.split_exists_le; [ | eapply x0 | eauto..].
    {
      inv LOCAL_WF2; eauto.
    }
    ii. des1. 
    exploit Memory.split_get0; [eapply x0 | eauto..]. ii; do 3 des1.
    exploit Memory.remove_exists; [eapply GET1 | eauto..]. ii; des1.
    rename mem4 into prm2'.
    
    do 3 eexists. exists inj', (Memory.op_kind_split ts3 (Message.concrete val' R2)).
    splits.
    econs; eauto.
    {
      econs; eauto.
      clear - WRITEABLE AT_LOC WRITABLE ATM_ID.
      exploit ATM_ID; eauto. ii. inv WRITABLE. 
      rewrite <- x. eauto.
    }
    {
      instantiate (2 := prm2'). instantiate (1 := mem3).
      econs; eauto. econs; eauto.
      econs. eapply TLE_write_prs_general with (inj := inj'); eauto.
      inv TS; eauto.
      rewrite NEW_INJ0. des_if; eauto. simpl in o. des; ss.
      eapply incr_inj_opt_ViewInj; eauto.
      eapply incr_inj_ViewInj; eauto. clear - CLOSED_TVIEW. unfold closed_tviewInj in CLOSED_TVIEW.
      des; eauto.
      ii. exploit CUR_VIEWINJ; eauto. ii.
      eapply incr_inj_ViewInj; eauto. clear - CLOSED_TVIEW. unfold closed_tviewInj in CLOSED_TVIEW.
      des; eauto.
      eapply incr_inj_closed_tviewInj; eauto.
      eapply incr_inj_closed_opt_ViewInj; eauto.
    }
    {
      intro ORD. eapply RELEASE in ORD.
      clear - PRM_NONSYNC ORD. unfold Memory.nonsynch_loc in *. ii.
      destruct msg; eauto.
      destruct released; eauto.
      eapply PRM_NONSYNC in GET; eauto. des.
      eapply ORD in GET. ss.
    }
    {
      eapply Mem_at_eq_split_concrete_prsv; eauto.
    }
    {
      rewrite NEW_INJ0.
      eapply functional_extensionality. ii. eapply functional_extensionality. ii.
      des_if; eauto; ss. des_if; ss; eauto. des; subst; ss.
      des_if; eauto. ss. des; subst; ss.
    }
    eauto.
    {
      ii. rewrite NEW_INJ0.
      erewrite Memory.split_o in H; eauto. des_ifH H; eauto.
      simpl in a. des1; subst. inv H. des_if; eauto.
      simpl in o. des1; ss.
      simpl in o. des_ifH H; ss. des1; subst.
      des_if; eauto. simpl in o0. des1; ss. des1; ss.
      exploit Memory.split_get0; [eapply MEM | eauto..]. ii; do 3 des1.
      eapply COMPLETE_INJ in GET5. des1. eauto.
      des_if; eauto.
    }
    {
      rewrite NEW_INJ0. ii. des_ifH H; ss. des1; subst. inv H.
      exploit Memory.split_get0; [eapply MEM | eauto..]. ii; do 3 des1.
      eauto.
      eapply SOUND_INJ in H. do 3 des1.
      eapply Memory.split_get1 in H; eauto.
      do 2 des1. eauto.
    }
    eauto. eauto. eauto.
  - des. subst.
    assert (SRC_LOWER_MSG: exists R2,
               Memory.get loc to (Local.promises lc2) = Some (from, Message.concrete val0 R2)).
    {
      exploit Memory.lower_get0; [eapply PROMISES | eauto..]. ii; des.
      exploit PRM; eauto. ii; do 5 des1.
      exploit ATM_ID; eauto. ii; subst. 
      clear - GET x LOCAL_WF1 LOCAL_WF2 MEM_AT_EQ AT_LOC.
      inv LOCAL_WF1. inv LOCAL_WF2.
      exploit PROMISES; eauto. exploit PROMISES0; eauto. ii.
      unfold Mem_at_eq in MEM_AT_EQ. exploit MEM_AT_EQ; eauto. ii. clear MEM_AT_EQ.
      unfold Mem_approxEq_loc in x2. des.
      specialize (x2 from ts' val0). des. exploit x2; eauto.
      ii; des. rewrite x0 in x6. inv x6. eauto.
    }
    des1.
    assert (SRC_LOWER_MEM: Memory.get loc to mem2 = Some (from, Message.concrete val0 R2)).
    {
      clear - LOCAL_WF2 SRC_LOWER_MSG. inv LOCAL_WF2.
      eapply PROMISES; eauto.
    }

    exploit lower_succeed_wf; [eapply PROMISES | eauto..].
    ii; do 3 des1. inv MSG_WF. inv MSG_LE.
    assert (ID_LOC_INJ: inj loc to = Some to).
    {
      clear - MEM COMPLETE_INJ ATM_ID AT_LOC.
      exploit Memory.lower_get0; eauto. ii; des.
      eapply COMPLETE_INJ in GET; eauto. des.
      exploit ATM_ID; eauto. ii; subst; eauto.
    }

    exploit Memory.lower_exists; [eapply SRC_LOWER_MSG | eauto | eauto | idtac..].
    {
      instantiate (1 := Message.concrete val0 (TView.write_released (Local.tview lc2) sc2 loc to releasedr2 ord)).
      econs. eapply View_opt_wf_inj_general with (inj := inj); eauto.
    }
    {
      econs; eauto.
      exploit opt_ViewInj_write_released_inj_general; eauto.
      instantiate (1 := sc2). instantiate (1 := sc1). intros WRITE_VIEWINJ.
      inv LOCAL_WF1. exploit PROMISES0; eauto. ii.
      exploit MSG_VIEW_REL; eauto. ii; des.
      eapply view_opt_le_inj; eauto.
      eapply closed_opt_viewInj_write_released; eauto.
    }
    ii. des1.
    exploit Memory.lower_exists_le; [ | eapply x0 | eauto..].
    {
      inv LOCAL_WF2; eauto.
    }
    ii. des1. 
    exploit Memory.lower_get0; [eapply x0 | eauto..]. ii; do 2 des1.
    exploit Memory.remove_exists; [eapply GET1 | eauto..]. ii; des1.
    rename mem4 into prm2'.

    do 3 eexists. exists inj, (Memory.op_kind_lower (Message.concrete val0 R2)).
    splits; eauto.
    econs; eauto.
    {
      econs; eauto.
      clear - WRITEABLE AT_LOC WRITABLE ATM_ID.
      exploit ATM_ID; eauto. ii. inv WRITABLE. 
      rewrite <- x. eauto.
    }
    {
      instantiate (2 := prm2'). instantiate (1 := mem3).
      econs; eauto. econs; eauto.
      econs. eapply TLE_write_prs_general with (inj := inj); eauto.
      inv TS; eauto.
    }
    {
      intro ORD. eapply RELEASE in ORD.
      clear - PRM_NONSYNC ORD. unfold Memory.nonsynch_loc in *. ii.
      destruct msg; eauto.
      destruct released; eauto.
      eapply PRM_NONSYNC in GET; eauto. des.
      eapply ORD in GET. ss.
    }
    {
      eapply Mem_at_eq_lower_concrete_prsv; eauto.
    }
    {
      eapply functional_extensionality. ii. eapply functional_extensionality. ii.
      des_if; eauto; ss. des; subst; ss.
    }
    {
      unfold incr_inj; ii; eauto.
    }
    {
      ii. erewrite Memory.lower_o in H; eauto.
      des_ifH H; subst. simpl in a. des1; subst; eauto. eauto.
    }
    {
      ii. erewrite Memory.lower_o; eauto.
      des_if; eauto.
    }
Qed.

Lemma Mem_at_eq_local_write_prsv
      loc from to val lo ord 
      lc1 sc1 mem1 releasedr1 releasedw1 lc1' sc1' mem1' kind inj
      lc2 sc2 mem2 releasedr2 index
      (MEM_AT_EQ: Mem_at_eq lo mem1 mem2)
      (WRITE1: Local.write_step lc1 sc1 mem1 loc from to val releasedr1 releasedw1 ord lc1' sc1' mem1' kind lo)
      (ATM_ID: forall loc0 to0 to0', lo loc0 = Ordering.atomic -> inj loc0 to0 = Some to0' -> to0 = to0')
      (WRITEABLE: inj loc (View.rlx (TView.cur (Local.tview lc1)) loc) =
                  Some (View.rlx (TView.cur (Local.tview lc2)) loc))
      (PRM: @rel_promises index inj dset_init (Local.promises lc1) (Local.promises lc2))
      (LOCAL_WF1: Local.wf lc1 mem1)
      (LOCAL_WF2: Local.wf lc2 mem2)
      (AT_LOC: lo loc = Ordering.atomic)
      (VIEW_INJ: opt_ViewInj inj releasedr1 releasedr2)
      (MON_INJ: monotonic_inj inj)
      (REL_VIEWINJ: ViewInj inj (TView.rel (Local.tview lc1) loc) (TView.rel (Local.tview lc2) loc))
      (CUR_VIEWINJ: Ordering.le Ordering.acqrel ord ->
                    ViewInj inj (TView.cur (Local.tview lc1)) (TView.cur (Local.tview lc2)))
      (CLOSED_TVIEW: closed_tviewInj inj (Local.tview lc1))
      (CLOSED_OPT_VIEW: closed_opt_viewinj inj releasedr1)
      (MSG_INJ: MsgInj inj mem1 mem2)
      (CLOSED_MEM: Memory.closed mem1):
  exists releasedw2 lc2' mem2' inj' kind',
    <<WRITE2: Local.write_step lc2 sc2 mem2 loc from to val releasedr2 releasedw2 ord lc2' sc2 mem2' kind' lo>> /\
    <<MEM_AT_EQ2: Mem_at_eq lo mem1' mem2'>> /\
    <<NEW_INJ: inj' = fun loc0 to0 => if loc_ts_eq_dec (loc0, to0) (loc, to) then Some to else inj loc0 to0 >> /\
    <<INCR_INJ: incr_inj inj inj'>> /\
    <<COMPLETE_INJ': forall ts f v R l, Memory.get l ts mem1' = Some (f, Message.concrete v R) ->
                                   exists ts', inj' l ts = Some ts'>> /\
    <<SOUND_INJ: forall ts ts' l, inj' l ts = Some ts' ->
                             exists f v R, Memory.get l ts mem1' = Some (f, Message.concrete v R)>> /\
    <<KIND_MATCH: kind_match kind kind'>> /\
    <<MON_INJ': monotonic_inj inj'>>.
Proof.
  eapply Mem_at_eq_local_write_prsv_general; eauto.
  - ii. clear - PRM H. inv PRM. exploit SOUND2; eauto.
    ii; des; eauto.
    do 4 eexists. split; eauto.
  - ii. inv PRM. clear SOUND1 SOUND2.
    exploit COMPLETE; eauto. ii; des.
    rewrite dset_gempty in x0. ss.
    clear COMPLETE. inv LOCAL_WF1. inv LOCAL_WF2.
    exploit PROMISES; eauto. ii.
    exploit PROMISES0; eauto. ii.
    inv MSG_INJ. exploit SOUND; eauto. ii; des.
    rewrite x in x3. inv x3.
    rewrite x2 in x5. inv x5. destruct R; ss.
    eauto.
  - ii. inv MSG_INJ. eapply SOUND in H; eauto.
    des; eauto.
  - ii. inv MSG_INJ. exploit COMPLETE; eauto.
    ii; des. eauto.
  - ii. inv MSG_INJ. exploit SOUND; eauto.
    ii; des. exploit ATM_ID; eauto. ii; subst.
    rewrite H0 in x1. inv x1.
    split; eauto.
    eapply closed_optview_msginj_implies_closed_viewInj; eauto.
    instantiate (1 := mem1).
    eapply WFConfig.closed_mem_implies_closed_msg; eauto.
    econs; eauto.
Qed.

Lemma Mem_at_eq_add_na_stable
      mem_tgt loc from to msg mem_tgt' mem_src lo
      (MEM_AT_EQ: Mem_at_eq lo mem_tgt mem_src)
      (ADD: Memory.add mem_tgt loc from to msg mem_tgt')
      (NA_LOC: lo loc = Ordering.nonatomic):
  Mem_at_eq lo mem_tgt' mem_src.
Proof.
  unfold Mem_at_eq in *. ii.
  exploit MEM_AT_EQ; eauto. ii. clear MEM_AT_EQ.
  unfold Mem_approxEq_loc in *. des.
  split; ii.
  - split; ii; des.
    eapply Memory_add_disj_loc_stable with (loc0 := loc0) in ADD; eauto.
    assert (GET_TGT: Memory.get loc0 t mem_tgt =
                       Some (f, Message.concrete val R)).
    {
      unfold Memory.get in *. rewrite <- ADD in H0; eauto.
    }
    specialize (x f t val). des.
    exploit x; eauto.
    ii; subst. rewrite NA_LOC in H. ss.
    specialize (x f t val). des.
    exploit x1; eauto. ii; des; eauto.
    eapply Memory_add_disj_loc_stable with (loc0 := loc0) in ADD; eauto.
    unfold Memory.get. rewrite <- ADD; eauto.
    ii; subst. rewrite NA_LOC in H. ss.
  - split; ii.
    eapply x0; eauto.
    eapply Memory_add_disj_loc_stable with (loc0 := loc0) in ADD; eauto.
    unfold Memory.get in *. rewrite ADD; eauto.
    ii; subst. rewrite NA_LOC in H; ss.
    eapply x0 in H0; eauto.
    eapply Memory_add_disj_loc_stable with (loc0 := loc0) in ADD; eauto.
    unfold Memory.get in *. rewrite <- ADD; eauto.
    ii; subst. rewrite NA_LOC in H; ss.
Qed.

Lemma Mem_at_eq_split_na_stable
      mem_tgt loc from to ts msg1 msg2 mem_tgt' mem_src lo
      (MEM_AT_EQ: Mem_at_eq lo mem_tgt mem_src)
      (SPLIT: Memory.split mem_tgt loc from to ts msg1 msg2 mem_tgt')
      (NA_LOC: lo loc = Ordering.nonatomic):
  Mem_at_eq lo mem_tgt' mem_src.
Proof.
  unfold Mem_at_eq in *. ii.
  exploit MEM_AT_EQ; eauto. ii. clear MEM_AT_EQ.
  unfold Mem_approxEq_loc in *. des.
  split; ii.
  - split; ii; des.
    eapply Memory_split_disj_loc_stable with (loc0 := loc0) in SPLIT; eauto.
    assert (GET_TGT: Memory.get loc0 t mem_tgt =
                       Some (f, Message.concrete val R)).
    {
      unfold Memory.get in *. rewrite <- SPLIT in H0; eauto.
    }
    specialize (x f t val). des.
    exploit x; eauto.
    ii; subst. rewrite NA_LOC in H. ss.
    specialize (x f t val). des.
    exploit x1; eauto. ii; des; eauto.
    eapply Memory_split_disj_loc_stable with (loc0 := loc0) in SPLIT; eauto.
    unfold Memory.get. rewrite <- SPLIT; eauto.
    ii; subst. rewrite NA_LOC in H. ss.
  - split; ii.
    eapply x0; eauto.
    eapply Memory_split_disj_loc_stable with (loc0 := loc0) in SPLIT; eauto.
    unfold Memory.get in *. rewrite SPLIT; eauto.
    ii; subst. rewrite NA_LOC in H; ss.
    eapply x0 in H0; eauto.
    eapply Memory_split_disj_loc_stable with (loc0 := loc0) in SPLIT; eauto.
    unfold Memory.get in *. rewrite <- SPLIT; eauto.
    ii; subst. rewrite NA_LOC in H; ss.
Qed.

Lemma Mem_at_eq_lower_na_stable
      mem_tgt loc from to msg1 msg2 mem_tgt' mem_src lo
      (MEM_AT_EQ: Mem_at_eq lo mem_tgt mem_src)
      (LOWER: Memory.lower mem_tgt loc from to msg1 msg2 mem_tgt')
      (NA_LOC: lo loc = Ordering.nonatomic):
  Mem_at_eq lo mem_tgt' mem_src.
Proof.
  unfold Mem_at_eq in *. ii.
  exploit MEM_AT_EQ; eauto. ii. clear MEM_AT_EQ.
  unfold Mem_approxEq_loc in *. des.
  split; ii.
  - split; ii; des.
    eapply Memory_lower_disj_loc_stable with (loc0 := loc0) in LOWER; eauto.
    assert (GET_TGT: Memory.get loc0 t mem_tgt =
                       Some (f, Message.concrete val R)).
    {
      unfold Memory.get in *. rewrite <- LOWER in H0; eauto.
    }
    specialize (x f t val). des.
    exploit x; eauto.
    ii; subst. rewrite NA_LOC in H. ss.
    specialize (x f t val). des.
    exploit x1; eauto. ii; des; eauto.
    eapply Memory_lower_disj_loc_stable with (loc0 := loc0) in LOWER; eauto.
    unfold Memory.get. rewrite <- LOWER; eauto.
    ii; subst. rewrite NA_LOC in H. ss.
  - split; ii.
    eapply x0; eauto.
    eapply Memory_lower_disj_loc_stable with (loc0 := loc0) in LOWER; eauto.
    unfold Memory.get in *. rewrite LOWER; eauto.
    ii; subst. rewrite NA_LOC in H; ss.
    eapply x0 in H0; eauto.
    eapply Memory_lower_disj_loc_stable with (loc0 := loc0) in LOWER; eauto.
    unfold Memory.get in *. rewrite <- LOWER; eauto.
    ii; subst. rewrite NA_LOC in H; ss.
Qed.

Lemma Mem_at_eq_remove_na_stable
      mem_tgt loc from to msg mem_tgt' mem_src lo
      (MEM_AT_EQ: Mem_at_eq lo mem_tgt mem_src)
      (REMOVE: Memory.remove mem_tgt loc from to msg mem_tgt')
      (NA_LOC: lo loc = Ordering.nonatomic):
  Mem_at_eq lo mem_tgt' mem_src.
Proof.
  unfold Mem_at_eq in *. ii.
  exploit MEM_AT_EQ; eauto. ii. clear MEM_AT_EQ.
  unfold Mem_approxEq_loc in *. des.
  split; ii.
  - split; ii; des.
    eapply Memory_remove_disj_loc_stable
      with (loc0 := loc0) in REMOVE; eauto.
    assert (GET_TGT: Memory.get loc0 t mem_tgt =
                       Some (f, Message.concrete val R)).
    {
      unfold Memory.get in *. rewrite <- REMOVE in H0; eauto.
    }
    specialize (x f t val). des.
    exploit x; eauto.
    ii; subst. rewrite NA_LOC in H. ss.
    specialize (x f t val). des.
    exploit x1; eauto. ii; des; eauto.
    eapply Memory_remove_disj_loc_stable with (loc0 := loc0) in REMOVE; eauto.
    unfold Memory.get. rewrite <- REMOVE; eauto.
    ii; subst. rewrite NA_LOC in H. ss.
  - split; ii.
    eapply x0; eauto.
    eapply Memory_remove_disj_loc_stable with (loc0 := loc0) in REMOVE; eauto.
    unfold Memory.get in *. rewrite REMOVE; eauto.
    ii; subst. rewrite NA_LOC in H; ss.
    eapply x0 in H0; eauto.
    eapply Memory_remove_disj_loc_stable with (loc0 := loc0) in REMOVE; eauto.
    unfold Memory.get in *. rewrite <- REMOVE; eauto.
    ii; subst. rewrite NA_LOC in H; ss.
Qed.

Lemma mem_id_le_2_mem_at_eq
      mem_src mem_tgt lo
      (MEM_LE: mem_id_le mem_src mem_tgt):
  Mem_at_eq lo mem_tgt mem_src.
Proof.
  inv MEM_LE. unfold Mem_at_eq. ii.
  unfold Mem_approxEq_loc. split.
  - split; ii; des; eauto.
    eapply SOUND in H0; eauto. des; eauto.
  - ii. split; ii; eauto.
Qed.

