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
Require Import LocalSim.
Require Import MemoryMerge.

Require Import WFConfig.
Require Import CompAuxDef.
Require Import MemoryProps.
Require Import promiseCertifiedAux.
Require Import Mem_at_eq_lemmas.
Require Import PromiseInjectionWeak.

(** * Memory properties *)
Lemma Memory_get_disj_proper
      loc from1 to1 msg1 from2 to2 msg2 mem
      (GET1: Memory.get loc to1 mem = Some (from1, msg1))
      (GET2: Memory.get loc to2 mem = Some (from2, msg2))
      (LT: Time.lt to1 to2):
  Time.le to1 from2.
Proof.
  exploit Memory.get_disjoint; [eapply GET1 | eapply GET2 | eauto..].
  ii; des; subst; ss.
  auto_solve_time_rel.
  unfold Interval.disjoint in x0.
  destruct (Time.le_lt_dec to1 from2); eauto.
  specialize (x0 to1).
  exploit x0; eauto; ss.
  econs; ss; eauto.
  eapply Memory.get_ts in GET1; eauto. des; subst; ss.
  auto_solve_time_rel.
  eapply Time.le_lteq. eauto.
  econs; ss; eauto.
  eapply Time.le_lteq; eauto.
Qed.

Lemma Memory_get_disj_proper2
      loc from1 to1 msg1 from2 to2 msg2 mem
      (GET1: Memory.get loc to1 mem = Some (from1, msg1))
      (GET2: Memory.get loc to2 mem = Some (from2, msg2))
      (LT: Time.lt from1 to2)
      (NEQ: to1 <> to2):
  Time.le to1 from2.
Proof.
  exploit Memory.get_disjoint; [eapply GET1 | eapply GET2 | eauto..].
  ii; des; subst; ss; eauto.
  unfold Interval.disjoint in x0.
  destruct (Time.le_lt_dec to1 from2); eauto.
  destruct (Time.le_lt_dec to1 to2).
  {
    specialize (x0 to1).
    exploit x0; ss; eauto.
    econs; ss; eauto.
    eapply Memory.get_ts in GET1.
    des; subst. auto_solve_time_rel.
    eauto.
    eapply Time.le_lteq. eauto.
  }
  {
    specialize (x0 to2).
    exploit x0; eauto; ss.
    econs; ss; eauto. eapply Time.le_lteq. eauto.
    econs; ss; eauto.
    eapply Memory.get_ts in GET2. des; subst.
    auto_solve_time_rel.
    eauto.
    eapply Time.le_lteq. eauto.
  }
Qed.

Lemma Memory_get_disj_proper3
      loc from1 to1 msg1 from2 to2 msg2 mem
      (GET1: Memory.get loc to1 mem = Some (from1, msg1))
      (GET2: Memory.get loc to2 mem = Some (from2, msg2))
      (LT: Time.lt to1 to2):
  Time.le from1 from2.
Proof.
  exploit Memory_get_disj_proper; [eapply GET1 | eapply GET2 | eauto..].
  introv LE.
  eapply memory_get_ts_le in GET1. auto_solve_time_rel.
Qed.

Lemma RSV_ITV_insert_middle_not_attach
      to1 to2 mem loc
      (LE: Time.lt to1 to2)
      (RSV_ITV: forall ts, Interval.mem (to1, to2) ts -> ~ Cover.covered loc ts mem)
      (NOT_ATTACH: attatched_time mem loc (Time.middle to1 to2)):
  False.
Proof.
  unfold attatched_time in NOT_ATTACH. des.
  destruct (Time.le_lt_dec to2 to').
  {
    specialize (RSV_ITV to2).
    eapply RSV_ITV; eauto. econs; ss; eauto. eapply Time.le_lteq; eauto.
    econs; eauto.
    econs; ss; eauto.
    eapply Time.middle_spec in LE. des; eauto.
  }
  {
    specialize (RSV_ITV to'). eapply RSV_ITV; eauto.
    econs; ss; eauto.
    eapply Memory.get_ts in GET. des; subst; ss.
    eapply Time.middle_spec in LE. des.
    rewrite GET in LE. clear - LE. auto_solve_time_rel.
    eapply Time.middle_spec in LE. des.
    clear - LE GET. auto_solve_time_rel.
    eapply Time.le_lteq. eauto.
    econs; eauto.
    econs; ss; eauto.
    eapply Memory.get_ts in GET. des; subst.
    eapply Time.middle_spec in LE. des.
    clear - LE GET. rewrite GET in LE. auto_solve_time_rel.
    eauto.
    eapply Time.le_lteq. eauto.
  }
Qed.

Lemma concrete_cover_prsv
      from to loc ts to' val R mem mem'
      (CONCRETE_COVER: forall ts, Interval.mem (from, to) ts ->
                             LocalSim.concrete_covered loc ts mem)
      (ADD: Memory.add mem loc to to' (Message.concrete val R) mem')
      (ITV: Interval.mem  (from, to') ts):
  LocalSim.concrete_covered loc ts mem'.
Proof.
  inv ITV; ss.
  destruct (Time.le_lt_dec ts to); subst.
  - exploit CONCRETE_COVER; eauto.
    instantiate (1 := ts). econs; eauto.
    ii. inv x.
    econs; eauto.
    instantiate (1 := R0). instantiate (1 := val0).
    eapply Memory.add_get1; eauto.
  - exploit Memory.add_get0; eauto. ii; des.
    econs; eauto. econs; eauto.
Qed.

Lemma concrete_covered_merge
      to1 to2 to3 loc mem ts
      (CONCRETE_COVER1: forall ts,
          Interval.mem (to1, to2) ts -> LocalSim.concrete_covered loc ts mem)
      (CONCRETE_COVER2: forall ts,
          Interval.mem (to2, to3) ts -> LocalSim.concrete_covered loc ts mem)
      (ITV: Interval.mem (to1, to3) ts):
  LocalSim.concrete_covered loc ts mem.
Proof.
  inv ITV; ss.
  destruct (Time.le_lt_dec ts to2).
  {
    eapply CONCRETE_COVER1; eauto. econs; eauto.
  }
  {
    eapply CONCRETE_COVER2; eauto. econs; eauto.
  }
Qed.

Lemma next_concrete_ext_loc:
  forall dom mem loc to
      (FINITE_MEM: forall ts f msg, Memory.get loc ts mem = Some (f, msg) -> In ts dom),
    (exists nxt_ts f0 val0 R0, Time.lt to nxt_ts /\
                          Memory.get loc nxt_ts mem = Some (f0, Message.concrete val0 R0) /\
                          (forall t' f' val' R',
                              Memory.get loc t' mem = Some (f', Message.concrete val' R') -> t' <> nxt_ts ->
                              (Time.le t' to \/ Time.lt nxt_ts t'))) \/
    (forall t' f' val' R', Memory.get loc t' mem = Some (f', Message.concrete val' R') -> Time.le t' to).
Proof.
  induction dom; ii; ss.
  - right. ii. exploit FINITE_MEM; eauto. ii; ss.
  - renames a to to0.
    destruct (Memory.get loc to0 mem) eqn:GET.
    + destruct p as (from0 & msg0).
      destruct msg0.
      {
        exploit Memory.remove_exists; eauto. ii; des.
        assert (IN_DOM_PROGRESS: forall from to msg,
                   Memory.get loc to mem2 = Some (from, msg) -> In to dom).
        {
          ii.
          erewrite Memory.remove_o in H; eauto.
          des_ifH H; ss.
          eapply FINITE_MEM in H; eauto. des; eauto; ss.
          subst. ss.
        }
        specialize (IHdom mem2 loc to).
        exploit IHdom; eauto. clear IN_DOM_PROGRESS. introv IN_DOM_PROGRESS.
        des.
        {
          destruct (Time.le_lt_dec to0 to).

          left.
          exists nxt_ts f0 val0 R0.
          split; eauto.
          split.
          erewrite Memory.remove_o in IN_DOM_PROGRESS0; eauto.
          des_ifH IN_DOM_PROGRESS0; ss; eauto.
          ii.
          destruct (Time.eq_dec to0 t'); subst; eauto.
          eapply IN_DOM_PROGRESS1; eauto.
          instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
          erewrite Memory.remove_o; eauto. des_if; ss; eauto. des; subst; ss.
          
          destruct (Time.le_lt_dec to0 nxt_ts).
          left.
          exists to0 from0 val released.
          split; eauto.
          split; eauto.
          ii.
          destruct (Time.eq_dec to0 t'); subst; eauto; ss.
          assert (GET': Memory.get loc t' mem2 = Some (f', Message.concrete val' R')).
          {
            erewrite Memory.remove_o; eauto.
            des_if; ss; des; subst; ss.
          }
          destruct (Time.eq_dec t' nxt_ts); subst.
          clear - l l0 n. eapply Time.le_lteq in l0; ss.
          des; subst; eauto. ss.
          eapply IN_DOM_PROGRESS1 in GET'; eauto.
          des; eauto.
          clear - l0 GET'. right. auto_solve_time_rel.

          left.
          exists nxt_ts f0 val0 R0.
          split; eauto. split; eauto.
          erewrite Memory.remove_o in IN_DOM_PROGRESS0; eauto.
          des_ifH IN_DOM_PROGRESS0; ss.
          ii.
          destruct (Time.eq_dec to0 t'); subst; eauto; ss.
          eapply IN_DOM_PROGRESS1; eauto.
          instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
          erewrite Memory.remove_o; eauto. des_if; ss; eauto. des; subst; ss.
        }
        {
          destruct (Time.le_lt_dec to0 to).
          right.
          ii.
          destruct (Time.eq_dec t' to0); subst; eauto.
          eapply IN_DOM_PROGRESS; eauto.
          instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
          erewrite Memory.remove_o; eauto.
          des_if; ss; subst; des; ss.
          left.
          exists to0 from0 val released.
          split; eauto.
          split; eauto.
          ii.
          left.
          eapply IN_DOM_PROGRESS; eauto.
          instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
          erewrite Memory.remove_o; eauto.
          des_if; ss; des; subst; ss.
        }
      }
      {
        exploit Memory.remove_exists; eauto. ii; des.
        assert (IN_DOM_PROGRESS: forall from to msg,
                   Memory.get loc to mem2 = Some (from, msg) -> In to dom).
        {
          ii.
          erewrite Memory.remove_o in H; eauto.
          des_ifH H; ss.
          eapply FINITE_MEM in H; eauto. des; subst; ss; eauto.
        }
        specialize (IHdom mem2 loc to).
        exploit IHdom; eauto. clear IN_DOM_PROGRESS. introv IN_DOM_PROGRESS.
        des.
        {
          left.
          exists nxt_ts f0 val0 R0.
          split; eauto.
          split. erewrite Memory.remove_o in IN_DOM_PROGRESS0; eauto.
          des_ifH IN_DOM_PROGRESS0; ss.
          ii.
          eapply IN_DOM_PROGRESS1; eauto.
          instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
          erewrite Memory.remove_o; eauto.
          des_if; ss; des; subst; ss.
          rewrite GET in H. ss.
        }
        {
          right.
          ii.
          eapply IN_DOM_PROGRESS.
          instantiate (3 := f'). instantiate (2 := val'). instantiate (1 := R').
          erewrite Memory.remove_o; eauto.
          des_if; ss; des; subst; ss.
          rewrite GET in H. ss.
        }
      }
    + assert (IN_DOM_PROGRESS: forall from to msg,
                   Memory.get loc to mem = Some (from, msg) -> In to dom).
      {
        ii. lets GET': H.
        eapply FINITE_MEM in H; eauto. des; eauto.
        inv H; ss.
        rewrite GET in GET'; ss.
      }
      specialize (IHdom mem loc to).
      exploit IHdom; eauto.
Qed.

Lemma next_concrete_ext_loc0:
  forall mem loc to,
    (exists nxt_ts f0 val0 R0, Time.lt to nxt_ts /\
                          Memory.get loc nxt_ts mem = Some (f0, Message.concrete val0 R0) /\
                          (forall t' f' val' R',
                              Memory.get loc t' mem = Some (f', Message.concrete val' R') -> t' <> nxt_ts ->
                              (Time.le t' to \/ Time.lt nxt_ts t'))) \/
    (forall t' f' val' R', Memory.get loc t' mem = Some (f', Message.concrete val' R') -> Time.le t' to).
Proof.
  ii.
  assert (exists dom, forall ts f msg, Memory.get loc ts mem = Some (f, msg) -> In ts dom).
  {
    exploit Cell.finite; eauto. instantiate (1 := (mem loc)). ii; des.
    exists dom. ii. eauto.
  }
  des.
  eapply next_concrete_ext_loc; eauto.
Qed.

Lemma memory_add_concrete_mem_incr
      mem loc from to msg mem'
      (ADD: Memory.add mem loc from to msg mem'):
  concrete_mem_incr mem mem'.
Proof.
  unfold concrete_mem_incr; ii.
  exists f R. split. eapply View.View.opt_le_PreOrder_obligation_1; eauto.
  split; eauto. eapply Time.le_lteq; eauto.
  split; eauto. erewrite Memory.add_get1; eauto.
  ii. inv H0; ss. auto_solve_time_rel.
Qed.

Lemma memory_split_concrete_mem_incr
      mem loc from to ts val R msg' mem'
      (SPLIT: Memory.split mem loc from to ts (Message.concrete val R) msg' mem'):
  concrete_mem_incr mem mem'.
Proof.
  unfold concrete_mem_incr; ii.
  exploit Memory.split_get1; eauto. ii; des.
  exists f' R0.
  split; eauto.
  eapply View.View.opt_le_PreOrder_obligation_1; eauto.
  split; eauto.
  split; eauto.
  ii.
  destruct (Loc.eq_dec loc loc0); subst.
  {
    destruct (Time.eq_dec t ts); subst.
    {
      exploit Memory.split_get0; [eapply SPLIT | eauto..]. ii; des.
      rewrite H in GET0. inv GET0.
      rewrite GET3 in GET2. inv GET2.
      econs; eauto.
    }
    {
      assert (Memory.get loc0 t mem' = Some (f, Message.concrete val0 R0)).
      erewrite Memory.split_o; eauto.
      des_if; ss; des; subst; ss; eauto.
      exploit Memory.split_get0; [eapply SPLIT | eauto..]. ii; des.
      rewrite H in GET. ss.
      des_if; ss; des; subst; ss; eauto.
      rewrite GET2 in H1. inv H1. inv H0; ss.
      assert (Time.lt f f). auto_solve_time_rel.
      auto_solve_time_rel.
    }
  }
  {
    assert (Memory.get loc0 t mem' = Some (f, Message.concrete val0 R0)).
    erewrite Memory.split_o; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    des_if; ss; des; subst; ss; eauto.
    rewrite GET2 in H1. inv H1. inv H0; ss.
    assert (Time.lt f f). auto_solve_time_rel.
    auto_solve_time_rel.
  }
Qed.

Lemma memory_lower_concrete_mem_incr
      mem loc from to msg msg' mem'
      (LOWER: Memory.lower mem loc from to msg msg' mem'):
  concrete_mem_incr mem mem'.
Proof.
  unfold concrete_mem_incr. ii.
  exploit Memory.lower_get1; [eapply LOWER | eapply H | eauto..]. ii; des.
  inv MSG_LE.
  exists f released.
  split; eauto.
  split; eauto.
  auto_solve_time_rel.
  split; eauto.
  ii. inv H0; ss.
  auto_solve_time_rel.
Qed.

Lemma memory_cancel_concrete_mem_incr
      mem loc from to mem'
      (ADD: Memory.remove mem loc from to Message.reserve mem'):
  concrete_mem_incr mem mem'.
Proof.
  unfold concrete_mem_incr. ii.
  exists f R.
  splits; eauto.
  eapply View.View.opt_le_PreOrder_obligation_1; eauto.
  auto_solve_time_rel.
  erewrite Memory.remove_o; eauto.
  des_if; eauto. simpl in a. des1; subst.
  exploit Memory.remove_get0; eauto. i. des1.
  rewrite H in GET. ss.
  introv ITV. inv ITV; ss.
  auto_solve_time_rel.
Qed.

Fixpoint dom_rm (dom: list Time.t) (to: Time.t) :=
  match dom with
  | nil => nil
  | to' :: dom' => if Time.eq_dec to to' then dom' else (to' :: dom_rm dom' to)
  end.

Lemma dom_rm_in_length_reduce:
  forall dom to n
    (LEN: length dom = S n)
    (IN: In to dom),
    length (dom_rm dom to) = n.
Proof.
  induction dom; ii; ss.
  des; subst; ss.
  inv LEN. des_if; eauto; ss.
  inv LEN.
  destruct dom. ss.
  simpl in IHdom.
  exploit IHdom; eauto. ii.
  des_ifH x; subst; eauto.
  des_if; eauto; ss.
  des_if; eauto; ss.
  des_if; eauto; ss.
  des_if; eauto; ss.
Qed.

Lemma dom_rm_stable:
  forall dom ts to
    (IN_DOM: In ts dom)
    (NEQ: ts <> to),
    In ts (dom_rm dom to).
Proof.
  induction dom; ii; ss.
  des; subst; ss; eauto.
  des_if; subst; ss; eauto.
  des_if; subst; ss; eauto.
Qed.

Lemma find_first_unused_timestamps':
  forall n dom loc val from to R val' from' to' R' to_r mem
    (IN_DOM: forall ts f msg, Memory.get loc ts mem = Some (f, msg) -> In ts dom)
    (LEN: length dom = n)
    (GET1: Memory.get loc to mem = Some (from, Message.concrete val R))
    (GET2: Memory.get loc to' mem = Some (from', Message.concrete val' R'))
    (LT1: Time.lt to to')
    (LT2: Time.lt to_r from')
    (NO_CCOVER: forall ts, Interval.mem (to_r, from') ts -> ~ Cover.covered loc ts mem)
    (NO_RSVs: forall ts f, Memory.get loc ts mem = Some (f, Message.reserve) -> False),
  exists from1 to1 val1 R1 to2,
    Memory.get loc to1 mem = Some (from1, Message.concrete val1 R1) /\
    Time.lt to1 to2 /\
    Time.le to to1 /\
    (forall ts, Interval.mem (to, to1) ts -> LocalSim.concrete_covered loc ts mem) /\
    (forall ts, Interval.mem (to1, to2) ts -> ~ Cover.covered loc ts mem) /\
    Time.le to2 from'.
Proof.
  induction n; ii.
  - destruct dom; ss; tryfalse.
    exploit IN_DOM; eauto. ii; ss.
  - exploit next_concrete_ext_loc; eauto. 
    instantiate (1 := to). ii; des.
    {
      (* next message exists *)
      destruct (Time.le_lt_dec f0 to).
      {
        (* f0 <= to *)
        eapply Time.le_lteq in l. des.

        (* f0 < to: contradiction *)
        exploit Memory.get_disjoint; [eapply GET1 | eapply x1 | eauto..].
        ii; des; subst. auto_solve_time_rel.
        unfold Interval.disjoint in x3.
        specialize (x3 to). exploit x3; eauto.
        eapply Memory.get_ts in GET1. des; subst. clear - l. auto_solve_time_rel.
        econs; eauto. ss. eapply Time.le_lteq; eauto.
        econs; eauto. ss. eapply Time.le_lteq; eauto.
        ii; ss.

        (* f0 = to: attach *)
        subst. 
        assert (LEN': length (dom_rm dom to) = n).
        {
          exploit IN_DOM; [eapply GET1 | eauto..]. introv IN_DOM'.
          eapply dom_rm_in_length_reduce; eauto.
        }
        exploit Memory.remove_exists; [eapply GET1 | eauto..].
        introv REMOVE_MEM. des.
        assert (GET': Memory.get loc nxt_ts mem2 = Some (to, Message.concrete val0 R0)).
        {
          erewrite Memory.remove_o; eauto.
          des_if; ss; eauto. des; subst; ss. auto_solve_time_rel.
        }
        assert (GET'': Memory.get loc to' mem2 = Some (from', Message.concrete val' R')).
        {
          erewrite Memory.remove_o; eauto.
          des_if; ss; des; subst; ss; eauto.
          auto_solve_time_rel.
        }
        exploit IHn; [| eapply LEN' | eapply GET' | eapply GET'' | eauto..].
        {
          ii.
          erewrite Memory.remove_o in H; eauto.
          des_ifH H; ss. des; ss.
          eapply IN_DOM in H.
          eapply dom_rm_stable; eauto.
        } 
        {
          destruct (Time.le_lt_dec nxt_ts to').
          {
            eapply Time.le_lteq in l. des; subst; eauto.
            rewrite GET2 in x1. inv x1.
            specialize (NO_CCOVER to).
            exploit NO_CCOVER; eauto; ss. econs; eauto; ss. eapply Time.le_lteq; eauto.
            econs. eapply GET1. econs; ss; eauto.
            eapply Memory.get_ts in GET1. des; subst; ss.
            auto_solve_time_rel.
            eapply Time.le_lteq; eauto.
          }
          {
            eapply x2 in GET2; eauto. des; try solve [auto_solve_time_rel].
            ii; subst. auto_solve_time_rel.
          }
        }
        {
          clear - NO_CCOVER REMOVE_MEM. ii.
          eapply Cover.remove_covered in REMOVE_MEM; eauto. des.
          exploit REMOVE_MEM; eauto.
          ii; des; ss. eapply NO_CCOVER in H; eauto.
        }
        {
          introv GET_RSV.
          erewrite Memory.remove_o in GET_RSV; eauto.
          des_ifH GET_RSV; ss; eauto.
        }

        ii; des.
        exists from1 to1 val1 R1 to2. 
        split.
        {
          erewrite Memory.remove_o in x; eauto.
          des_ifH x; des; ss.
        }
        split; eauto.
        split; eauto.
        {
          eapply Time.le_lteq. left.
          auto_solve_time_rel.
        }
        split; eauto.
        { 
          introv ITV.
          exploit Interval.mem_split. eapply ITV.
          instantiate (1 := nxt_ts). econs; eauto. 
          ii; des; eauto.
          {
            econs. eapply x1. eauto.
          }
          {
            eapply x5 in x9.
            inv x9.
            erewrite Memory.remove_o in CONCRETE_MSG; eauto.
            des_ifH CONCRETE_MSG; des; ss; eauto.
            econs; eauto.
          }
        }
        split; eauto.
        {
          introv ITV COVER. 
          exploit x6; eauto.
          inv COVER. inv ITV; ss.
          econs. 2: eapply ITV0.
          instantiate (1 := msg).
          erewrite Memory.remove_o; eauto.
          des_if; ss; des; subst; ss.
          inv ITV0; ss. 
          clear - x0 x4 FROM TO0.
          cut (Time.lt to to1). ii.
          cut (Time.lt to ts). ii. auto_solve_time_rel.
          auto_solve_time_rel. auto_solve_time_rel.
        }
      } 
      {
        (* to < f0: find the solution *)
        exists from to val R f0.
        split; eauto. split; eauto. split. eapply Time.le_lteq; eauto.
        split.
        ii. inv H; ss. auto_solve_time_rel.
        split; eauto.
        ii. inv H; ss. inv H0.
        destruct msg.

        destruct (Time.eq_dec to0 nxt_ts); subst.
        rewrite x1 in GET. inv GET.
        inv ITV; ss. clear - TO FROM0. auto_solve_time_rel.
        lets GET': GET.
        eapply x2 in GET; eauto. des.
        inv ITV; ss.
        cut (Time.le ts to). ii.
        clear - FROM H. auto_solve_time_rel. auto_solve_time_rel.
        assert (LE: Time.le nxt_ts from0).
        {
          clear - x1 GET' GET x0.
          exploit Memory.get_disjoint; [eapply x1 | eapply GET' | eauto..].
          ii; des; subst; ss.
          auto_solve_time_rel.
          unfold Interval.disjoint in x2.
          destruct (Time.le_lt_dec nxt_ts from0); eauto.
          specialize (x2 nxt_ts).
          exploit x2; eauto; ss.
          eapply Memory.get_ts in x1; eauto.
          des; subst; ss.
          auto_solve_time_rel.
          econs; ss; eauto. eapply Time.le_lteq; eauto.
          econs; ss; eauto. eapply Time.le_lteq; eauto.
        }
        assert (LT': Time.lt ts nxt_ts).
        { 
          clear - x1 TO l.
          eapply Memory.get_ts in x1; eauto. des; subst; ss.
          auto_solve_time_rel. auto_solve_time_rel.
        }
        assert (GT: Time.lt nxt_ts ts).
        {
          clear - ITV LE. inv ITV; ss.
          auto_solve_time_rel.
        }
        clear - LT' GT. auto_solve_time_rel.
        ii. auto_solve_time_rel.

        eapply NO_RSVs in GET; ss.

        destruct (Time.eq_dec nxt_ts to'); subst.
        {
          rewrite GET2 in x1. inv x1. auto_solve_time_rel.
        }
        {
          destruct (Time.le_lt_dec f0 from'); eauto.
          destruct (Time.le_lt_dec to' f0).
          {
            lets GET_RSV: GET2.
            eapply x2 in GET2; eauto. des.
            auto_solve_time_rel.
            exploit Memory_get_disj_proper; [eapply x1 | eapply GET_RSV | eauto..].
            introv LE.
            clear - x1 LE.
            eapply Memory.get_ts in x1. des; subst; ss.
            eapply Time.le_lteq. left. auto_solve_time_rel.
          }
          {
            exploit Memory_get_disj_proper2; [eapply x1 | eapply GET2 | eauto..].
            introv LE.
            cut (Time.le f0 nxt_ts). introv LE2. clear - LE2 LE.
            auto_solve_time_rel.
            eapply memory_get_ts_le; eauto.
          }
        }
      }
    }
    {
      (* next does not exist: contradiction *)
      eapply x0 in GET2. clear - GET2 LT1. auto_solve_time_rel.
    }
Qed.

Lemma find_first_unused_timestamps:
  forall loc val from to R val' from' to' R' to_r mem
    (GET1: Memory.get loc to mem = Some (from, Message.concrete val R))
    (GET2: Memory.get loc to' mem = Some (from', Message.concrete val' R'))
    (LT1: Time.lt to to')
    (LT2: Time.lt to_r from')
    (NO_CCOVER: forall ts, Interval.mem (to_r, from') ts -> ~ Cover.covered loc ts mem)
    (NO_RSVs: forall ts f, Memory.get loc ts mem = Some (f, Message.reserve) -> False),
  exists from1 to1 val1 R1 to2,
    <<LAST_ATTACH: Memory.get loc to1 mem = Some (from1, Message.concrete val1 R1)>> /\
    <<RSV: Time.lt to1 to2 >> /\
    <<IS_LAST: Time.le to to1>> /\
    <<CONCRETE_COVER: forall ts, Interval.mem (to, to1) ts -> LocalSim.concrete_covered loc ts mem>> /\
    <<RSV_ITV: forall ts, Interval.mem (to1, to2) ts -> ~ Cover.covered loc ts mem>> /\
    <<LE_NXT: Time.le to2 from'>>.
Proof.
  ii.
  assert (exists dom, forall ts f msg, Memory.get loc ts mem = Some (f, msg) -> In ts dom).
  {
    exploit Cell.finite; eauto. instantiate (1 := (mem loc)). ii; des.
    exists dom. ii. eauto.
  }
  des.
  eapply find_first_unused_timestamps'; eauto.
Qed.

Lemma find_first_unused_timestamps_general':
  forall n dom loc val from to R mem
    (IN_DOM: forall ts f msg, Memory.get loc ts mem = Some (f, msg) -> In ts dom)
    (LEN: length dom = n)
    (GET1: Memory.get loc to mem = Some (from, Message.concrete val R))
    (NO_RSVs: forall ts f, Memory.get loc ts mem = Some (f, Message.reserve) -> False),
  exists from1 to1 val1 R1 to2,
    Memory.get loc to1 mem = Some (from1, Message.concrete val1 R1) /\
    Time.lt to1 to2 /\
    Time.le to to1 /\
    (forall ts, Interval.mem (to, to1) ts -> LocalSim.concrete_covered loc ts mem) /\
    (forall ts, Interval.mem (to1, to2) ts -> ~ Cover.covered loc ts mem).
Proof.
  induction n; ii.
  - destruct dom; ss; tryfalse.
    eapply IN_DOM in GET1. ss.
  - exploit next_concrete_ext_loc; eauto.
    instantiate (1 := to). ii; des.
    {
      (* next message exists *)
      exploit Memory_get_disj_proper; [eapply GET1 | eapply x1 | eauto..]. introv LE.
      eapply Time.le_lteq in LE. des.
      {
        (* not attach, find the answer *)
        exists from to val R f0.
        split; eauto. split; eauto.
        split. eapply Time.le_lteq. eauto.
        split.
        introv ITV. inv ITV; ss. cut (Time.lt ts ts). ii. auto_solve_time_rel. auto_solve_time_rel.
        introv ITV COVER. inv ITV; ss. inv COVER; ss.

        destruct (Time.eq_dec nxt_ts to0); subst.
        {
          rewrite x1 in GET. inv GET. inv ITV; ss.
          clear - TO FROM0. auto_solve_time_rel.
        }
        {
          destruct msg; ss.

          (* not reservation *)
          exploit x2; eauto. ii; des. inv ITV; ss.
          clear - FROM x TO0. cut (Time.le ts to). introv LE.
          clear - FROM LE. auto_solve_time_rel.
          auto_solve_time_rel.
          inv ITV; ss.
          exploit Memory_get_disj_proper3; [eapply x1 | eapply GET | eauto..]. introv LE'.
          clear - TO LE' FROM0.
          cut (Time.lt f0 ts). introv LT. auto_solve_time_rel.
          auto_solve_time_rel.

          (* reservation *)
          eapply NO_RSVs in GET; eauto.
        }
      }
      {
        (* attach *)
        subst f0.
        assert (LEN': length (dom_rm dom to) = n).
        {
          exploit IN_DOM; [eapply GET1 | eauto..]. introv IN_DOM'.
          eapply dom_rm_in_length_reduce; eauto.
        }
        exploit Memory.remove_exists; [eapply GET1 | eauto..].
        introv REMOVE_MEM. des.
        assert (GET': Memory.get loc nxt_ts mem2 = Some (to, Message.concrete val0 R0)).
        {
          erewrite Memory.remove_o; eauto.
          des_if; ss; eauto. des; subst; ss. auto_solve_time_rel.
        }
        exploit IHn; [| eapply LEN' | eapply GET' | eauto..].
        {
          ii.
          erewrite Memory.remove_o in H; eauto.
          des_ifH H; ss. des; ss.
          eapply IN_DOM in H.
          eapply dom_rm_stable; eauto.
        } 
        {
          introv GET_RSV.
          erewrite Memory.remove_o in GET_RSV; eauto.
          des_ifH GET_RSV; ss; eauto.
        }

        ii; des.
        exists from1 to1 val1 R1 to2.
        split.
        {
          erewrite Memory.remove_o in x; eauto.
          des_ifH x; des; ss.
        }
        split; eauto.
        split; eauto.
        {
          eapply Time.le_lteq. left.
          auto_solve_time_rel.
        }
        split; eauto.
        {
          introv ITV.
          exploit Interval.mem_split. eapply ITV.
          instantiate (1 := nxt_ts). econs; eauto. 
          ii; des; eauto.
          {
            econs. eapply x1. eauto.
          }
          {
            eapply x5 in x8.
            inv x8.
            erewrite Memory.remove_o in CONCRETE_MSG; eauto.
            des_ifH CONCRETE_MSG; des; ss; eauto.
            econs; eauto.
          }
        }
        {
          introv ITV COVER. 
          exploit x6; eauto.
          inv COVER. inv ITV; ss.
          econs. 2: eapply ITV0.
          instantiate (1 := msg).
          erewrite Memory.remove_o; eauto.
          des_if; ss; des; subst; ss.
          inv ITV0; ss. 
          clear - x0 x4 FROM TO0.
          cut (Time.lt to to1). ii.
          cut (Time.lt to ts). ii. auto_solve_time_rel.
          auto_solve_time_rel. auto_solve_time_rel.
        }
      }
    }
    {
      (* next message does not exists *)
      assert (MAX_MSG: forall t' f' msg', Memory.get loc t' mem = Some  (f', msg') -> Time.le t' to).
      {
        introv GET_MSG. destruct msg'; ss; eauto.
        eapply NO_RSVs in GET_MSG. ss.
      }

      exists from to val R (Time.incr to).
      split; eauto. split. eapply Time.incr_spec.
      split. eapply Time.le_lteq. eauto.
      split. introv ITV. inv ITV; ss. auto_solve_time_rel.
      introv ITV COVER. inv ITV; ss. inv COVER; ss.
      eapply MAX_MSG in GET; eauto. inv ITV; ss.
      cut (Time.le ts to). introv LE. clear - FROM LE. auto_solve_time_rel.
      auto_solve_time_rel.
    }
Qed.

Lemma find_first_unused_timestamps_general:
  forall loc val from to R mem
    (GET1: Memory.get loc to mem = Some (from, Message.concrete val R))
    (NO_RSVs: forall ts f, Memory.get loc ts mem = Some (f, Message.reserve) -> False),
  exists from1 to1 val1 R1 to2,
    <<LAST_ATTACH: Memory.get loc to1 mem = Some (from1, Message.concrete val1 R1)>> /\
    <<RSV: Time.lt to1 to2 >> /\
    <<IS_LAST: Time.le to to1>> /\
    <<CONCRETE_COVER: forall ts, Interval.mem (to, to1) ts -> LocalSim.concrete_covered loc ts mem>> /\
    <<RSV_ITV: forall ts, Interval.mem (to1, to2) ts -> ~ Cover.covered loc ts mem>>.
Proof.
  ii.
  assert (exists dom, forall ts f msg, Memory.get loc ts mem = Some (f, msg) -> In ts dom).
  {
    exploit Cell.finite; eauto. instantiate (1 := (mem loc)). ii; des.
    exists dom. ii. eauto.
  }
  des.
  eapply find_first_unused_timestamps_general'; eauto.
Qed.

Lemma Mem_at_eq_na_step_prsv_aux
      lang lo e1 e2 m m2
      (NA_STEP: @Thread.na_step lang lo e1 e2)
      (ATOMIC_COVER: Mem_at_eq lo (Thread.memory e1) m)
      (MEM: m2 = Thread.memory e2):
  Mem_at_eq lo m2 m.
Proof.
  eapply Mem_at_eq_na_step_prsv in NA_STEP; eauto.
  subst.
  eauto.
Qed.

Lemma not_cover_attach_contr
      loc to from mem msg from' to'
      (GET: Memory.get loc to mem = Some (from, msg))
      (NOT_COVER: forall ts,
          Interval.mem (from', to') ts ->
          ~ Cover.covered loc ts mem)
      (LT: Time.lt from to)
      (ITV1: Time.le from' from)
      (ITV2: Time.lt from to'):
  False.
Proof.
  destruct (Time.le_lt_dec to to'); subst.
  - specialize (NOT_COVER to).
    eapply NOT_COVER; eauto.
    econs; ss; eauto. auto_solve_time_rel.
    econs; eauto.
    econs; eauto. ss.
    eapply Time.le_lteq; eauto.
  - specialize (NOT_COVER to').
    eapply NOT_COVER; eauto.
    econs; ss; eauto. auto_solve_time_rel.
    eapply Time.le_lteq; eauto.
    econs; eauto.
    econs; eauto.
    ss. eapply Time.le_lteq; eauto.
Qed.

(** Memory lemmas *)
Lemma concrete_prm_local_write_noadd
      loc to lc lc' from' l val R' sc sc' mem mem' kind f t v lo releasedr releasedw ord
      (WRITE: Local.write_step lc sc mem l f t v releasedr releasedw ord lc' sc' mem' kind lo)
      (GET: Memory.get loc to (Local.promises lc') = Some (from', Message.concrete val R')):
  exists from R, Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val R) /\
              Time.le from from' /\ View.opt_le R' R.
Proof.
  inv WRITE; ss. inv WRITE0; ss. inv PROMISE; ss.
  - (* memory add *)
    exploit MemoryMerge.add_remove; [eapply PROMISES | eapply REMOVE | eauto..].
    i; subst. do 2 eexists. splits; eauto.
    auto_solve_time_rel. eapply View.View.opt_le_PreOrder_obligation_1; eauto.
  - (* memory split *)
    des; subst. inv RESERVE.
    erewrite Memory.remove_o in GET; eauto.
    des_ifH GET; ss. des1; ss.
    {
      erewrite Memory.split_o in GET; eauto.
      des_ifH GET; ss. des1; subst; ss. des1; subst; ss.
      {
        des_ifH GET; ss. des1; subst; ss.
        do 2 eexists. splits; eauto.
        auto_solve_time_rel.
        eapply View.View.opt_le_PreOrder_obligation_1; eauto.
      }
      {
        des_ifH GET; ss. des1. subst; ss.
        do 2 eexists. splits; eauto.
        auto_solve_time_rel.
        eapply View.View.opt_le_PreOrder_obligation_1; eauto.
      }
    }
    {
      erewrite Memory.split_o in GET; eauto.
      des_ifH GET; ss. des1; subst; ss. des1; subst; ss.
      {
        des_ifH GET; ss.
        {
          des1; subst. inv GET. exploit Memory.split_get0; [eapply PROMISES | eauto..].
          i. do 3 des1.
          do 2 eexists. split; eauto. exploit split_succeed_wf; eauto.
          i. do 3 des1. split; eauto. eapply Time.le_lteq; eauto.
          eapply View.View.opt_le_PreOrder_obligation_1; eauto.
        }
        {
          do 2 eexists. splits; eauto.
          auto_solve_time_rel. eapply View.View.opt_le_PreOrder_obligation_1; eauto.
        }
      }
      {
        des_ifH GET; ss.
        {
          des1; subst. inv GET. exploit Memory.split_get0; [eapply PROMISES | eauto..].
          i. do 3 des1.
          do 2 eexists. split; eauto. exploit split_succeed_wf; eauto.
          i. do 3 des1. split; eauto. eapply Time.le_lteq; eauto.
          eapply View.View.opt_le_PreOrder_obligation_1; eauto.
        }
        {
          do 2 eexists. splits; eauto.
          auto_solve_time_rel. eapply View.View.opt_le_PreOrder_obligation_1; eauto.
        }
      }
    }
  - (* memory lower *)
    des; subst.
    erewrite Memory.remove_o in GET; eauto. des_ifH GET; ss.
    erewrite Memory.lower_o in GET; eauto. des_ifH GET; ss.
    {
      des; subst; ss.
    }
    do 2 eexists. splits; eauto.
    auto_solve_time_rel. eapply View.View.opt_le_PreOrder_obligation_1; eauto.
Qed.
