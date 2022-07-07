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

(** Auxilary lemmas for premises clean-up or memory step reasoning *)

Lemma nonatomic_or_atomic
      or:
  or = Ordering.plain \/ or <> Ordering.plain.
Proof.
  destruct or; eauto; try solve [right; ii; ss].
Qed.

Lemma split_or_non_split:
  forall kind, 
  (exists ts3 msg3, kind = Memory.op_kind_split ts3 msg3) \/ (forall ts3 msg3, kind <> Memory.op_kind_split ts3 msg3).
Proof.
  destruct kind; eauto; try solve [right; ii; ss].
Qed.


Theorem cse_wf_transform_func:
  forall lo code_src code_tgt fid cdhp_src fentry, 
    cse_optimizer lo code_src = Some code_tgt
    -> 
    code_src!fid = Some (cdhp_src, fentry)
    -> 
    (exists cdhp_tgt,
      code_tgt ! fid = Some (cdhp_tgt, fentry)).
Proof.
    intros.
    pose proof H.
    unfold cse_optimizer in H. 
    inv H. unfold transform_prog. rewrite PTree.gmap.
    unfolds Coqlib.option_map. rewrite H0. 
    unfolds transform_func. 
    remember ((AveDS.analyze_program code_src succ AveLat.top Ave_B.transf_blk) ! fid) as afunc.
    destruct afunc.
    2: { 
      exists cdhp_src. eapply f_equal. trivial. 
    }
    unfolds transform_cdhp. 
    eexists.
    eapply f_equal.
    econs.
Qed.

Theorem cse_wf_transform_cdhp: 
  forall cdhp_src ai cdhp_tgt f b_src ,
  transform_cdhp cdhp_src ai = cdhp_tgt
  -> 
  cdhp_src ! f = Some b_src
  -> 
  exists b_tgt,
  cdhp_tgt ! f = Some b_tgt
.
Proof.
  intros.
  unfolds transform_cdhp.
  rewrite <- H.
  eexists.
  rewrite PTree.gmap; unfolds Coqlib.option_map.
  rewrite H0. econs.
Qed.

Theorem cse_wf_transform_cdhp_reverse: 
  forall cdhp_src ai cdhp_tgt f b_tgt,
  transform_cdhp cdhp_src ai = cdhp_tgt
  -> 
  cdhp_tgt ! f = Some b_tgt
  -> 
  exists b_src,
  cdhp_src ! f = Some b_src
.
Proof.
  intros.
  unfolds transform_cdhp.
  rewrite <- H in H0.
  rewrite PTree.gmap in H0. unfolds Coqlib.option_map.
  destruct (cdhp_src ! f); try discriminate; eauto.
Qed.

Theorem cse_wf_transform_blk:
  forall lo code_src code_tgt fid f cdhp_src fentry blk_src, 
    cse_optimizer lo code_src = Some code_tgt
    -> 
    code_src ! fid = Some (cdhp_src, fentry)
    -> 
    cdhp_src ! f = Some blk_src
    -> 
    (exists cdhp_tgt blk_tgt,
      code_tgt ! fid = Some (cdhp_tgt, fentry) /\ cdhp_tgt ! f = Some blk_tgt).
Proof.
    intros.
    pose proof H.
    unfold cse_optimizer in H. inv H. unfold transform_prog. rewrite PTree.gmap.
    unfolds Coqlib.option_map. rewrite H0. 
    unfolds transform_func. 
    remember ((AveDS.analyze_program code_src succ AveLat.top Ave_B.transf_blk) ! fid) as afunc.
    destruct afunc.
    2: { 
      exists cdhp_src. 
      eexists. splits; eauto.
    }

    unfolds transform_cdhp. 
    eexists. eexists.
    splits; try econs.
    rewrite PTree.gmap; unfold Coqlib.option_map.
    rewrite H1. econs.
Qed.

Lemma rlx_read_step_keep_na_cur_pln: 
forall lc mem loc loc' ts val released or lc' lo,
    Local.read_step lc mem loc ts val released or lc' lo
    -> 
    (or = Ordering.relaxed \/ or = Ordering.strong_relaxed)
    -> 
    loc <> loc'
    ->
    lo loc' = Ordering.nonatomic
    ->
    View.pln (TView.cur (Local.tview lc)) loc' =
    View.pln (TView.cur (Local.tview lc')) loc'.
Proof.
    intros.
    inv H.
    destruct H0 as [RELAXED|RELAXED].
    - rewrite RELAXED. simpl.
    replace (Ordering.le Ordering.acqrel Ordering.relaxed) with false; trivial.
    replace (Ordering.le Ordering.relaxed Ordering.relaxed) with true; trivial.
    rewrite TimeMap.join_bot.
    unfold View.singleton_ur_if.
    unfold View.singleton_ur. simpl.
    pose proof (@TimeMap.add_spec_neq loc' loc ts (View.pln (TView.cur (Local.tview lc)))).
    eapply loc_neq_sym in H1.
    pose proof H1.
    apply H in H1.
    unfold TimeMap.get in *.
    rewrite <- H1.
    inv READABLE.
    unfold TimeMap.add.
    des_ifs.

    assert (TimeMap.join (View.pln (TView.cur (Local.tview lc))) (TimeMap.singleton loc ts)
    loc' = View.pln (TView.cur (Local.tview lc)) loc'). {
        unfold TimeMap.join.
        unfold TimeMap.singleton.
        rewrite  Loc_add_neq; eauto.
        unfold LocFun.init.
        rewrite Time_join_bot. eauto.
    }
    rewrite H3. 

    unfold TimeMap.get.
    trivial. 
    -  rewrite RELAXED. simpl.
    replace (Ordering.le Ordering.acqrel Ordering.strong_relaxed) with false; trivial.
    replace (Ordering.le Ordering.relaxed Ordering.strong_relaxed) with true; trivial.
    rewrite TimeMap.join_bot.
    unfold View.singleton_ur_if.
    unfold View.singleton_ur. simpl.
    pose proof (@TimeMap.add_spec_neq loc' loc ts (View.pln (TView.cur (Local.tview lc)))).
    eapply loc_neq_sym in H1.
    pose proof H1.
    apply H in H1.
    unfold TimeMap.get in *.
    rewrite <- H1.
    inv READABLE.
    unfold TimeMap.add.
    des_ifs.

    assert (TimeMap.join (View.pln (TView.cur (Local.tview lc))) (TimeMap.singleton loc ts)
    loc' = View.pln (TView.cur (Local.tview lc)) loc'). {
        unfold TimeMap.join.
        unfold TimeMap.singleton.
        rewrite  Loc_add_neq; eauto.
        unfold LocFun.init.
        rewrite Time_join_bot. eauto.
    }
    rewrite H3. 

    unfold TimeMap.get.
    trivial. 
Qed.

Lemma fence_rel_step_keep_na_cur_rlx: 
forall lc loc lc' sc sc' lo,
    Local.fence_step lc sc Ordering.relaxed Ordering.acqrel lc' sc'
    ->
    lo loc = Ordering.nonatomic
    ->
    View.rlx (TView.cur (Local.tview lc)) loc =
    View.rlx (TView.cur (Local.tview lc')) loc.
Proof. 
  intros.
  inv H.
  simpls.
  replace (Ordering.le Ordering.acqrel Ordering.strong_relaxed) with false; trivial.
Qed.

Lemma fence_rel_step_keep_na_cur_pln: 
forall lc loc lc' sc sc' lo,
    Local.fence_step lc sc Ordering.relaxed Ordering.acqrel lc' sc'
    ->
    lo loc = Ordering.nonatomic
    ->
    View.pln (TView.cur (Local.tview lc)) loc =
    View.pln (TView.cur (Local.tview lc')) loc.
Proof.
  intros.
  inv H.
  simpls.
  replace (Ordering.le Ordering.acqrel Ordering.strong_relaxed) with false; trivial.
Qed. 

Lemma rlx_read_step_keep_na_cur_rlx: 
forall lc mem loc loc' ts val released or lc' lo,
    Local.read_step lc mem loc ts val released or lc' lo
    -> 
    (or = Ordering.relaxed \/ or = Ordering.strong_relaxed)
    -> 
    loc <> loc'
    ->
    lo loc' = Ordering.nonatomic
    ->
    View.rlx (TView.cur (Local.tview lc)) loc' =
    View.rlx (TView.cur (Local.tview lc')) loc'.
Proof.
    intros.
    inv H.
    destruct H0 as [RELAXED|RELAXED].
    - rewrite RELAXED. simpl.
    replace (Ordering.le Ordering.acqrel Ordering.relaxed) with false; trivial.
    replace (Ordering.le Ordering.relaxed Ordering.relaxed) with true; trivial.
    rewrite TimeMap.join_bot.
    unfold View.singleton_ur_if.
    unfold View.singleton_ur. simpl.
    pose proof (@TimeMap.add_spec_neq loc' loc ts (View.rlx (TView.cur (Local.tview lc)))).
    eapply loc_neq_sym in H1.
    pose proof H1.
    apply H in H1.
    unfold TimeMap.get in *.
    rewrite <- H1.
    inv READABLE.
    unfold TimeMap.add.
    des_ifs.

    assert (TimeMap.join (View.rlx (TView.cur (Local.tview lc))) (TimeMap.singleton loc ts)
    loc' = View.rlx (TView.cur (Local.tview lc)) loc'). {
        unfold TimeMap.join.
        unfold TimeMap.singleton.
        rewrite  Loc_add_neq; eauto.
        unfold LocFun.init.
        rewrite Time_join_bot. eauto.
    }
    rewrite H3. 

    unfold TimeMap.get.
    trivial. 
    -  rewrite RELAXED. simpl.
    replace (Ordering.le Ordering.acqrel Ordering.strong_relaxed) with false; trivial.
    replace (Ordering.le Ordering.relaxed Ordering.strong_relaxed) with true; trivial.
    rewrite TimeMap.join_bot.
    unfold View.singleton_ur_if.
    unfold View.singleton_ur. simpl.
    pose proof (@TimeMap.add_spec_neq loc' loc ts (View.rlx (TView.cur (Local.tview lc)))).
    eapply loc_neq_sym in H1.
    pose proof H1.
    apply H in H1.
    unfold TimeMap.get in *.
    rewrite <- H1.
    inv READABLE.
    unfold TimeMap.add.
    des_ifs.

    assert (TimeMap.join (View.rlx (TView.cur (Local.tview lc))) (TimeMap.singleton loc ts)
    loc' = View.rlx (TView.cur (Local.tview lc)) loc'). {
        unfold TimeMap.join.
        unfold TimeMap.singleton.
        rewrite  Loc_add_neq; eauto.
        unfold LocFun.init.
        rewrite Time_join_bot. eauto.
    }
    rewrite H3. 

    unfold TimeMap.get.
    trivial. 
Qed.

Lemma construct_incr_inj1:
forall inj inj' loc to,
    (exists mem, eq_ident_mapping inj mem) ->
    inj' = (fun (loc1 : Loc.t) (to1 : Time.t) => if loc_ts_eq_dec (loc, to) (loc1, to1) then Some to else inj loc1 to1) ->
    incr_inj inj inj'.
Proof. intros.
    destruct H as (mem & MAP).
    inv MAP. 
    unfolds incr_inj.
    intros.
    rewrite H0.
    des_ifs; simpls. 
    destruct a; simpls.
    rewrite <- H3 in H0.
    apply H1 in H0. rewrite H0. trivial.
Qed.

Theorem remove_keeps_promises_injected:
forall inj loc from to msg promises promises',
  mem_injected inj promises ->
  Memory.remove promises loc from to msg promises' ->
  mem_injected inj promises'.
Proof.
  intros.
  unfolds mem_injected.
  intros.
  pose proof H0 as MEM.
  eapply Memory.remove_o with (l:=loc0) (t:=t) in H0; eauto.
  rewrite H0 in MSG.
  des_ifH H0; simpls.
  econs; try discriminate.
  eapply Memory.remove_o with (l:=loc0) (t:=t) in MEM; eauto.
  Unshelve. trivial.  
Qed.


Theorem prm_add_incr_mem_with_inj:
forall inj inj' mem mem' loc from to msg promises promises' kind,
  mem_inj_dom_eq inj mem ->
  Memory.promise promises mem loc from to msg
             promises' mem' kind ->
  kind = Memory.op_kind_add ->
  msg <> Message.reserve ->
  inj' =
    (fun (loc1 : Loc.t) (to1 : Time.t) =>
    if loc_ts_eq_dec (loc, to) (loc1, to1)
    then Some to
    else inj loc1 to1) ->
  mem_inj_dom_eq inj' mem'.
Proof.
  intros.
  inv H0; try discriminate.
  inversion H.
  econs; eauto.
  { (** mem -> inj *)
    intros.
    eapply Memory.add_o with (l:=loc0) (t:=t) in MEM; eauto.
    des_ifH MEM; simpls.
    { (** [loc0 t] is newly insert*)
      destruct a.
      exists t.
      des_ifs; simpls.
      destruct o; try contradiction.
    }
    { (** [loc0 t] in inj *)
      destruct o.
      {
        des_ifs; simpls.
        destruct a; subst; try contradiction.
        rewrite MEM in MSG.
        apply SOUND in MSG.
        trivial.
      }
      {
        des_ifs; simpls.
        destruct a; subst; try contradiction.
        rewrite MEM in MSG.
        apply SOUND in MSG.
        trivial.
      }
    }
  }
  { (** inj -> mem *)
    intros.
    eapply Memory.add_o with (l:=loc0) (t:=t) in MEM; eauto.
    des_ifH MEM; simpls.
    {
      inversion TS.
      {
        destruct a.
        subst; eauto.
      }
      {
        rewrite H3 in H2. contradiction.
      }
    }
    {
      destruct o.

      {
        des_ifH INJ; simpls.
        destruct a; subst; try contradiction.
        rewrite MEM. eapply COMPLETE; eauto.
      }
      {
        des_ifH INJ; simpls.
        destruct a; subst; try contradiction.
        rewrite MEM. eapply COMPLETE; eauto.
      }
    }
  }
Qed.

Theorem prm_split_incr_mem_with_inj:
forall inj inj' mem mem' loc from to to' msg msg' promises promises' kind,
  mem_inj_dom_eq inj mem ->
  Memory.promise promises mem loc from to msg
             promises' mem' kind ->
  kind = Memory.op_kind_split to' msg' ->
  msg <> Message.reserve ->
  inj' =
    (fun (loc1 : Loc.t) (to1 : Time.t) =>
    if loc_ts_eq_dec (loc, to) (loc1, to1)
    then Some to
    else inj loc1 to1) ->
  mem_inj_dom_eq inj' mem'.
Proof.
  intros.
  inv H0; try discriminate.
  inversion H.
  econs; eauto.
  { 
    intros.
    pose proof MEM as MEM'.
    eapply Memory.split_o with (l:=loc0) (t:=t)  in MEM; eauto.
      des_ifH MEM; simpls.
    { (** [loc0 t] is newly insert*)
      destruct a.
      exists t.
      des_ifs; simpls.
      destruct o; try contradiction.
    }
    { (** [loc0 t] in inj *)
      destruct o.
      {
        des_ifs; simpls.
        {eexists; eauto. }
        {eexists; eauto. }
        destruct a; subst; try contradiction.
        rewrite MEM in MSG.
        apply SOUND in MSG.
        trivial.
      }
      {
        des_ifs; simpls.
        {eexists; eauto. }
        {eexists; eauto. }
        destruct a; subst; try contradiction.
        destruct o; try contradiction.
        {
          eapply Memory.split_get0 in MEM'.
          destruct MEM' as (_ & M & _ & _).
          apply SOUND in M; trivial.
        }
        {
          rewrite MEM in MSG.
          apply SOUND in MSG. trivial.
        }
      }
    }
  }
  {
    intros.
    pose proof MEM as MEM'.
    eapply Memory.split_o with (l:=loc0) (t:=t)  in MEM; eauto.
      des_ifH MEM; simpls.
    { (** [loc0 t] is newly insert*)
      destruct RESERVE as (v' & R' & M).
      rewrite M in MEM. do 3 eexists; eauto.
    }
    { (** [loc0 t] in inj *)
      destruct o.
      {
        des_ifs; simpls.
        { destruct a. subst. contradiction.  }
        { destruct a. subst. contradiction.  }
        destruct a; subst; try contradiction.
        rewrite MEM.
        apply COMPLETE in INJ.
        trivial.
      }
      {
        des_ifs; simpls.
        { destruct a. subst. contradiction.  }        
        { destruct a. subst. contradiction.  }
        destruct a; subst; try contradiction.
        destruct o; try contradiction.
        {
          eapply Memory.split_get0 in MEM'.
          destruct MEM' as (_ & _ & _ & M).
          destruct RESERVEORIGINAL as (v' & R' & M').
          rewrite M' in M.
          do 3 eexists; eauto.
        }
        {
          rewrite MEM .
          apply COMPLETE in INJ. trivial.
        }
      }
    }
  }
Qed.


Theorem promise_resv_preserve_mem_inj_dom_eq:
forall msg inj mem mem' prm prm' kind from loc to,
  msg = Message.reserve ->
  mem_inj_dom_eq inj mem
  ->
  Memory.promise prm mem loc from to msg
              prm' mem' kind
  ->
  mem_inj_dom_eq inj mem'.
Proof.
  intros.
  rewrite H in H1.
  inv H1.
  { (** add *)
    inversion MEM.
    inversion H0.
    econs.
    {
        intros. 
        eapply Memory.add_o with (l:=loc0) (t:=t) in MEM; eauto.
        des_ifH MEM; simpls.
        { rewrite MEM in MSG. try discriminate. }
        { rewrite MEM in MSG.
          apply SOUND in MSG. trivial.
        }
    }
    {
      intros. 
      eapply COMPLETE in INJ.
      destruct INJ as (val & f & R & MSG).
      eapply Memory.add_get1 in MEM; eauto.
    }
  }
  { (** split *)
    destruct RESERVE as (v & R & H).
    try discriminate.
  }
  { (** lower *)
    inversion MEM.
    inversion LOWER.
    destruct RESERVE as (v & R & H).
    rewrite H in MSG_LE.
    inversion MSG_LE.
  }
  { (** cancel *)
    inversion MEM.
    inversion H0.
    econs.
    {
        intros. 
        eapply Memory.remove_o with (l:=loc0) (t:=t) in MEM; eauto.
        des_ifH MEM; simpls.
        { rewrite MEM in MSG. try discriminate. }
        { rewrite MEM in MSG.
          apply SOUND in MSG. trivial.
        }
    }
    {
      intros. 
      pose proof Memory.concrete_msg_remove_rsv_stable.
      eapply COMPLETE in INJ.
      destruct INJ as (val & f & R & MSG).
      eapply H2 in MSG; eauto.
    }
  }
Qed.

Theorem incr_inj_preserve_mem_injected:
forall inj inj' mem,
  incr_inj inj inj' -> 
  mem_injected inj mem ->
  mem_injected inj' mem.
Proof.
  intros.
  unfolds incr_inj.
  unfolds mem_injected.
  intros.
  apply H0 in MSG.
  destruct MSG.
  exists x.
  apply H in H1. trivial.
Qed.

Theorem promise_ccl_keeps_promises_injected:
forall inj mem mem' loc from to msg promises promises' kind,
  mem_injected inj promises ->
  Memory.promise promises mem loc from to msg
             promises' mem' kind ->
  kind = Memory.op_kind_cancel ->
  mem_injected inj promises'.
Proof.
  intros.
  rewrite H1 in H0.
  inv H0.
  inversion PROMISES.
  unfolds mem_injected.
  intros.
  eapply Memory.remove_o with (l:=loc0) (t:=t) in PROMISES; eauto.
  rewrite PROMISES in MSG.
  des_ifH PROMISES; simpls.
  econs; try discriminate.
  eapply Memory.remove_o with (l:=loc0) (t:=t) in MEM; eauto.
  Unshelve. trivial.  
Qed.

Theorem promise_resv_keeps_promises_injected:
forall inj mem mem' loc from to msg promises promises' kind,
  mem_injected inj promises ->
  msg = Message.reserve ->
  Memory.promise promises mem loc from to msg
             promises' mem' kind ->
  mem_injected inj promises'.
Proof.
  intros.
  rewrite H0 in H1.
  inv H1.
  { (** add *)
    inversion PROMISES.
    unfolds mem_injected.
    intros.
    eapply Memory.add_o with (l:=loc0) (t:=t) in PROMISES; eauto.
    rewrite PROMISES in MSG.
    des_ifH PROMISES; simpls.
    econstructor; try discriminate. 
      { 
        apply H in MSG. trivial.  
      }
  }
  { (** split *)
    destruct RESERVE as (v & R & g).
    try discriminate.
  }
  { (** lower *)
    inversion MEM.
    inversion LOWER.
    destruct RESERVE as (v & R & G).
    rewrite G in MSG_LE.
    inversion MSG_LE.
  }
  { (** cancel *)
    inversion PROMISES.
    unfolds mem_injected.
    intros.
    eapply Memory.remove_o with (l:=loc0) (t:=t) in PROMISES; eauto.
    rewrite PROMISES in MSG.
    des_ifH PROMISES; simpls.
    econs; try discriminate.
    eapply Memory.remove_o with (l:=loc0) (t:=t) in MEM; eauto.
    Unshelve. trivial. trivial.   
  }
Qed.


Theorem prm_add_keeps_promises_injected:
forall inj inj' mem mem' loc from to msg promises promises' kind,
  mem_injected inj promises ->
  Memory.promise promises mem loc from to msg
             promises' mem' kind ->
  kind = Memory.op_kind_add ->
  inj' =
    (fun (loc1 : Loc.t) (to1 : Time.t) =>
    if loc_ts_eq_dec (loc, to) (loc1, to1)
    then Some to
    else inj loc1 to1) ->
  mem_injected inj' promises'.
Proof.
  intros.
  pose proof H0.
  unfolds mem_injected.
  inv H0; try discriminate.
  intros.
  eapply Memory.add_o with (l:=loc0) (t:=t) in PROMISES; eauto.

  des_ifH PROMISES; simpls.
  { (** for new [loc to]*) 
    destruct a.
    exists to.
    rewrite H0. rewrite H1. 
    des_ifs; simpls.
    destruct o; try contradiction.
  }
  { (** for old [loc to]*)
    rewrite PROMISES in MSG.
    apply H in MSG.
    destruct MSG. 
    exists x.
    destruct o.
    {
      des_ifs; simpls. destruct a. rewrite H2 in H1. try contradiction. 
    }
    {
      des_ifs; simpls. destruct a. rewrite H5 in H1. try contradiction. 
    }
  }
Qed.

Theorem prm_split_keeps_promises_injected:
forall inj inj' mem mem' loc from to to' msg msg' promises promises' kind,
  mem_injected inj promises ->
  Memory.promise promises mem loc from to msg
             promises' mem' kind ->
  kind = Memory.op_kind_split to' msg' ->
  inj' =
    (fun (loc1 : Loc.t) (to1 : Time.t) =>
    if loc_ts_eq_dec (loc, to) (loc1, to1)
    then Some to
    else inj loc1 to1) ->
  mem_injected inj' promises'.
Proof.
  intros.
  pose proof H0.
  unfolds mem_injected.
  inv H0; try discriminate.
  intros.
  pose proof PROMISES as PROMISES'.
  eapply Memory.split_o with (l:=loc0) (t:=t)  in PROMISES; eauto.

  des_ifH PROMISES; simpls.
  { (** for new [loc to]*) 
    destruct a.
    exists to.
    rewrite H0. rewrite H1. 
    des_ifs; simpls.
    destruct o; try contradiction.
  }
  { (** for old [loc to]*)
    rewrite PROMISES in MSG.
    des_ifH MSG; simpls.
    {
      inv MSG.
      destruct a. rewrite H0 in o; rewrite H1 in o.
      destruct o; try contradiction. inversion H4.
      eapply Memory.split_get0 in PROMISES'.
      destruct PROMISES' as (_ & M & _ & _).
      des_ifs; simpls. 
      { 
        destruct a. exists f. trivial.
      }
      {
        eapply H in M.
        trivial.
      }
    }
    apply H in MSG.
    destruct MSG. 
    exists x.
    destruct o.
    {
      des_ifs; simpls. destruct a. rewrite H2 in H1. try contradiction. 
    }
    {
      des_ifs; simpls. destruct a; destruct o0.
      rewrite H2 in H5; try contradiction.
      rewrite H4 in H1. try contradiction. 
    }
  }
Qed.


Theorem prm_lower_keeps_promises_injected:
forall inj mem mem' loc from to msg msg' promises promises' kind,
  mem_injected inj promises ->
  Memory.promise promises mem loc from to msg
             promises' mem' kind ->
  kind = Memory.op_kind_lower msg' ->
  mem_injected inj promises'.
Proof.
  intros.
  pose proof H0.
  unfolds mem_injected.
  inv H0; try discriminate.
  intros.
  pose proof PROMISES as PROMISE'.
  eapply Memory.lower_o with (l:=loc0) (t:=t) in PROMISES; eauto.
  
  des_ifH PROMISES; simpls.
  { (** for msg whose R is subst by lower *) 
    destruct a.
    (** related msg' and msg *)
    inv H2.
    eapply Memory.lower_get0 in PROMISE'. 
    destruct PROMISE' as (OLD_MSG & NEW_MSG & _).
    destruct RESERVE as (v & R' & M).
    rewrite M in OLD_MSG.
    eapply H in OLD_MSG.
    eapply Memory.lower_o with (l:=loc) (t:=to) in PROMISES0; eauto.
  }
  { (** for old [loc to]*)
    rewrite PROMISES in MSG.
    apply H in MSG. trivial.
  }
Qed.

Theorem prm_lower_keeps_mem_inj_dom_eq:
forall inj mem mem' loc from to msg msg' promises promises' kind,
  mem_inj_dom_eq inj mem ->
  Memory.promise promises mem loc from to msg
             promises' mem' kind ->
  kind = Memory.op_kind_lower msg' ->
  mem_inj_dom_eq inj mem'.
Proof.
  intros.
  inv H.
  pose proof H0.
  inv H0; try discriminate.
  intros.
  pose proof MEM as MEM'.
  destruct RESERVE as (v & R & M).
  econs.  
  { intros. 
    eapply Memory.lower_o with (l:=loc0) (t:=t) in MEM; eauto.
    des_ifH MEM; simpls.
    { (** for msg whose R is subst by lower *) 
      destruct a.
      eapply Memory.lower_get0 in MEM'. 
      destruct MEM' as (OLD_MSG & NEW_MSG & _).
      rewrite M in OLD_MSG.
      eapply SOUND in OLD_MSG. 
      rewrite <- H0 in OLD_MSG. 
      rewrite <- H1 in OLD_MSG.
      trivial. 
    }
    { (** for old [loc to]*)
      rewrite MEM in MSG.
      apply SOUND in MSG. trivial.
    }
  }
  { intros.
    eapply Memory.lower_o with (l:=loc0) (t:=t) in MEM; eauto.
    des_ifH MEM; simpls.
    { (** for msg whose R is subst by lower *) 
      destruct a.
      eapply Memory.lower_get0 in MEM'; eauto. 
      destruct MEM' as (OLD_MSG & NEW_MSG & _).
      inversion TS.
      2: {
        inversion PROMISES. inv LOWER. inv MSG_LE.
      }
      rewrite <- H2 in NEW_MSG.
      rewrite <- H0 in NEW_MSG.
      rewrite H1.
      do 3 eexists; eauto.
    }
    { (** for old [loc to]*)
      eapply Memory.lower_o with (l:=loc0) (t:=t) in MEM'; eauto.
      des_ifH MEM'; simpls.
      destruct a. subst; try tauto.
      rewrite MEM'.
      eapply COMPLETE; eauto.
    }
  }
Qed.

Theorem prm_keeps_mem_inj_dom_eq:
forall inj inj' mem mem' loc from to msg promises promises' kind,

  mem_inj_dom_eq inj mem ->
  Memory.promise promises mem loc from to msg
             promises' mem' kind ->
  msg <> Message.reserve ->
  inj' =
    (fun (loc1 : Loc.t) (to1 : Time.t) =>
    if loc_ts_eq_dec (loc, to) (loc1, to1)
    then Some to
    else inj loc1 to1) ->
  (forall (loc : Loc.t) (t t' : Time.t),
      inj loc t = Some t' -> (t = t'))->
  mem_inj_dom_eq inj' mem'.
Proof.
  intros.
  inversion H0.
  - eapply prm_add_incr_mem_with_inj; eauto.
  - eapply prm_split_incr_mem_with_inj; eauto.
  - eapply prm_lower_keeps_mem_inj_dom_eq in H0; eauto.
    assert (eq_inj inj inj'). {
      unfold eq_inj. intros.
      split.
      { intro.
        rewrite H2. des_if; simpls.
        eapply H3 in H5.
        destruct a. rewrite H7; rewrite H5. trivial.
        trivial.
      }
      { intro.
          pose proof MEM as MEM'.
          eapply Memory.lower_o with (l:=loc0) (t:=t) in MEM; eauto.

          des_ifH MEM; simpls.
          { (** for msg whose R is subst by lower *) 
            assert (t = t'). {
              rewrite H2 in H5. des_ifH H5; simpls.
              destruct a0. subst. inv H5. trivial.
              destruct a. rewrite H6 in o; rewrite H7 in o. destruct o; try contradiction.
            }
            destruct a.
            eapply Memory.lower_get0 in MEM'; eauto. 
            destruct MEM' as (OLD_MSG & NEW_MSG & _).
            inversion TS.
            destruct RESERVE as (v & R & CONCRETE).
            2: {
              inversion PROMISES. inv LOWER. inv MSG_LE. 
              destruct RESERVE as (v & R & CONCRETE); discriminate.
            }
            inversion H.
            rewrite CONCRETE in OLD_MSG.
            eapply SOUND in OLD_MSG.
            destruct OLD_MSG.
            rewrite <- H6.
            subst.
            pose proof H14.
            eapply H3 in H14.
            rewrite <- H14 in H2. 
            trivial.
          }
          {  (** for old [loc to]*)
            rewrite H2 in H5.
            des_ifH H5; simpls.
            destruct a. rewrite H6 in o; rewrite H7 in o. destruct o; try contradiction.
            trivial.
          }
        }
    }
    eapply eq_inj_implies_mem_inj_dom_eq; eauto.
  - rewrite RESERVE in H1. contradiction.
Qed.

Theorem prm_concrete_keeps_promises_injected:
forall inj inj' mem mem' loc from to promises promises' kind v released,
  (exists mem, eq_ident_mapping inj mem) ->
  mem_injected inj promises ->
  Memory.promise promises mem loc from to (Message.concrete v released)
             promises' mem' kind ->
  inj' =
    (fun (loc1 : Loc.t) (to1 : Time.t) =>
    if loc_ts_eq_dec (loc, to) (loc1, to1)
    then Some to
    else inj loc1 to1) ->
  mem_injected inj' promises'.
Proof.
  intros until released.
  intro MAP.
  intros.
  pose proof H0.
  unfolds mem_injected.
  inv H0; try discriminate.
  2: {
    eapply prm_split_keeps_promises_injected; eauto.
     }
  - 
  eapply prm_add_keeps_promises_injected; eauto.
  -
  eapply prm_lower_keeps_promises_injected; eauto. 
  unfolds mem_injected. intros.
  exists t. 
  des_if; simpls.
  * destruct a. rewrite H1. eauto.
  * destruct MAP. inv H0. 
    apply H in MSG. destruct MSG.
    pose proof H0. apply H3 in H0. rewrite <- H0 in H4. trivial.
Qed.

Lemma atomic_write_step_keep_na_cur_rlx: 
forall lc sc mem loc loc' from to  val releasedm released or lc' sc' mem' kind lo,
    Local.write_step lc sc mem loc from to val releasedm released or lc' sc' mem' kind lo
    -> 
    (or = Ordering.relaxed \/ or = Ordering.strong_relaxed \/ or = Ordering.acqrel)
    -> 
    loc <> loc'
    ->
    lo loc' = Ordering.nonatomic
    ->
    View.rlx (TView.cur (Local.tview lc)) loc' =
    View.rlx (TView.cur (Local.tview lc')) loc'.
Proof.
    intros.
    inv H.
    destruct H0 as [RELAXED|[RELAXED|ACQ]].
    - rewrite RELAXED. simpls.
    unfold TimeMap.join.
    unfold TimeMap.singleton.
    rewrite  Loc_add_neq; eauto.
    unfold LocFun.init.
    rewrite Time_join_bot. eauto.
    - rewrite RELAXED. simpls.
    unfold TimeMap.join.
    unfold TimeMap.singleton.
    rewrite  Loc_add_neq; eauto.
    unfold LocFun.init.
    rewrite Time_join_bot. eauto.
    -  rewrite ACQ. simpls.
    unfold TimeMap.join.
    unfold TimeMap.singleton.
    rewrite  Loc_add_neq; eauto.
    unfold LocFun.init.
    rewrite Time_join_bot. eauto.
Qed.
 
Lemma atomic_write_step_keep_na_cur_pln: 
forall lc sc mem loc loc' from to  val releasedm released or lc' sc' mem' kind lo,
    Local.write_step lc sc mem loc from to val releasedm released or lc' sc' mem' kind lo
    -> 
    (or = Ordering.relaxed \/ or = Ordering.strong_relaxed \/ or = Ordering.acqrel)
    -> 
    loc <> loc'
    ->
    lo loc' = Ordering.nonatomic
    ->
    View.pln (TView.cur (Local.tview lc)) loc' =
    View.pln (TView.cur (Local.tview lc')) loc'.
  Proof.
      intros.
      inv H.
      destruct H0 as [RELAXED|[RELAXED|ACQ]].
      - rewrite RELAXED. simpls.
      unfold TimeMap.join.
      unfold TimeMap.singleton.
      rewrite  Loc_add_neq; eauto.
      unfold LocFun.init.
      rewrite Time_join_bot. eauto.
      - rewrite RELAXED. simpls.
      unfold TimeMap.join.
      unfold TimeMap.singleton.
      rewrite  Loc_add_neq; eauto.
      unfold LocFun.init.
      rewrite Time_join_bot. eauto.
      -  rewrite ACQ. simpls.
      unfold TimeMap.join.
      unfold TimeMap.singleton.
      rewrite  Loc_add_neq; eauto.
      unfold LocFun.init.
      rewrite Time_join_bot. eauto.
  Qed.

Theorem incr_mem_preserve_closed_view:
forall view mem mem',
    Memory.closed_view view mem ->
    concrete_mem_incr mem mem' ->
    Memory.closed_view view mem'.
Proof.
    intros.
    unfold concrete_mem_incr in H0.
    inv H. 
    econs; eauto.
    - 
        unfolds Memory.closed_timemap. 
        intro.
        pose proof (PLN loc).
        destruct H as (f & v & R & MSG).
        eapply H0 in MSG; eauto.
        destruct MSG as (f' & R' & _ & _ & MSG' & _).
        econs; eauto.
    - 
        unfolds Memory.closed_timemap. 
        intro.
        pose proof (RLX loc).
        destruct H as (f & v & R & MSG).
        eapply H0 in MSG; eauto.
        destruct MSG as (f' & R' & _ & _ & MSG' & _).
        econs; eauto.
Qed.

Theorem incr_mem_preserve_local_wf:
  forall lc mem mem',
    Local.wf lc mem ->
    concrete_mem_incr mem mem' ->
    Memory.le (Local.promises lc) mem' -> (** why this *)
    Local.wf lc mem'.
Proof.
  intros.
  inv H.
  econs; eauto.
  clear - TVIEW_CLOSED H0.
  unfolds concrete_mem_incr.
  econs; eauto.
  - 
  intro.
  inv TVIEW_CLOSED.
  econs. 
    * 
    eapply incr_mem_preserve_closed_view; eauto.
    *     
    eapply incr_mem_preserve_closed_view; eauto.
  - 
    inv TVIEW_CLOSED.
    econs. 
    * 
    eapply incr_mem_preserve_closed_view; eauto.
    *     
    eapply incr_mem_preserve_closed_view; eauto.
  -
    inv TVIEW_CLOSED.
    econs. 
    * 
    eapply incr_mem_preserve_closed_view; eauto.
    *     
    eapply incr_mem_preserve_closed_view; eauto.
Qed. 

Lemma non_split_write_o
    l t
    mem lc sc loc from to val releasedm released mem' lc' sc' kind ord lo
    (WRITE: Local.write_step lc sc mem loc from to val releasedm released ord lc' sc' mem' kind lo)
    (NON_SPLIT: ~ (exists msg3 ts3, kind = Memory.op_kind_split ts3 msg3)):
    Memory.get l t mem' =
    if loc_ts_eq_dec (l, t) (loc, to)
    then Some (from, Message.concrete val released)
    else Memory.get l t mem.
Proof.
    intros.
    pose proof WRITE.
    eapply Local.write_step_non_cancel in H; eauto.
    inv WRITE. inv WRITE0. inv PROMISE.
    - 
    inv MEM. unfold Memory.get, LocFun.add.  
    des_if; simpls. 
    { 
        erewrite Cell.add_o; eauto.
        repeat (condtac; subst; des; ss; try congr).
    }  
    repeat (condtac; subst; des; ss; try congr).
    -   exfalso. apply NON_SPLIT. do 2 eexists; eauto.
    - 
    inv MEM. unfold Memory.get, LocFun.add.  
    des_if; simpls. 
    { 
        erewrite Cell.lower_o; eauto.
        repeat (condtac; subst; des; ss; try congr).
    }  
    repeat (condtac; subst; des; ss; try congr).
    - 
    unfolds Memory.op_kind_is_cancel. simpls. discriminate.
Qed.

Lemma split_write_o
    l t
    mem lc sc loc val ts1 ts2 ts3 msg3 releasedm released mem' lc' sc' kind ord lo
    (WRITE: Local.write_step lc sc mem loc ts1 ts2 val releasedm released ord lc' sc' mem' kind lo)
    (SPLIT: (kind = Memory.op_kind_split ts3 msg3)):
    Memory.get l t mem' =
    if loc_ts_eq_dec (l, t) (loc, ts2)
    then Some (ts1, Message.concrete val released)
    else if loc_ts_eq_dec (l, t) (loc, ts3)
         then Some (ts2, msg3)
         else Memory.get l t mem.
Proof.
    intros.
    pose proof WRITE.
    inv WRITE. inv WRITE0. inv PROMISE; try discriminate. 
    inv MEM. unfold Memory.get, LocFun.add.  
    des_if; simpls. 
    { 
        erewrite Cell.split_o; eauto.
        repeat (condtac; subst; des; ss; try congr).
    }  
    repeat (condtac; subst; des; ss; try congr).
Qed.

