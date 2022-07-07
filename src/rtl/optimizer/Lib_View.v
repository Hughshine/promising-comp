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

Require Import WFConfig.
Require Import CompAuxDef.
Require Import MemoryProps.
Require Import promiseCertifiedAux.
Require Import Mem_at_eq_lemmas.
Require Import PromiseInjectionWeak.

(** * View properties *)
Lemma view_inj_prop_pln
      inj R R' loc
      (CLOSED_VIEWINJ: closed_viewInj inj R)
      (VIEW_INJ: ViewInj inj R R'):
  inj loc (View.pln R loc) = Some (View.pln R' loc).
Proof.
  unfold closed_viewInj in *. des.
  unfold closed_TMapInj in *. specialize (CLOSED_VIEWINJ loc). des.
  unfold ViewInj in *. destruct R, R'; ss. des; ss.
  unfold TMapInj in VIEW_INJ.
  exploit VIEW_INJ; eauto. ii; subst; eauto.
Qed.

Lemma view_inj_prop_rlx
      inj R R' loc
      (CLOSED_VIEWINJ: closed_viewInj inj R)
      (VIEW_INJ: ViewInj inj R R'):
  inj loc (View.rlx R loc) = Some (View.rlx R' loc).
Proof.
  unfold closed_viewInj in *. des.
  unfold closed_TMapInj in *. specialize (CLOSED_VIEWINJ0 loc). des.
  unfold ViewInj in *. destruct R, R'; ss. des; ss.
  unfold TMapInj in VIEW_INJ0.
  exploit VIEW_INJ0; eauto. ii; subst; eauto.
Qed.

Lemma cur_na_view_message
      tview prm mem loc
      (LOCAL_WF: Local.wf (Local.mk tview prm) mem):
  exists from val R,
    Memory.get loc ((View.pln (TView.cur tview)) loc) mem = Some (from, Message.concrete val R).
Proof.
  inv LOCAL_WF; ss. inv TVIEW_CLOSED.
  inv CUR. unfold Memory.closed_timemap in PLN; ss.
Qed.

Lemma TimeMap_join_stable
      tm loc to
      (LE: Time.le to (tm loc)):
  TimeMap.join tm (TimeMap.singleton loc to) = tm.
Proof.
  unfold TimeMap.join, TimeMap.singleton.
  eapply functional_extensionality; ii.
  destruct (Loc.eq_dec loc x); subst.
  rewrite Loc_add_eq.
  unfold Time.join. des_if; eauto.
  eapply Time.le_lteq in LE. eapply Time.le_lteq in l. des; subst; eauto.
  auto_solve_time_rel. ii.
  auto_solve_time_rel.
  rewrite Loc_add_neq; eauto.
  unfold LocFun.init.
  rewrite Time_join_bot. eauto.
Qed.

Lemma View_join_stable
      view loc to
      (LE: Time.le to ((View.rlx view) loc)):
  View.join view (View.singleton_rw loc to) = view.
Proof.
  unfold View.join. destruct view; ss.
  rewrite TimeMap.join_bot.
  rewrite TimeMap_join_stable; eauto.
Qed.

Lemma read_na_cur_msg_local_stable
      lc mem loc lo
      (LOC: lo loc = Ordering.nonatomic)
      (LOCAL_WF: Local.wf lc mem):
  exists val R, 
    Local.read_step lc mem loc
                    (View.pln (TView.cur (Local.tview lc)) loc) val R Ordering.plain lc lo.
Proof.
  pose proof cur_na_view_message; eauto.
  destruct lc; ss. exploit H; eauto. instantiate (1 := loc). clear H.
  ii; des.
  exists val R.
  econs; eauto.
  rewrite LOC. ss.
  ss. econs; eauto. auto_solve_time_rel.
  ii. tryfalse.
  ss.
  unfold TView.read_tview. destruct tview; ss.
  assert (ORD1: Ordering.le Ordering.acqrel Ordering.plain = false).
  {
    eauto.
  }
  rewrite ORD1.
  assert (ORD2: Ordering.le Ordering.relaxed Ordering.plain = false).
  {
    eauto.
  }
  rewrite ORD2.
  rewrite View.join_bot_r. rewrite View.join_bot_r.
  ss.
  rewrite View_join_stable; eauto.
  rewrite View_join_stable; eauto.
  clear - LOCAL_WF.
  inv LOCAL_WF; ss. inv TVIEW_WF; ss. inv CUR_ACQ.
  unfold TimeMap.le in PLN. specialize (PLN loc).
  inv ACQ. unfold TimeMap.le in PLN_RLX. specialize (PLN_RLX loc).
  clear - PLN PLN_RLX.
  auto_solve_time_rel.
  inv LOCAL_WF; ss.
  inv TVIEW_WF; ss.
  inv CUR; ss.
Qed.

Lemma le_strongrlx_tview_read_disj_loc_cur
      tview loc to or loc' R
      (DISJ_LOC: loc <> loc')
      (LE: Ordering.le or Ordering.strong_relaxed):
  <<CUR_RLX: View.rlx (TView.cur (TView.read_tview tview loc to R or)) loc' =
             View.rlx (TView.cur tview) loc'>> /\
  <<CUR_PLN: View.pln (TView.cur (TView.read_tview tview loc to R or)) loc' =
             View.pln (TView.cur tview) loc'>>.
Proof.
  unfold TView.read_tview; ss.
  assert (ORD: Ordering.le Ordering.acqrel or = false).
  {
    destruct or; ss; eauto.
  }
  rewrite ORD.
  unfold View.singleton_ur_if; ss.
  des_if; ss.
  {
    unfold TimeMap.join, TimeMap.bot; ss.
    repeat (rewrite Time_join_bot; ss).
    unfold TimeMap.singleton.
    rewrite Loc_add_neq; eauto.
    unfold LocFun.init.
    repeat (rewrite Time_join_bot; ss).
  }
  {
    unfold TimeMap.join, TimeMap.bot; ss.
    repeat (rewrite Time_join_bot; ss).
    unfold TimeMap.singleton.
    rewrite Loc_add_neq; eauto.
    unfold LocFun.init.
    repeat (rewrite Time_join_bot; ss).
  }
Qed.

Lemma le_relacq_tview_disj_loc_cur
      tview sc loc to ow loc'
      (DISJ_LOC: loc <> loc'):
  <<CUR_RLX: View.rlx (TView.cur (TView.write_tview tview sc loc to ow)) loc' =
             View.rlx (TView.cur tview) loc'>> /\
  <<CUR_PLN: View.pln (TView.cur (TView.write_tview tview sc loc to ow)) loc' =
             View.pln (TView.cur tview) loc'>>.
Proof.
  unfold TView.write_tview; ss.
  unfold TimeMap.singleton; ss.
  destruct tview; ss. unfold TimeMap.join; ss.
  rewrite Loc_add_neq; eauto. unfold LocFun.init; ss.
  rewrite Time_join_bot. rewrite Time_join_bot.
  eauto.
Qed.

Lemma le_relacq_tview_disj_loc_acq
      tview sc loc to ow loc'
      (DISJ_LOC: loc <> loc'):
  <<ACQ_RLX: View.rlx (TView.acq (TView.write_tview tview sc loc to ow)) loc' =
             View.rlx (TView.acq tview) loc'>> /\
  <<ACQ_PLN: View.pln (TView.acq (TView.write_tview tview sc loc to ow)) loc' =
             View.pln (TView.acq tview) loc'>>.
Proof.
  unfold TView.write_tview; ss.
  unfold TimeMap.singleton; ss.
  destruct tview; ss. unfold TimeMap.join; ss.
  rewrite Loc_add_neq; eauto. unfold LocFun.init; ss.
  rewrite Time_join_bot. rewrite Time_join_bot.
  eauto.
Qed.

Lemma le_strong_relaxed_tview_disj_loc_rel
      tview sc loc to ow loc'
      (LT_REL: Ordering.le ow Ordering.strong_relaxed)
      (DISJ_LOC: loc <> loc'):
  <<REL: TView.rel (TView.write_tview tview sc loc to ow) loc' = TView.rel tview loc'>>.
Proof.
  unfold TView.write_tview; ss.
  assert (Ordering.le Ordering.acqrel ow = false).
  {
    destruct ow; ss.
  }
  rewrite H. rewrite Loc_add_neq; eauto.
Qed.
