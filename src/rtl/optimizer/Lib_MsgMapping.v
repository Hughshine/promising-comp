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

(** * Message Mapping *)
Lemma TMapInj_lower
      inj tm tm' loc
      (CLOSED_TM: closed_TMapInj inj tm)
      (TM_INJ: TMapInj inj tm tm'):
  inj loc (tm loc) = Some (tm' loc).
Proof.
  unfold closed_TMapInj in *. specialize (CLOSED_TM loc).
  des.
  unfold TMapInj in *.
  exploit TM_INJ; eauto. ii; subst.
  eauto.
Qed.

Lemma MsgInj_add_src_concrete_prsv
      inj mem_tgt mem_src mem_src'
      loc from to msg
      (MSG_INJ: MsgInj inj mem_tgt mem_src)
      (ADD: Memory.add mem_src loc from to msg mem_src'):
  MsgInj inj mem_tgt mem_src'.
Proof.
  inv MSG_INJ. econs; eauto.
  ii. eapply SOUND in MSG; eauto. des.
  do 3 eexists. splits; eauto.
  eapply Memory.add_get1; eauto.
Qed.

Lemma inj_sc_fence_tm_closed
      sc_tgt mem_tgt sc_src mem_src inj
      (INJ_SC: TMapInj inj sc_tgt sc_src)
      (MSG_INJ: MsgInj inj mem_tgt mem_src)
      (CLOSED_SC: Memory.closed_timemap sc_tgt mem_tgt):
  Memory.closed_timemap sc_src mem_src.
Proof.
  unfold Memory.closed_timemap in *.
  ii. specialize (CLOSED_SC loc). des.
  inv MSG_INJ.
  exploit SOUND; eauto. ii; des.
  unfold TMapInj in INJ_SC. specialize (INJ_SC loc t').
  exploit INJ_SC; eauto. ii; subst.
  eauto.
Qed.
