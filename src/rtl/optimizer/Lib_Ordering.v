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

(** * Ordering lemmas *)
Lemma nonatomic_or_atomic
      or:
  or = Ordering.plain \/ or <> Ordering.plain.
Proof.
  destruct or; eauto; try solve [right; ii; ss].
Qed.

Lemma na_load_atomic_loc_abort
      (state: Language.state rtl_lang) local sc mem lo BB r loc
      (LOAD: State.blk state = Inst.load r loc Ordering.plain ## BB)
      (AT_LOC: lo loc = Ordering.atomic)
      (CONSISTENT: Local.promise_consistent local):
  Thread.is_abort (Thread.mk rtl_lang state local sc mem) lo.
Proof.
  destruct state; ss.
  econs; eauto.
  right. left. ss. 
  assert (exists st2, State.step (ProgramEvent.read loc Int.one Ordering.plain)
                            {| State.regs := regs; State.blk := blk; State.cdhp := cdhp;
                               State.cont := cont; State.code := code |} st2).
  { 
    exists {| State.regs := RegFun.add r Int.one regs; State.blk := BB;
         State.cdhp := cdhp; State.cont := cont; State.code := code |}.
    subst. econs; eauto.
  }
  des.
  exists st2 loc Ordering.plain Int.one.
  split; eauto. rewrite AT_LOC. ss. ii; des; ss.
Qed.

Lemma na_store_atomic_loc_abort
      (state: Language.state rtl_lang) local sc mem lo BB loc e
      (LOAD: State.blk state = Inst.store loc e Ordering.plain ## BB)
      (AT_LOC: lo loc = Ordering.atomic)
      (CONSISTENT: Local.promise_consistent local):
  Thread.is_abort (Thread.mk rtl_lang state local sc mem) lo.
Proof.
  destruct state; ss.
  econs; eauto.
  right. left. ss.
  assert (exists st2 val, State.step (ProgramEvent.write loc val Ordering.plain)
                                {| State.regs := regs; State.blk := blk; State.cdhp := cdhp;
                                   State.cont := cont; State.code := code |} st2).
  {
    do 2 eexists.
    eapply State.step_store; eauto.
  }
  des.
  exists st2 loc Ordering.plain val.
  split; eauto.
  rewrite AT_LOC. ii; ss; des; ss.
Qed.
