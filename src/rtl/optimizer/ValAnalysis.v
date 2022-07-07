Require Import RelationClasses.
Require Import List.
Require Import Omega.
Require Import sflib.
From Paco Require Import paco.
Require Import Basics.

Require Import Basic.
Require Import Axioms.
Require Import Loc.
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
Require Import Coqlib.

Require Import Integers.
Require Import LibTactics.
Set Implicit Arguments.

(** * Value Analysis *)

(** This file is the implementation of the value analysis,
    whose result is the values of registers and variables in each program point.  *)

Module LVal <: SEMILATTICE_WITH_TOP.
  Inductive t' := vtop | VAL (n:int) | vbot.
  Definition t := t'.

  Definition eq (x y:t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).

  Definition beq (x y: t): bool :=
    match x, y with
    | vtop, vtop => true
    | vbot, vbot => true
    | VAL v1, VAL v2 => if Int.eq_dec v1 v2 then true else false
    | _, _ => false
    end.

  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    ii. destruct x, y; ss.
    des_ifH H; ss. subst. econs; eauto.
  Qed.

  Definition ge (x y: t): Prop :=
    match x, y with
    | vtop, _ => true
    | _, vbot => true
    | VAL v1, VAL v2 => if Int.eq_dec v1 v2 then true else false
    | _, _ => false
    end.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    ii. destruct x, y; ss; eauto.
    unfold eq in *. inv H.
    des_if; ss; eauto. 
  Qed.

  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    ii. destruct x, y, z; ss; tryfalse; eauto.
    des_ifH H; ss; subst.
    des_ifH H0; ss; subst.
  Qed.

  Definition bot := vbot.

  Lemma ge_bot: forall x, ge x bot.
  Proof.
    ii; destruct x; ss.
  Qed.

  Definition top := vtop.

  Lemma ge_top: forall x, ge top x.
  Proof. unfold ge, top; ii; ss. Qed.

  Definition lub (x y: t): t :=
    match x, y with
    | vbot, vbot => vbot
    | VAL v1, VAL v2 => if Int.eq_dec v1 v2 then VAL v1 else vtop
    | _, _ => vtop
    end.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    ii; destruct x, y; ss.
    des_if; subst; ss; eauto.
    des_if; ss.
  Qed.

  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    ii; destruct x, y; ss.
    des_if; subst; ss; eauto.
    des_if; ss.
  Qed.
End LVal.

Module VALSET := LPMap(LVal).
Definition vreg := VALSET.t.
Definition vmem := VALSET.t.

(** ** Lattices for Value Analysis *)
(** The result of the value analysis of each program point is
    a pair of mapping, where [vreg] maps register to LVal and [vmem] maps memory location to LVal. *)
Module ValLat <: SEMILATTICE_WITH_TOP.
  
  Definition t := (vreg * vmem)%type.

  Definition eq (x y:t) :=
    VALSET.eq (fst x) (fst y) /\ VALSET.eq (snd x) (snd y).
  Definition eq_refl: forall x, eq x x.
    ii. unfold eq. ss.
  Qed.

  Definition eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    ii. unfold eq in *; ss. des.
    split; eauto; ss.
    destruct x, y; ss.
    eapply VALSET.eq_sym; eauto.
    eapply VALSET.eq_sym; eauto.
  Qed.

  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    ii. unfold eq in *; ss. des.
    split.
    eapply VALSET.eq_trans; eauto.
    eapply VALSET.eq_trans; eauto.
  Qed.

  Definition beq (x y: t): bool :=
    VALSET.beq (fst x) (fst y) && VALSET.beq (snd x) (snd y). 

  Definition beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    ii. unfold beq in *. unfold eq.
    destruct (VALSET.beq (fst x) (fst y)) eqn:VALSET_BEQ1; ss.
    split. eapply VALSET.beq_correct; eauto.
    eapply VALSET.beq_correct; eauto.
  Qed.

  Definition ge (x y: t) :=
    VALSET.ge (fst x) (fst y) /\ VALSET.ge (snd x) (snd y).

  Definition ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge; destruct x, y; simpl. intros [A B]; split; eapply VALSET.ge_refl; eauto.
  Qed.
  
  Definition ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge; destruct x, y, z; simpl.
    intros [A B] [C D]; split; eapply VALSET.ge_trans; eauto.
  Qed.

  Definition bot := (VALSET.bot, VALSET.bot).

  Lemma ge_bot: forall x, ge x bot.
  Proof.
    ii; destruct x; ss. unfold bot.
    econs; ss; eapply VALSET.ge_bot; eauto.
  Qed.

  Definition top := (VALSET.top, VALSET.top).

  Lemma ge_top: forall x, ge top x.
  Proof.
    unfold ge, top; ii; ss.
    split; eapply VALSET.ge_top; eauto.
  Qed.

  Definition lub (x y: t): t :=
    (VALSET.lub (fst x) (fst y), VALSET.lub (snd x) (snd y)).

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    ii; destruct x, y; ss.
    unfold ge; ss.
    split; eapply VALSET.ge_lub_left; eauto.
  Qed.

  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    ii; destruct x, y; ss.
    unfold ge; ss.
    split; eapply VALSET.ge_lub_right; eauto.
  Qed.
End ValLat.

Fixpoint eval_expr_ae (e: Inst.expr) (aregs: vreg) :=
  match aregs with
  | VALSET.Bot => LVal.bot
  | _ =>
    match e with
    | Inst.expr_val v => LVal.VAL v                           
    | Inst.expr_reg r => (VALSET.get r aregs)
    | Inst.expr_op2 op e1 e2 =>
      match (eval_expr_ae e1 aregs), (eval_expr_ae e2 aregs) with
      | LVal.VAL v1, LVal.VAL v2 => LVal.VAL (Op2.eval op v1 v2)
      | _, _ => LVal.top
      end
    end
  end.

Definition eval_loc_ae (loc: Loc.t) (amem: vmem) :=
  VALSET.get loc amem.

Definition mem_to_top (amem: vmem) :=
  match amem with
  | VALSET.Bot => VALSET.Bot
  | _ => VALSET.top
  end.

(** ** Transfer Function for the Single Instruction *)
Definition transf_instr (instr: Inst.t) (ae: ValLat.t): ValLat.t :=
  match ae with
  | (aregs, amem) =>
    match instr with
    | Inst.skip => (aregs, amem)
    | Inst.assign r e =>
      (VALSET.set r (eval_expr_ae e aregs) aregs, amem)
    | Inst.load r loc or =>
      if Ordering.le Ordering.acqrel or then
        (VALSET.set r LVal.top aregs, mem_to_top amem)
      else
        (VALSET.set r (eval_loc_ae loc amem) aregs, amem)
    | Inst.store loc e ow =>
      match ow with
      | Ordering.plain =>
        (aregs, VALSET.set loc (eval_expr_ae e aregs) amem)
      | _ => (aregs, amem)
      end
    | Inst.cas r loc er ew or ow =>
      if Ordering.le Ordering.acqrel or then
        (VALSET.set r LVal.top aregs, mem_to_top amem)
      else
        (VALSET.set r LVal.top aregs, VALSET.set loc LVal.top amem)
    | Inst.fence_acq | Inst.fence_sc => (aregs, mem_to_top amem)
    | Inst.fence_rel => (aregs, amem)
    | Inst.print e => (aregs, mem_to_top amem)
    end
  end.

Lemma transf_instr_bot
      instr:
  transf_instr instr ValLat.bot = ValLat.bot.
Proof.
  destruct instr; ss.
  - destruct or; ss.
  - destruct ow; ss.
  - des_if; eauto.
Qed.

Module ValDS := Dataflow_Solver(ValLat)(NodeSetForward).

(** ** Transfer Function for the Basic Block *)
Fixpoint transf_blk (ae: ValDS.L.t) (bb: BBlock.t) {struct bb}: ValDS.AI.b := 
  match bb with     
  | BBlock.blk instr bb' =>
    ValDS.AI.Cons ae (transf_blk (transf_instr instr ae) bb')
  | BBlock.call f fret => ValDS.AI.Cons ae (ValDS.AI.Atom (fst ae, mem_to_top (snd ae)))
  | _ => ValDS.AI.Cons ae (ValDS.AI.Atom ae)
  end.

Lemma transf_blk_first
      l bb:
  ValDS.AI.getFirst (transf_blk l bb) = l.
Proof.
  destruct bb; ss; eauto.
Qed.

Lemma transf_blk_bot:
      forall bb,
        ValDS.AI.getLast (transf_blk ValDS.AI.bot bb) = ValDS.AI.bot.
Proof.
  induction bb; ii; try solve [ss; eauto].
  assert (transf_blk ValDS.AI.bot (c##bb) =
          ValDS.AI.Cons (ValDS.AI.bot) (transf_blk (transf_instr c ValDS.AI.bot) bb)). eauto.
  assert (transf_instr c ValDS.AI.bot = ValDS.AI.bot).
  eapply transf_instr_bot; eauto.
  rewrite H0 in H. rewrite H.
  simpl. eauto.
Qed.

Definition transf (ai: ValDS.L.t) (bb: BBlock.t): ValDS.AI.t := 
  ValDS.AI.getLast (transf_blk ai bb).
