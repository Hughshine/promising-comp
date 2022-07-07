Require Import RelationClasses.
Require Import List.

Require Import sflib.
From Paco Require Import paco.

Require Import Basic.
Require Import Axioms.
Require Import Loc.
Require Import Language.
Require Import ZArith.
Require Import FSets.
Require Import FSetInterface.
Require Import Lattice.
Require Import Event.
Require Import Syntax.
Require Import Semantics.
Require Import Kildall.

Require Import Integers.
Require Import LibTactics.
Set Implicit Arguments.

(** * Liveness Analysis *)

(** ** Neededness (liveness) for Memory Locations *)
(** Interpretation of [nmem]:
- [NMemDead]: all memory locations are unused (dead). It acts as bottom.
- [NMem locs]: all memory locations are used, except the locations in locs.
*)
Inductive nmem : Type :=
  | NMemDead
  | NMem (locs: LocSet.t). 

(** Set a location to dead (not live) *)
Definition nmem_add_dead (nm: nmem) (loc: Loc.t) :=
  match nm with
  | NMemDead => NMemDead
  (* set loc to unused *)
  | NMem locs => NMem (LocSet.add loc locs)
  end.

(** Set a location to live *)
Definition nmem_remove_dead (nm: nmem) (loc: Loc.t) :=
  match nm with
  | NMemDead => NMem LocSet.empty  (* very conservative, should never happen *)
  | NMem locs => NMem (LocSet.remove loc locs)
  end.

(** NMem lub *) 
Definition nmem_lub (nm1 nm2: nmem) :=
  match nm1 with
  | NMemDead => nm2
  | NMem locs1 => match nm2 with
                 | NMemDead => NMem locs1
                 | NMem locs2 => NMem (LocSet.inter locs1 locs2)
                 end
  end.

(** NMem beq *)
Definition nmem_beq (nm1 nm2: nmem) :=
  match nm1 with
  | NMemDead => match nm2 with
               | NMemDead => true
               | NMem locs2 => false
               end
  | NMem locs1 =>
    match nm2 with
    | NMemDead => false
    | NMem locs2 => if LocSet.eq_dec locs1 locs2 then true else false
    end
  end.

(** NMem eq *) 
Definition nmem_eq (nm1 nm2: nmem) :=
  match nm1 with
  | NMemDead => match nm2 with
               | NMemDead => True
               | NMem locs2 => False
               end
  | NMem locs1 =>
    match nm2 with
    | NMemDead => False
    | NMem locs2 => LocSet.eq locs1 locs2
    end
  end.

Lemma nmem_eq_refl (nm: nmem): nmem_eq nm nm.
Proof.
  destruct nm; ss; eauto.
Qed.

Lemma nmem_eq_sym (nm1 nm2: nmem):
  nmem_eq nm1 nm2 -> nmem_eq nm2 nm1.
Proof.
  ii.
  destruct nm1, nm2; ss; eauto.
  eapply LocSet.eq_leibniz in H; subst.
  eapply LocSet.eq_equiv.
Qed.

Lemma nmem_eq_trans (nm1 nm2 nm3: nmem):
  nmem_eq nm1 nm2 -> nmem_eq nm2 nm3 -> nmem_eq nm1 nm3.
Proof.
  destruct nm1, nm2, nm3; simpls; eauto.
  ii; tryfalse.
  introv LocEq1 LocEq2. 
  eapply LocSet.eq_leibniz in LocEq1.
  eapply LocSet.eq_leibniz in LocEq2.
  subst.
  eapply LocSet.eq_equiv.
Qed.

Lemma nmem_beq_correct (nm1 nm2: nmem):
  nmem_beq nm1 nm2 = true -> nmem_eq nm1 nm2.
Proof.
  ii. destruct nm1, nm2; ss; eauto.
  des_ifH H; eauto. tryfalse.
Qed.

(** NMem ge *) 
Definition nmem_ge (nm1 nm2: nmem) :=
  match nm1, nm2 with
  | NMemDead, NMemDead => True
  | NMemDead, NMem locs2 => False
  | NMem locs1, NMem locs2 => LocSet.Subset locs1 locs2
  | _, NMemDead => True
  end.

Lemma nmem_ge_refl (nm1 nm2: nmem):
  nmem_eq nm1 nm2 -> nmem_ge nm1 nm2.
Proof.
  ii. destruct nm1, nm2; ss; eauto.
  eapply LocSet.eq_leibniz in H. subst.
  eapply RegSet.Facts.Subset_refl.
Qed.

Lemma nmem_ge_trans (nm1 nm2 nm3: nmem):
  nmem_ge nm1 nm2 -> nmem_ge nm2 nm3 -> nmem_ge nm1 nm3.
Proof.
  destruct nm1, nm2, nm3; ss; ii; tryfalse; eauto.
Qed.

Lemma nmem_ge_lub_left (nm1 nm2: nmem):
  nmem_ge (nmem_lub nm1 nm2) nm1.
Proof.
  destruct nm1, nm2; ss.
  unfold LocSet.Subset. ii.
  eapply LocSet.Facts.inter_1; eauto.
Qed.

Lemma nmem_ge_lub_right (nm1 nm2: nmem):
  nmem_ge (nmem_lub nm1 nm2) nm2.
Proof.
  destruct nm1, nm2; ss.
  unfold LocSet.Subset. ii.
  eapply LocSet.Facts.inter_2; eauto.
Qed.

Module NREG := LPMap1(LBoolean).
Definition nreg := NREG.t.

(** ** Lattices for liveness analysis *)
(** The result of the liveness analysis of each program point is
    a pair of liveness registers [nreg] and liveness memory locations [nmem]. *)
Module LvLat <: SEMILATTICE.

  Definition t := (nreg * nmem)%type.

  Definition eq (x y: t) :=
    NREG.eq (fst x) (fst y) /\ nmem_eq (snd x) (snd y).
    
  Definition eq_refl: forall x, eq x x.
  Proof.
    unfold eq. ii. destruct x; ss. split.
    eapply NREG.eq_refl.
    eapply nmem_eq_refl.
  Qed.

  Definition eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    ii. destruct x, y; ss. unfold eq in *; ss.
    des.
    split. eapply NREG.eq_sym; eauto.
    eapply nmem_eq_sym; eauto.
  Qed.

  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq; destruct x, y, z; simpl. intros [A B] [C D]; split.
    eapply NREG.eq_trans; eauto.
    eapply nmem_eq_trans; eauto.
  Qed.

  Definition beq (x y: t): bool :=
    match x, y with
    | (nr1, nm1), (nr2, nm2) =>
      NREG.beq nr1 nr2 && nmem_beq nm1 nm2
    end.

  Definition beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold beq, eq; destruct x, y; simpl; intros.
    eapply andb_prop in H. des.
    split.
    apply NREG.beq_correct; auto.
    eapply nmem_beq_correct; eauto.
  Qed.

  Definition ge (x y: t) :=
    NREG.ge (fst x) (fst y) /\ nmem_ge (snd x) (snd y).

  Definition ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge; destruct x, y; simpl. intros [A B]; split.
    apply NREG.ge_refl; auto.
    eapply nmem_ge_refl; eauto.
  Qed.
  
  Definition ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge; destruct x, y, z; simpl. intros [A B] [C D]; split.
    eapply NREG.ge_trans; eauto. 
    eapply nmem_ge_trans with (nm2 := n2); eauto.
  Qed.

  Definition bot : t := (NREG.bot, NMemDead).

  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, bot; destruct x; simpl. split.
    eapply NREG.ge_bot.
    destruct n0; ss.
  Qed.

  Definition lub (x y: t) : t :=
    (NREG.lub (fst x) (fst y), nmem_lub (snd x) (snd y)).

  Definition ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold ge; destruct x, y; simpl; split.
    apply NREG.ge_lub_left.
    eapply nmem_ge_lub_left.
  Qed.
  
  Definition ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    unfold ge; destruct x, y; simpl; split.
    apply NREG.ge_lub_right.
    eapply nmem_ge_lub_right.
  Qed.
End LvLat.

(** Dead register: a register r is dead if [nreg] maps r to false. *)
Definition is_dead_reg (r: Reg.t) (nr: nreg) :=
  if NREG.get r nr then false else true.

(** Dead location: a location x is dead if
    - nmem is [NMemDead]; or,
    - nmem is [NMem locs] and x is in locs.  *)
Definition is_dead_loc (loc: Loc.t) (nm: nmem) :=
  match nm with
  | NMemDead => true
  | NMem locs => LocSet.mem loc locs
  end. 

(** [set_reg_dead] sets a register r in nr to a dead register. *)
Definition set_reg_dead (r: Reg.t) (nr: nreg) :=
  NREG.set r false nr.

(** [set_reg_live] sets a register r in nr to a live register. *)
Definition set_reg_live (r: Reg.t) (nr: nreg) :=
  NREG.set r true nr.

(** [set_expr_live] sets all the registers in the expression e to live registers. *)
Fixpoint set_expr_live (e: Inst.expr) (nr: nreg) :=
  match e with
  | Inst.expr_val v => nr
  | Inst.expr_reg r => set_reg_live r nr 
  | Inst.expr_op2 _ op1 op2 =>
    let nr' := set_expr_live op2 nr in set_expr_live op1 nr'                     
  end.

(** ** Transfer Function for the Single Instruction *)
(** [transf_instr] is the transfer function for a single instruction in the liveness analysis.
    It takes two parameters:
    - [instr]: the instruction;
    - [ai]: the abstract interpretation at the point after [instr].

    The return value is the abstract interpretation at the point before [instr].

    We have: [transf_instr (instr, ai)] [instr] [ai]. *)
Definition transf_instr (instr: Inst.t) (ai: LvLat.t): LvLat.t :=
  match ai with
  | (nr, nm) =>
    match instr with
    | Inst.skip => (nr, nm)
    | Inst.assign r e =>
      (* if r is dead *)
      if is_dead_reg r nr then
        (nr, nm)
      else
        (set_expr_live e (set_reg_dead r nr), nm)
    | Inst.load r loc or =>
      (* if r is dead *)
      if is_dead_reg r nr then
        (nr, nm)
      else
        (set_reg_dead r nr, nmem_remove_dead nm loc)
    | Inst.store loc e ow =>
      match ow with
      | Ordering.plain =>
        (* if location x is dead *)
        if is_dead_loc loc nm then
          (nr, nm)
        else
          (set_expr_live e nr, nmem_add_dead nm loc)
      | Ordering.relaxed
      | Ordering.strong_relaxed =>
        (set_expr_live e nr, nm)
      (** for release write, we set all memory locations to be used *)
      | Ordering.acqrel
      | Ordering.seqcst =>
        (set_expr_live e nr, NMem LocSet.empty)
      end
    | Inst.cas r loc er ew or ow =>
      if Ordering.le ow Ordering.strong_relaxed then
        (set_expr_live ew (set_expr_live er (set_reg_dead r nr)), nm)
      else
        (set_expr_live ew (set_expr_live er (set_reg_dead r nr)), NMem LocSet.empty)
    | Inst.fence_rel | Inst.fence_sc => (nr, NMem LocSet.empty)
    | Inst.fence_acq => (nr, nm)
    | Inst.print e => (set_expr_live e nr, NMem LocSet.empty)
    end
  end.

(** The liveness analysis is defined based on the pattern of the backward analysis. *)
Module LvDS := Backward_Dataflow_Solver(LvLat)(NodeSetBackward).

(** ** Transfer Function for the Basic Block in the Liveness Analysis *)
Fixpoint transf_blk (ai: LvDS.AI.t) (bb: BBlock.t) {struct bb}: LvDS.AI.b :=
  match bb with
  | BBlock.blk instr bb =>
    match transf_blk ai bb with
    | LvDS.AI.Cons ai' ai_b => LvDS.AI.Cons (transf_instr instr ai') (LvDS.AI.Cons ai' ai_b)
    | LvDS.AI.Atom ai' => LvDS.AI.Cons (transf_instr instr ai') (LvDS.AI.Atom ai')
    end
  | BBlock.jmp f => LvDS.AI.Cons ai (LvDS.AI.Atom ai)
  | BBlock.call f fret =>
    match ai with
    | (nr, nm) => LvDS.AI.Cons (nr, NMem LocSet.empty) (LvDS.AI.Atom (nr, nm))
    end
  | BBlock.be e f1 f2 =>
    match ai with
    | (nr, nm) => LvDS.AI.Cons (set_expr_live e nr, nm) (LvDS.AI.Atom (nr, nm))
    end
  | BBlock.ret => LvDS.AI.Cons (NREG.bot, NMem LocSet.empty) (LvDS.AI.Atom ai)
  end.

Definition transf (ai: LvLat.t) (bb: BBlock.t): LvLat.t := 
  LvDS.AI.getFirst (transf_blk ai bb).
    
Theorem wf_transf_blk: (* to be simplify *)
  forall b l,
    LvDS.AI.getLast (transf_blk l b) = l.
Proof.
  induction b; ii; ss; eauto; try solve [destruct l; simpls; eauto].
  destruct (transf_blk l b) eqn:Heqe; simpls.
  specialize (IHb l). rewrite Heqe in IHb. simpls. eauto.
  specialize (IHb l). rewrite Heqe in IHb. simpls. eauto.
Qed.

Lemma transf_blk_cons
      ai_tail b:
  exists ai' ai_b', transf_blk ai_tail b = LvDS.AI.Cons ai' ai_b'.
Proof.
  destruct b; ss; destruct ai_tail; ss; eauto.
  destruct (transf_blk (n, n0) b); ss; eauto.
Qed.

