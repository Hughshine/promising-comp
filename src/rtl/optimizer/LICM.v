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
Require Import Iteration.

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
Require Import CorrectOpt.
Require Import CSE.
Require Import Lib_Ordering.
Require Import DetLoop.
Set Implicit Arguments.

(** * The Definition of Loop Invariant Code Motion *)

(** Loop invariant code motion first uses [LInv] to detect the loop invariant and
    allocate a new register to save the result of the loop invariant,
    then uses [CSE] to eliminate the redundant reads. *)

(** ** Allocation of Pre-Header  *)
(** [alloc_ph] allocates a new block as the pre-header of the block labelled l_entry. *)
Definition alloc_inst (linv: LOOP_INV): Inst.t :=
  match linv with
  | LINV_EXPR r e => Inst.assign r e
  | LINV_LOC r loc => Inst.load r loc Ordering.plain
  end.

Fixpoint alloc_ph (loop_invs: list LOOP_INV) (l_entry: positive) : BBlock.t :=
  match loop_invs with
  | linv :: loop_invs' => (alloc_inst linv) ## (alloc_ph loop_invs' l_entry)
  | _ => BBlock.jmp l_entry
  end.

(** [consInv] adds instructions into the pre-header. *)
Fixpoint consInv (loop_invs: list LOOP_INV) (BB: BBlock.t) :=
  match loop_invs with
  | linv :: loop_invs' => consInv loop_invs' (alloc_inst linv ## BB)
  | _ => BB
  end.

(** ** Pointing to Pre-Header  *)
(** We give a mapping that records the preheader of the entry of each loop. *)
Definition pt_modify (l l_entry l_ph: positive): positive :=
  if Pos.eq_dec l l_entry then l_ph else l.

Fixpoint ptB_ph (l_ph l_entry: positive) (BB: BBlock.t) : BBlock.t :=
  match BB with
  | c ## BB' => c ## (ptB_ph l_ph l_entry BB')
  | BBlock.jmp f => BBlock.jmp (pt_modify f l_entry l_ph)
  | BBlock.be e f1 f2 => BBlock.be e (pt_modify f1 l_entry l_ph) (pt_modify f2 l_entry l_ph)
  | _ => BB
  end.

Fixpoint is_exit (l: positive) (loop_invs: list (positive * positive * list LOOP_INV)) :=
  match loop_invs with
  | (l_entry, l_exit, loopinvs) :: loop_invs' =>
    if Pos.eq_dec l l_exit then true
    else is_exit l loop_invs'
  | nil => false
  end.

Definition ptC_ph (cdhp: CodeHeap) (l_ph l_entry: positive)
         (loop_invs: list (positive * positive * list LOOP_INV)) := 
  PTree.map (fun (l: positive) (BB: BBlock.t) =>
               if is_exit l loop_invs then BB else ptB_ph l_ph l_entry BB) cdhp.

Lemma ptC_ph_dom_eq
      cdhp l_ph l_entry loop_invs l BB
      (GET: (ptC_ph cdhp l_ph l_entry loop_invs) ! l = Some BB):
  exists BB', cdhp ! l = Some BB' /\ (BB = BB' \/ BB = ptB_ph l_ph l_entry BB').
Proof.
  unfold ptC_ph in *.
  rewrite PTree.gmap in GET.
  unfold option_map in GET.
  destruct (cdhp ! l) eqn:Heqe; ss.
  exists t. split; eauto.
  des_ifH GET; ss; eauto.
  inv GET; eauto. inv GET; eauto.
Qed.

Lemma ptC_ph_dom_eq2
      cdhp l_ph l_entry loop_invs l BB
      (GET: cdhp ! l = Some BB):
  exists BB', (ptC_ph cdhp l_ph l_entry loop_invs) ! l = Some BB' /\
         (BB' = BB \/ BB' = ptB_ph l_ph l_entry BB).
Proof.
  unfold ptC_ph. rewrite PTree.gmap; eauto.
  unfold option_map. rewrite GET.
  des_if; eauto.
Qed.

(** ** Code Transformation: allocating new blocks for loop invaraints *)
Fixpoint TransC' (cdhp: CodeHeap) (preheader: PTree.t positive)
         (loop_invs loop_invs0: list (positive * positive * list LOOP_INV)) (max_p: positive):
  (CodeHeap * positive * (PTree.t positive)) :=
  match loop_invs with
  | (l_entry, l_exit, loopinvs) :: loop_invs' =>
    match PTree.get l_entry preheader with
    (* l_entry already has a pre-header *)
    | Some l_ph =>
      match (cdhp ! l_ph) with
      | Some BB_ph =>
        let BB' := consInv loopinvs BB_ph in 
        let cdhp' := PTree.set l_ph BB' cdhp in
        TransC' cdhp' preheader loop_invs' loop_invs0 max_p
      | None =>
        TransC' cdhp preheader loop_invs' loop_invs0 max_p
      end
    (* l_entry does not have a pre-header *)
    | None =>
      let BB_ph := alloc_ph loopinvs l_entry in
      let preheader' := PTree.set l_entry max_p preheader in
      let cdhp' := PTree.set max_p BB_ph (ptC_ph cdhp max_p l_entry loop_invs0) in
      TransC' cdhp' preheader' loop_invs' loop_invs0 (Pos.succ max_p)
    end
  | nil => (cdhp, max_p, preheader)
  end.

Fixpoint max_labelled_node {A: Type} (ls: list (positive * A)) (max_p: positive) :=
  match ls with
  | nil => max_p
  | (p, _) :: ls' => if (max_p <? p)%positive then
                      max_labelled_node ls' p
                    else max_labelled_node ls' max_p
  end.

Definition TransC (func: Func)
           (loop_invs: list (positive * positive * list LOOP_INV)) : Func :=
  let (cdhp, ep) := func in
  let max_p := max_labelled_node (PTree.elements cdhp) 1%positive in
  match (TransC' cdhp (PTree.empty positive) loop_invs loop_invs (Pos.succ max_p)) with
  | (cdhp', max_p', preheader) => 
    match (PTree.get ep preheader) with
    | Some ep_ph => (cdhp', ep_ph)
    | None => (cdhp', ep)
    end
  end.

Lemma max_labelled_node_prop':
  forall A (m: list (positive * A)) p0 p
    (LE: (p0 <= p)%positive),
    (p0 <= max_labelled_node m p)%positive.
Proof.
  induction m; ii; eauto; ss.
  destruct a.
  destruct ((p <? p1)%positive) eqn:Heqe; ss.
  eapply Pos.ltb_lt in Heqe.
  assert ((p0 < p1)%positive). eapply Pos.le_lt_trans; eauto.
  eapply IHm in H; eauto.
  eapply Pos.lt_le_incl; eauto.
  eapply IHm in H; eauto.
Qed.

Lemma max_lablled_node_prop:
  forall A m l (BB: A) p
    (IN: In (l, BB) m),
    (l <= max_labelled_node m p)%positive.
Proof.
  induction m; ii; ss.
  destruct a. des1.
  inv IN.
  destruct ((p <? l)%positive) eqn:Heqe; ss.
  eapply max_labelled_node_prop' in H; eauto. eapply Pos.le_refl.
  eapply max_labelled_node_prop' in H; eauto. eapply Pos.ltb_ge; eauto.
  destruct ((p <? p0)%positive) eqn:Heqe; ss.
  eapply IHm in H; eauto.
  eapply IHm in H; eauto.
Qed.

Lemma TransC'_new_allocated_prop:
  forall loopinvs0 loopinvs cdhp_s max_p cdhp_t max_p' preheader0 preheader l l'
    (TRANSC': TransC' cdhp_s preheader0 loopinvs0 loopinvs max_p = (cdhp_t, max_p', preheader))
    (PREHEADER: preheader ! l = Some l'),
    (preheader0 ! l = Some l') \/ ((max_p <= l')%positive).
Proof.
  induction loopinvs0; ii; ss; eauto.
  - inv TRANSC'. eauto.
  - destruct a. destruct p.
    destruct (preheader0 ! p) eqn:Heqe; ss.
    {
      destruct (cdhp_s ! p1) eqn:Heqe1; ss.      
      eapply IHloopinvs0 in TRANSC'; eauto.
      eapply IHloopinvs0 in TRANSC'; eauto.
    }
    {
      eapply IHloopinvs0 in TRANSC'; eauto.
      des1.
      destruct (Pos.eq_dec p l); subst.
      rewrite PTree.gss in TRANSC'. inv TRANSC'. right. eapply Pos.le_refl; eauto.
      rewrite PTree.gso in TRANSC'; eauto.
      right.
      assert (SUCC_LT: (max_p < Pos.succ max_p)%positive).
      {
        eapply Pos.lt_succ_diag_r; eauto.
      }
      eapply POrderedType.Positive_as_OT.lt_le_incl.
      eapply Pos.lt_le_trans; eauto.
    }
Qed.
    
(** ** Loop Invariant Code Motion *)
(** The implementation of [LInv],
    which detects loop invariants in the program and
    allocates a new register to save the result of loop invariants  *)
Definition LInv: Optimizer rtl_lang := 
  fun (lo: Ordering.LocOrdMap) (prog: Code) =>
  let loop_P := det_loop_invs prog lo in
  Some (PTree.map (fun (l: positive) (func: Func) =>
                     match PTree.get l loop_P with
                     | None => func
                     | Some loop_invs => TransC func loop_invs
                     end) prog).

(** The implementation of the loop invariant code motion *)
Definition licm: Optimizer rtl_lang :=
  opt_link cse_optimizer LInv.


