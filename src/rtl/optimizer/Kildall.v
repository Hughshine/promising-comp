(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Solvers for dataflow inequations. *)
(** Modification: we do optimization on bblock*)

Require Import Coqlib.
Require Import Iteration.
Require Import Maps.
Require Import Lattice.
Require Import LibTactics.
Require Import Syntax.
Require Import Language.
(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.
Require Import Basics.
(** A forward dataflow problem is a set of inequations of the form
- [X(s) >= transf n X(n)]
  if program point [s] is a successor of program point [n]
- [X(n) >= a]
  if [n] is an entry point and [a] its minimal approximation.

The unknowns are the [X(n)], indexed by program points (e.g. nodes in the
CFG graph of a RTL function).  They range over a given ordered set that
represents static approximations of the program state at each point.
The [transf] function is the abstract transfer function: it computes an
approximation [transf n X(n)] of the program state after executing instruction
at point [n], as a function of the approximation [X(n)] of the program state
before executing that instruction.

Symmetrically, a backward dataflow problem is a set of inequations of the form
- [X(n) >= transf s X(s)]
  if program point [s] is a successor of program point [n]
- [X(n) >= a]
  if [n] is an entry point and [a] its minimal approximation.

The only difference with a forward dataflow problem is that the transfer
function [transf] now computes the approximation before a program point [s]
from the approximation [X(s)] after point [s].

This file defines two solvers for dataflow problems.  The first two
solve (optimally) forward and backward problems using Kildall's worklist
algorithm.  They assume that the unknowns range over a semi-lattice, that is,
an ordered type equipped with a least upper bound operation.*)

(** * Solving forward dataflow problems using Kildall's algorithm *)

(** A forward dataflow solver has the following generic interface.
  Unknowns range over the type [L.t], which is equipped with
  semi-lattice operations (see file [Lattice]).  *)

Module AI (L: SEMILATTICE).
  Section AI.
    Definition t := L.t. (** Abstract Interpretation *)
    Definition bot := L.bot.
    Definition ge := L.ge.
    
    Inductive b' := 
    | Atom (l: t)
    | Cons (l: t) (b: b') 
    .

    Definition b := b'. (** Abstract list of a block*)
    Definition bots:b := Atom bot . (** TODO: may change this to other definition? *)
    Definition APartial := PMap.t t.
    Definition ACdhp := PMap.t (b). (** Analysis result of a codeheap *)

    (*Definition AFunc := PTree.t (b). (** Analysis result of a function *)*)
    (*Definition AThrd := PTree.t (ACdhp). (** Analysis result of a thread *)*)
    Definition AProg := PTree.t (ACdhp).

    Notation "l : b" := (Cons l b) (at level 69, right associativity).

    Definition getFirst (br: b): t :=
      match br with 
      | Atom l => l
      | l:br' => l
      end.

    Fixpoint getLast (br: b): t :=
      match br with 
      | Atom l => l
      | l:br' => getLast(br')
      end.
    
    Definition getTail (br: b): b := 
      match br with 
      | Atom _ => br
      | l:br' => br'
      end.

    Fixpoint len (br: b): nat := 
      match br with 
      | Atom l => 1
      | l:br' => 1+(len br')
      end.
    
    Theorem len_gt_zero: 
      forall b, 
        (len b) > 0. 
    Proof.
      intros. unfolds len; simpls.  
      destruct b0; eauto.   
      lia.  
    Qed.
    
    (** `br` for block result *)
    Definition In_bb (br: b): t :=
      match br with 
      | l:br' => l
      | Atom l => l
      end.
    
    Fixpoint Out_bb (br: b): t := 
      match br with 
      | Atom l => l 
      | l:b' => Out_bb b'
      end.
      
    Fixpoint br_from_i_opt (br: b) (i: nat) {struct i}: option b := 
      match i with 
      | O => Some br
      | S i' =>  
          match br with 
          | l:br' => br_from_i_opt br' i' 
          | _ => None
          end
      end.

      Definition br_from_i (br: b) (i: nat): b := 
        match br_from_i_opt br i with 
        | Some r => r
        | None => AI.Atom (getLast br)
        end.
    
    Fixpoint br_index_i (br: b) (i: nat): option t := 
      match i with 
      | O => 
        match br with 
        | l : _ => Some l
        | _ => None 
        end
      | S i' =>  
          match br with 
          | l:br' => br_index_i br i' 
          | _ => None
          end
      end.
    
    Theorem get_first_from_blk_bots:
      forall i,
      getFirst (br_from_i bots i) = bot.
    Proof.
      destruct i.
      - 
      unfolds bots.
      unfolds br_from_i; unfolds br_from_i_opt.
      unfolds getFirst; trivial.
      -
      unfolds br_from_i; unfolds br_from_i_opt.
      simpls.
      trivial.
    Qed.

    Theorem get_first_from_bots:
      forall analysis l i, 
        analysis = PMap.init bots
        -> 
        getFirst (br_from_i (analysis!!l) i) = bot. 
    Proof.
      intros.
      unfold "!!".
      rewrite H. simpls.
      rewrite PTree.gempty.
      unfolds br_from_i.
      unfolds br_from_i_opt. unfolds bots. 
      destruct i; eauto.
    Qed.

    Theorem get_first_from_eval:
    forall analysis l i eval, 
      analysis = PMap.init (Atom eval)
      -> 
      getFirst (br_from_i (analysis!!l) i) = eval. 
    Proof.
      intros.
      unfold "!!".
      rewrite H. simpls.
      rewrite PTree.gempty.
      unfolds br_from_i.
      unfolds br_from_i_opt. unfolds bots. 
      destruct i; eauto.
    Qed.

    Theorem get_head_from_eval:
    forall analysis l eval, 
      analysis = PMap.init (Atom eval)
      -> 
      getFirst (analysis!!l) = eval. 
    Proof.
      intros.
      unfold "!!".
      rewrite H. simpls.
      rewrite PTree.gempty.
      unfolds br_from_i.
      unfolds br_from_i_opt. unfolds getFirst. trivial. 
    Qed.

    Theorem get_last_from_bots:
    forall analysis l i, 
      analysis = PMap.init bots
      -> 
      getLast (br_from_i (analysis!!l) i) = bot. 
  Proof.
    intros.
    unfold "!!".
    rewrite H. simpls.
    rewrite PTree.gempty.
    unfolds br_from_i.
    unfolds br_from_i_opt. unfolds bots. 
    destruct i; eauto.
  Qed.

  Theorem get_last_from_eval:
  forall analysis l i eval, 
    analysis = PMap.init (Atom eval)
    -> 
    getLast (br_from_i (analysis!!l) i) = eval. 
  Proof.
    intros.
    unfold "!!".
    rewrite H. simpls.
    rewrite PTree.gempty.
    unfolds br_from_i.
    unfolds br_from_i_opt. unfolds bots. 
    destruct i; eauto.
  Qed.

  Theorem br_from_i_eval:
  forall i eval,
    br_from_i (Atom eval) i = Atom eval.
  Proof.
    induction i.
    intros. unfold br_from_i. unfold br_from_i_opt. trivial.
    intros. unfold br_from_i. unfold br_from_i_opt. eapply f_equal. unfold getLast. trivial.
  Qed.


  Theorem from_cons_plus:
    forall i ai ablk,
    br_from_i (Cons ai ablk) (S i) = br_from_i ablk i.
  Proof.
    induction i.
    - 
    intros.
    unfold br_from_i; unfold br_from_i_opt. trivial.
    -
    intros.  
    unfold br_from_i; unfold br_from_i_opt. simpls.
    fold br_from_i_opt.
    destruct ablk eqn:EqAblk; eauto.
  Qed.


  Theorem get_first_from_ablk_bots:
  forall i,  
    getFirst (br_from_i bots i) = bot. 
  Proof.
    intros.
    unfolds br_from_i.
    unfolds br_from_i_opt. unfolds bots.
    destruct i; eauto.
  Qed.

  Theorem get_first_from_ablk_eval:
  forall i eval,  
    getFirst (br_from_i (Atom eval) i) = eval. 
  Proof.
    intros.
    unfolds br_from_i.
    unfolds br_from_i_opt. unfolds bots.
    destruct i; eauto.
  Qed.

  Theorem get_last_from_ablk_bots:
    forall  i,  
      getLast (br_from_i bots i) = bot. 
  Proof.
    intros.
    unfolds br_from_i.
    unfolds br_from_i_opt. unfolds bots.
    destruct i; eauto.
  Qed.

  Theorem get_last_from_ablk_eval:
  forall i eval,  
    getLast (br_from_i (Atom eval) i) = eval. 
  Proof.
    intros.
    unfolds br_from_i.
    unfolds br_from_i_opt. unfolds bots.
    destruct i; eauto.
  Qed.
      
    Lemma get_tail_from_i_eq_i_plus_one:
      forall i ai,
        getTail (br_from_i ai i) = br_from_i ai (i+1).
    Proof.
      induction i.
      - intros.
        unfolds getTail. 
        simpls.
        unfold br_from_i. unfold br_from_i_opt.
        destruct ai; simpls.
        unfolds br_from_i.
        unfolds br_from_i_opt; eauto.
        unfolds br_from_i.
        unfolds br_from_i_opt; eauto.
      - 
        intros.
        unfold getTail.
        unfolds br_from_i.
        unfolds br_from_i_opt; eauto. simpls.
        destruct ai eqn:EqAi; simpls; trivial.
        folds br_from_i_opt.
        eapply (IHi b0).
    Qed.
    
    Lemma get_last_from_i_eq_i_plus_one:
      forall i ai,
        len ai > S i 
        -> 
        getLast (br_from_i ai i) = getLast (br_from_i ai (i+1)).
    Proof.
      induction i.
      - intros.
        unfolds br_from_i; unfolds br_from_i_opt. 
        unfolds bots.
        simpls.
        destruct ai eqn:Eq; eauto.
      - intros. 
        unfold br_from_i; unfold br_from_i_opt; simpls.
        destruct ai eqn:EqAI; eauto.
        unfold len in H. simpl in H.  
        assert (((fix len (br : b) : nat :=
            match br with
            | Atom _ => 1
            | _ : br' => S (len br')
            end) b0) > S i). {lia. }
        eapply IHi in H0.
        trivial.
    Qed.

    Lemma get_last_from_i_eq_from_zero:
    forall i ai,
      len ai > S i 
      -> 
      getLast (br_from_i ai i) = getLast ai.
  Proof.
    induction i.
    - intros.
      unfolds br_from_i; unfolds br_from_i_opt. 
      unfolds bots.
      simpls.
      destruct ai eqn:Eq; eauto.
    - intros. 
      unfold br_from_i; unfold br_from_i_opt; simpls.
      destruct ai eqn:EqAI; eauto.
      unfold len in H. simpl in H.  
      assert (((fix len (br : b) : nat :=
          match br with
          | Atom _ => 1
          | _ : br' => S (len br')
          end) b0) > S i). {lia. }
      eapply IHi in H0.
      trivial.
  Qed.

    Lemma br_from_i_not_atom:
    forall i ai_blk,
      len ai_blk > i + 1 ->
      forall l,
      br_from_i ai_blk i <> Atom l.
    Proof.
      induction i. 
      intros. unfolds len. unfolds br_from_i. unfolds br_from_i_opt. 
      destruct ai_blk. lia. intro. discriminate.

      intros. unfold len in H. unfold br_from_i. unfold br_from_i_opt.
      destruct ai_blk. lia. folds len. 
      assert (len ai_blk > i + 1). {lia. }
      eapply (IHi) in H0; eauto.
    Qed.

    Lemma get_i_plus_1_eq_get_last:
    forall i ai,
      len ai = i + 2 ->
      getFirst (br_from_i ai (i+1)) = getLast ai.
    Proof.
      induction i.
      -
        intros.
        unfold getFirst.
        unfold br_from_i. unfold br_from_i_opt.
        unfold getLast. 
        destruct ai eqn:EqAi; unfold len; try discriminate.
        simpl.
        destruct b0; trivial.
        unfold len in H. fold len in H.
        pose proof (len_gt_zero b0).
        lia.
      - 
        intros.
        destruct ai eqn:EqAi.
        {
          unfold len in H. lia.
        }
        unfold len in H. 
        fold len in H.
        assert (len b0 = i + 2). {lia. }
        eapply IHi in H0; eauto.
    Qed.
  End AI.
End AI.

Module Type DATAFLOW_SOLVER.
Declare Module L : SEMILATTICE.
Module AI := AI(L).

(** Should I use AI.t here? *)
(* Declare Module L: SEMILATTICE. *)

  (** [fixpoint successors transf ep ev] is the solver.
    It returns either an error or a mapping from program points to
    values of type [L.t] representing the solution.  [successors]
    is a finite map returning the list of successors of the given program
    point. [transf] is the transfer function, [ep] the entry point,
    and [ev] the minimal abstract value for [ep]. *)

  (** {A} will be BBlock of concur-rtl 
      finally, `PMap.t AI.t` will be additionally transferred into `PMap.t AI.b` 
  *)

  Parameter fixpoint:  
    forall {A: Type} (code: PTree.t A) (successors: A -> list positive)
           (transf: positive -> AI.t -> AI.t)
           (ep: positive) (ev: AI.t),
    option (PMap.t AI.t).   

  (** The [fixpoint_solution] theorem shows that the returned solution,
    if any, satisfies the dataflow inequations. *)
  Axiom fixpoint_solution:
    forall A (code: PTree.t A) successors transf ep ev res n instr s,
    fixpoint code successors transf ep ev = Some res ->
    code!n = Some instr -> In s (successors instr) ->
    (forall n, L.eq (transf n L.bot) L.bot) ->
    L.ge res!!s (transf n res!!n). 


  (** The [fixpoint_entry] theorem shows that the returned solution,
    if any, satisfies the additional constraint over the entry point. *)

  Axiom fixpoint_entry:
    forall A (code: PTree.t A) successors transf ep ev res,
    fixpoint code successors transf ep ev = Some res ->
    L.ge res!!ep ev.


  (** Finally, any property that is preserved by [L.lub] and [transf]
      and that holds for [L.bot] also holds for the results of
      the analysis. *)

  Axiom fixpoint_invariant:
    forall A (code: PTree.t A) successors transf ep ev
           (P: L.t -> Prop),
    P L.bot ->
    (forall x y, P x -> P y -> P (L.lub x y)) ->
    (forall pc instr x, code!pc = Some instr -> P x -> P (transf pc x)) ->
    P ev ->
    forall res pc,
    fixpoint code successors transf ep ev = Some res ->
    P res!!pc.

End DATAFLOW_SOLVER.

(** Kildall's algorithm manipulates worklists, which are sets of CFG nodes
  equipped with a ``pick next node to examine'' operation.
  The algorithm converges faster if the nodes are chosen in an order
  consistent with a reverse postorder traversal of the CFG.
  For now, we parameterize the dataflow solver over a module
  that implements sets of CFG nodes. *)

Module Type NODE_SET.

  Parameter t: Type.
  Parameter empty: t.
  Parameter add: positive -> t -> t.
  Parameter pick: t -> option (positive * t).
  Parameter all_nodes: forall {A: Type}, PTree.t A -> t.

  Parameter In: positive -> t -> Prop.
  Axiom empty_spec:
    forall n, ~In n empty.
  Axiom add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Axiom pick_none:
    forall s n, pick s = None -> ~In n s.
  Axiom pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Axiom all_nodes_spec:
    forall A (code: PTree.t A) n bb,
    code!n = Some bb -> In n (all_nodes code).

End NODE_SET.

(** Reachability in a control-flow graph. *)

Section REACHABLE.

Context {A: Type} (code: PTree.t A) (successors: A -> list positive).

Inductive reachable: positive -> positive -> Prop :=
  | reachable_refl: forall n, reachable n n
  | reachable_left: forall n1 n2 n3 i,
      code!n1 = Some i -> In n2 (successors i) -> reachable n2 n3 ->
      reachable n1 n3.

Scheme reachable_ind := Induction for reachable Sort Prop.

Lemma reachable_trans:
  forall n1 n2, reachable n1 n2 -> forall n3, reachable n2 n3 -> reachable n1 n3.
Proof.
  induction 1; intros.
- auto.
- econstructor; eauto.
Qed.

Lemma reachable_right:
  forall n1 n2 n3 i,
  reachable n1 n2 -> code!n2 = Some i -> In n3 (successors i) ->
  reachable n1 n3.
Proof.
  intros. apply reachable_trans with n2; auto. econstructor; eauto. constructor.
Qed.

End REACHABLE.

(** We now define a generic solver for forward dataflow inequations
  that works over any semi-lattice structure. *)

Module Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET) <: 
  DATAFLOW_SOLVER with Module L := LAT.  

Module L := LAT.
Module AI := AI(L).

Section Kildall.

Context {A: Type}.
Variable code: PTree.t A.
Variable successors: A -> list positive.
(* Variable transf_blk: positive -> AI.t -> AI.b. *)
Variable transf: positive -> AI.t -> AI.t.
(* Definition transf (n: positive) (l: AI.t): AI.t := AI.Out_bb (transf_blk n l). *)

(** The state of the iteration has three components:
- [aval]: A mapping from program points to values of type [L.t] representing
  the candidate solution found so far. Change to analysis result of block.
- [worklist]: A worklist of program points that remain to be considered.
- [visited]: A set of program points that were visited already
  (i.e. put on the worklist at some point in the past).

Only the first two components are computationally relevant.  The third
is a ghost variable used only for stating and proving invariants.
For this reason, [visited] is defined at sort [Prop] so that it is
erased during program extraction.
*)


Record state : Type :=
  mkstate { aval: PTree.t AI.t; worklist: NS.t; visited: positive -> Prop }.

Definition abstr_value (n: positive) (s: state) : AI.t :=
  match s.(aval)!n with
  | None => AI.bot
  | Some v => v
  end.

(** Kildall's algorithm, in pseudo-code, is as follows:
<<
    while worklist is not empty, do
        extract a node n from worklist
        compute out = transf n aval[n]
        for each successor s of n:
            compute in = lub aval[s] out
            if in <> aval[s]:
                aval[s] := in
                worklist := worklist union {s}
                visited := visited union {s}
            end if
        end for
    end while
    return aval
>>
*)

(** [propagate_succ] corresponds, in the pseudocode,
  to the body of the [for] loop iterating over all successors. 
  For successor `n`, we meet out with old_in, to see if fact changed
    if changed 
      then add to worklist, change state
      else unchanged.
*)

Definition propagate_succ (s: state) (out: AI.t) (n: positive) :=
  match s.(aval)!n with
  | None =>
      {| aval := PTree.set n out s.(aval);
         worklist := NS.add n s.(worklist); 
         visited := fun p => p = n \/ s.(visited) p |}
  | Some oldl =>
      let newl := L.lub oldl out in
      if L.beq oldl newl
      then s
      else {| aval := PTree.set n newl s.(aval);
              worklist := NS.add n s.(worklist);
              visited := fun p => p = n \/ s.(visited) p |}
  end.

(** [propagate_succ_list] corresponds, in the pseudocode,
  to the [for] loop iterating over all successors. *)

Fixpoint propagate_succ_list (s: state) (out: AI.t) (succs: list positive)
                             {struct succs} : state :=
  match succs with
  | nil => s
  | n :: rem => propagate_succ_list (propagate_succ s out n) out rem
  end.

(** [step] corresponds to the body of the outer [while] loop in the
  pseudocode. *)
Definition step (s: state) : PMap.t AI.t + state :=
  match NS.pick s.(worklist) with
  | None =>
      inl _ (L.bot, s.(aval))
  | Some(n, rem) =>
      match code!n with   
      | None =>
          inr _ {| aval := s.(aval); worklist := rem; visited := s.(visited) |}
      | Some instr =>
          inr _ (propagate_succ_list
                  {| aval := s.(aval); worklist := rem; visited := s.(visited) |}
                  (transf n (abstr_value n s))  
                  (successors instr))
      end
  end.

(** The whole fixpoint computation is the iteration of [step] from
  an initial state. *)
(* PrimIter.iterate
  : forall A B : Type, (A -> B + A) -> A -> option B 
                          step     entry value
  *)
Definition fixpoint_from (start: state) : option (PMap.t AI.t) :=
  PrimIter.iterate _ _ step start.

(** There are several ways to build the initial state.  For forward
  dataflow analyses, the initial worklist is the function entry point,
  and the initial mapping sets the function entry point to the given
  abstract value, and leaves unset all other program points, which
  corresponds to [L.bot] initial abstract values. *)

Definition start_state (enode: positive) (eval: AI.t) :=
  {| aval := PTree.set enode eval (PTree.empty (AI.t));
     worklist := NS.add enode NS.empty;
     visited := fun n => n = enode |}.

Definition fixpoint (enode: positive) (eval: AI.t) :=
  fixpoint_from (start_state enode eval).
(* Check PMap.map1. *)
  
(** For backward analyses (viewed as forward analyses on the reversed CFG),
  the following two variants are more useful.  Both start with an
  empty initial mapping, where all program points start at [L.bot].
  The first initializes the worklist with a given set of entry points
  in the reversed CFG.  (See the backward dataflow solver below for
  how this list is computed.)  The second start state construction
  initializes the worklist with all program points of the given CFG. *)

  Definition start_state_nodeset (enodes: NS.t) :=
    {| aval := PTree.empty AI.t;
       worklist := enodes;
       visited := fun n => NS.In n enodes |}.
  
  Definition fixpoint_nodeset (enodes: NS.t) := 
    fixpoint_from (start_state_nodeset enodes).
  
  Definition start_state_allnodes :=
    {| aval := PTree.empty AI.t;
       worklist := NS.all_nodes code;
       visited := fun n => exists instr, code!n = Some instr |}.
  
  Definition fixpoint_allnodes :=
    fixpoint_from start_state_allnodes.

(** ** Characterization of the propagation functions *)

Inductive optge: option AI.t -> option AI.t -> Prop :=
  | optge_some: forall l l',
      L.ge l l' -> optge (Some l) (Some l')
  | optge_none: forall ol,
      optge ol None.

Remark optge_refl: forall ol, optge ol ol.
Proof. destruct ol; constructor. apply L.ge_refl; apply L.eq_refl. Qed.

Remark optge_trans: forall ol1 ol2 ol3, optge ol1 ol2 -> optge ol2 ol3 -> optge ol1 ol3.
Proof.
  intros. inv H0.
  inv H. constructor. eapply L.ge_trans; eauto.
  constructor.
Qed.

Remark optge_abstr_value:
  forall st st' n,
  optge st.(aval)!n st'.(aval)!n ->
  L.ge (abstr_value n st) (abstr_value n st').
Proof.
  intros. unfold abstr_value. inv H. auto. apply L.ge_bot.
Qed.

(** propagate_succ的一些性质 *)
Lemma propagate_succ_charact:
  forall st out n,
  let st' := propagate_succ st out n in 
     optge st'.(aval)!n (Some out)
  /\ (forall s, n <> s -> st'.(aval)!s = st.(aval)!s)
  /\ (forall s, optge st'.(aval)!s st.(aval)!s)
  /\ (NS.In n st'.(worklist) \/ st'.(aval)!n = st.(aval)!n)
  /\ (forall n', NS.In n' st.(worklist) -> NS.In n' st'.(worklist))
  /\ (forall n', NS.In n' st'.(worklist) -> n' = n \/ NS.In n' st.(worklist))
  /\ (forall n', st.(visited) n' -> st'.(visited) n')
  /\ (forall n', st'.(visited) n' -> NS.In n' st'.(worklist) \/ st.(visited) n')
  /\ (forall n', st.(aval)!n' = None -> st'.(aval)!n' <> None -> st'.(visited) n').
Proof.
  unfold propagate_succ; intros; simpl.
  destruct st.(aval)!n as [v|] eqn:E;
  [predSpec L.beq L.beq_correct v (L.lub v out) | idtac].
  - (* already there, unchanged *)
    repeat split; intros.
    + rewrite E. constructor. eapply L.ge_trans. apply L.ge_refl. apply H; auto. apply L.ge_lub_right.
    + apply optge_refl.
    + right; auto.
    + auto.
    + auto.
    + auto.
    + auto.
    + congruence.
  - (* already there, updated *)
    simpl; repeat split; intros.
    + rewrite PTree.gss. constructor. apply L.ge_lub_right.
    + rewrite PTree.gso by auto. auto.
    + rewrite PTree.gsspec. destruct (peq s n).
      subst s. rewrite E. constructor. apply L.ge_lub_left.
      apply optge_refl.
    + rewrite NS.add_spec. auto.
    + rewrite NS.add_spec. auto.
    + rewrite NS.add_spec in H0. intuition.
    + auto.
    + destruct H0; auto. subst n'. rewrite NS.add_spec; auto.
    + rewrite PTree.gsspec in H1. destruct (peq n' n). auto. contradiction.
  - (* not previously there, updated *)
    simpl; repeat split; intros.
    + rewrite PTree.gss. apply optge_refl.
    + rewrite PTree.gso by auto. auto.
    + rewrite PTree.gsspec. destruct (peq s n).
      subst s. rewrite E. constructor.
      apply optge_refl.
    + rewrite NS.add_spec. auto.
    + rewrite NS.add_spec. auto.
    + rewrite NS.add_spec in H. intuition.
    + auto.
    + destruct H; auto. subst n'. rewrite NS.add_spec. auto.
    + rewrite PTree.gsspec in H0. destruct (peq n' n). auto. congruence.
Qed.

Lemma propagate_succ_list_charact:
  forall out l st,
  let st' := propagate_succ_list st out l in
     (forall n, In n l -> optge st'.(aval)!n (Some out))  
  /\ (forall n, ~In n l -> st'.(aval)!n = st.(aval)!n)
  /\ (forall n, optge st'.(aval)!n st.(aval)!n)
  /\ (forall n, NS.In n st'.(worklist) \/ st'.(aval)!n = st.(aval)!n)
  /\ (forall n', NS.In n' st.(worklist) -> NS.In n' st'.(worklist))
  /\ (forall n', NS.In n' st'.(worklist) -> In n' l \/ NS.In n' st.(worklist))
  /\ (forall n', st.(visited) n' -> st'.(visited) n')
  /\ (forall n', st'.(visited) n' -> NS.In n' st'.(worklist) \/ st.(visited) n')
  /\ (forall n', st.(aval)!n' = None -> st'.(aval)!n' <> None -> st'.(visited) n').
Proof.
  induction l; simpl; intros.
  - repeat split; intros.
    + contradiction.
    + apply optge_refl.
    + auto.
    + auto.
    + auto.
    + auto.
    + auto.
    + congruence.
  - generalize (propagate_succ_charact st out a).
    set (st1 := propagate_succ st out a).
    intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
    generalize (IHl st1).
    set (st2 := propagate_succ_list st1 out l).
    intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). clear IHl.
    repeat split; intros.
    + destruct H.
      * subst n. eapply optge_trans; eauto.
      * auto.
    + rewrite B2 by tauto. apply A2; tauto.
    + eapply optge_trans; eauto.
    + destruct (B4 n). auto.
      destruct (peq n a).
      * subst n. destruct A4. left; auto. right; congruence.
      * right. rewrite H. auto.
    + eauto.
    + exploit B6; eauto. intros [P|P]. auto.
      exploit A6; eauto. intuition.
    + eauto.
    + specialize (B8 n'); specialize (A8 n'). intuition.
    + destruct st1.(aval)!n' eqn:ST1.
      apply B7. apply A9; auto. congruence.
      apply B9; auto.
Qed.


(** Characterization of [fixpoint_from]. *)

Inductive steps: state -> state -> Prop :=
  | steps_base: forall s, steps s s
  | steps_right: forall s1 s2 s3, steps s1 s2 -> step s2 = inr s3 -> steps s1 s3.

Scheme steps_ind := Induction for steps Sort Prop.

Lemma fixpoint_from_charact:
  forall start res,
  fixpoint_from start = Some res ->
  exists st, steps start st /\ NS.pick st.(worklist) = None /\ res = (AI.bot, st.(aval)).
Proof. 
  unfold fixpoint; intros.
  eapply (PrimIter.iterate_prop _ _ step
              (fun st => steps start st)
              (fun res => exists st, steps start st /\ NS.pick (worklist st) = None /\ res = (L.bot, aval st))); eauto.
  intros. destruct (step a) eqn:E.
  exists a; split; auto.
  unfold step in E. destruct (NS.pick (worklist a)) as [[n rem]|].
  destruct (code!n); discriminate.
  inv E. auto.
  eapply steps_right; eauto.
  constructor.
Qed.

(** ** Monotonicity properties *)

(** We first show that the [aval] and [visited] parts of the state
evolve monotonically:
- at each step, the values of the [aval[n]] either remain the same or
  increase with respect to the [optge] ordering;
- every node visited in the past remains visited in the future.
*)

Lemma step_incr:
  forall n s1 s2, step s1 = inr s2 ->
  optge s2.(aval)!n s1.(aval)!n /\ (s1.(visited) n -> s2.(visited) n). (** aval 一定会变大*)
Proof.
  unfold step; intros.
  destruct (NS.pick (worklist s1)) as [[p rem] | ]; try discriminate.
  destruct (code!p) as [instr|]; inv H.
  + generalize (propagate_succ_list_charact
                     (transf p (abstr_value p s1))
                     (successors instr)
                     {| aval := aval s1; worklist := rem; visited := visited s1 |}).
      simpl.
      set (s' := propagate_succ_list {| aval := aval s1; worklist := rem; visited := visited s1 |}
                    (transf p (abstr_value p s1)) (successors instr)).
      intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
      auto.
  + split. apply optge_refl. auto.
Qed.

Lemma steps_incr: 
  forall n s1 s2, steps s1 s2 ->
  optge s2.(aval)!n s1.(aval)!n /\ (s1.(visited) n -> s2.(visited) n).
Proof.
  induction 1.
  - split. apply optge_refl. auto.
  - destruct IHsteps. exploit (step_incr n); eauto. intros [P Q].
    split. eapply optge_trans; eauto. eauto.
Qed.

(** ** Correctness invariant *)

(** The following invariant is preserved at each iteration of Kildall's
  algorithm: for all visited program point [n], either
  [n] is in the worklist, or the inequations associated with [n]
  ([aval[s] >= transf n aval[n]] for all successors [s] of [n])
  hold.  In other terms, the worklist contains all nodes that were
  visited but do not yet satisfy their inequations.

  The second part of the invariant shows that nodes that already have
  an abstract value associated with them have been visited. *)

  Record good_state (st: state) : Prop := {
    gs_stable: forall n,
      st.(visited) n -> 
      NS.In n st.(worklist) \/ 
      (forall i s, 
       code!n = Some i -> In s (successors i) ->
       optge st.(aval)!s (Some (transf n (abstr_value n st))));
    gs_defined: forall n v,
      st.(aval)!n = Some v -> st.(visited) n 
  }.

(** We show that the [step] function preserves this invariant. *)

Lemma step_state_good:
  forall st pc rem instr,
  NS.pick st.(worklist) = Some (pc, rem) ->
  code!pc = Some instr ->
  good_state st ->
  good_state (propagate_succ_list (mkstate st.(aval) rem st.(visited))
                                  (transf pc (abstr_value pc st))
                                  (successors instr)).
Proof.
  intros until instr; intros PICK CODEAT [GOOD1 GOOD2].
  pose proof (NS.pick_some _ _ _ PICK) as PICK2.
  set (out := transf pc (abstr_value pc st)).
  generalize (propagate_succ_list_charact out (successors instr) {| aval := aval st; worklist := rem; visited := visited st |}).
  set (st' := propagate_succ_list {| aval := aval st; worklist := rem; visited := visited st |} out
                                  (successors instr)).
  simpl; intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  constructor. 
  - (* stable *)
    intros.
    destruct (A8 n H); auto. destruct (A4 n). auto. 
    replace (abstr_value n st') with (abstr_value n st)
      by (unfold abstr_value; rewrite H1; auto).
    exploit GOOD1; eauto. intros [P|P].
    + (* n was on the worklist *)
      rewrite PICK2 in P; destruct P.
      * (* node n is our node pc *)
        subst n. fold out. right; intros.
        assert (i = instr) by congruence. subst i.
        apply A1; auto.
      * (* n was already on the worklist *)
        left. apply A5; auto.
    + (* n was stable before, still is *)
      right. intros. apply optge_trans with st.(aval)!s. eapply A3. eapply P; eauto. 
  - (* defined *)  
    intros.
    destruct st.(aval)!n as [v'|] eqn:ST.
    + apply A7. eapply GOOD2; eauto.
    + apply A9; auto. congruence.
Qed.

Lemma step_state_good_2:
  forall st pc rem,
  good_state st ->
  NS.pick (worklist st) = Some (pc, rem) ->
  code!pc = None ->
  good_state (mkstate st.(aval) rem st.(visited)).
Proof.
  intros until rem; intros [GOOD1 GOOD2] PICK CODE.
  generalize (NS.pick_some _ _ _ PICK); intro PICK2.
  constructor; simpl; intros.
  - (* stable *)
    exploit GOOD1; eauto. intros [P | P].
    + rewrite PICK2 in P. destruct P; auto.
      subst n. right; intros. congruence.
    + right; exact P.
  - (* defined *)
  eapply GOOD2; eauto.
Qed.

Lemma steps_state_good:
  forall st1 st2, steps st1 st2 -> good_state st1 -> good_state st2.
Proof.
  induction 1; intros.
  - auto.
  - unfold step in e.
    destruct (NS.pick (worklist s2)) as [[n rem] | ] eqn:PICK; try discriminate.
    destruct (code!n) as [instr|] eqn:CODE; inv e.
    eapply step_state_good; eauto.
    eapply step_state_good_2; eauto.
Qed.

(** We show that initial states satisfy the invariant. *)

Lemma start_state_good:
  forall enode eval, good_state (start_state enode eval).
Proof.
  intros. unfold start_state; constructor; simpl; intros.
  - subst n. rewrite NS.add_spec; auto.
  - rewrite PTree.gsspec in H. rewrite PTree.gempty in H.
    destruct (peq n enode). auto. discriminate.
Qed.

Lemma start_state_nodeset_good:
  forall enodes, good_state (start_state_nodeset enodes).
Proof.
  intros. unfold start_state_nodeset; constructor; simpl; intros.
  - left. auto.
  - rewrite PTree.gempty in H. congruence.
Qed.

Lemma start_state_allnodes_good:
  good_state start_state_allnodes.
Proof.
  unfold start_state_allnodes; constructor; simpl; intros.
  - destruct H as [instr CODE]. left. eapply NS.all_nodes_spec; eauto.
  - rewrite PTree.gempty in H. congruence.
Qed.

(** Reachability in final states. *)

Lemma reachable_visited:
  forall st, good_state st -> NS.pick st.(worklist) = None ->
  forall p q, reachable code successors p q -> st.(visited) p -> st.(visited) q.
Proof.
  intros st [GOOD1 GOOD2] PICK. induction 1; intros.
  - auto.
  - eapply IHreachable; eauto.
    exploit GOOD1; eauto. intros [P | P].
    eelim NS.pick_none; eauto.
    exploit P; eauto. intros OGE; inv OGE. eapply GOOD2; eauto.
Qed.


(** ** Correctness of the solution returned by [fixpoint]. *)

(** As a consequence of the [good_state] invariant, the result of
  [fixpoint], if defined, is a solution of the dataflow inequations.
  This assumes that the transfer function maps [L.bot] to [L.bot]. *)
Theorem fixpoint_solution:
  forall ep ev res n instr s,
  fixpoint ep ev = Some res ->
  code!n = Some instr ->
  In s (successors instr) ->
  (forall n, L.eq (transf n AI.bot) AI.bot) ->  
  L.ge res!!s (transf n res!!n). 
Proof.
  unfold fixpoint; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit steps_state_good; eauto. apply start_state_good.  intros [GOOD1 GOOD2]. 
  rewrite RES; unfold PMap.get; simpl. 
  destruct st.(aval)!n as [v|] eqn:STN. 
  - destruct (GOOD1 n) as [P|P]. eauto. 
    {
      eelim NS.pick_none; eauto. 
    }
    {
      exploit P; eauto. unfold abstr_value; rewrite STN. intros OGE. inv OGE. auto.
    }
  - apply L.ge_trans with L.bot. apply L.ge_bot. apply L.ge_refl. apply L.eq_sym. eauto.
Qed.


Theorem fixpoint_solution_fst_bot: 
  forall ep ev res,
  fixpoint ep ev = Some res ->
  fst res = AI.bot.
Proof.
  intros.
  unfolds fixpoint.
  (* unfolds fixpoint_from. *)
  remember (start_state ep ev) as start.
  pose proof (fixpoint_from_charact start res) H.
  destruct H0 as (a & b & c & HH).
  rewrite HH. simpls. trivial.
Qed.

  (** Moreover, the result of [fixpoint], if defined, satisfies the additional
  constraint given on the entry point. *)

Theorem fixpoint_entry:
  forall ep ev res,
  fixpoint ep ev = Some res ->
  L.ge res!!ep ev.
Proof.
  unfold fixpoint; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit (steps_incr ep); eauto. simpl. rewrite PTree.gss. intros [P Q].
  rewrite RES; unfold PMap.get; simpl. inv P. auto.
Qed.


Theorem fixpoint_entry_exists:
  forall ep ev res,
  fixpoint ep ev = Some res ->
  exists l, 
  (snd res)!ep = Some l.
Proof.
  unfold fixpoint; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit (steps_incr ep); eauto. simpl. rewrite PTree.gss. intros [P Q].
  rewrite RES. 
  unfold snd.
  simpl. inv P. 
  eexists. auto.
Qed.

(** For [fixpoint_allnodes], we show that the result is a solution
  without assuming [transf n L.bot = L.bot]. *)

Theorem fixpoint_allnodes_solution:
  forall res n instr s,
  fixpoint_allnodes = Some res ->
  code!n = Some instr ->
  In s (successors instr) ->
  L.ge res!!s (transf n res!!n).
Proof.
  unfold fixpoint_allnodes; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit steps_state_good; eauto. apply start_state_allnodes_good. intros [GOOD1 GOOD2].
  exploit (steps_incr n); eauto. simpl. intros [U V].
  exploit (GOOD1 n). apply V. exists instr; auto. intros [P|P].
  eelim NS.pick_none; eauto.
  exploit P; eauto. intros OGE. rewrite RES; unfold PMap.get; simpl.
  inv OGE. assumption.
Qed.

(** For [fixpoint_nodeset], we show that the result is a solution
  at all program points that are reachable from the given entry points. *)

Theorem fixpoint_nodeset_solution:
  forall enodes res e n instr s,
  fixpoint_nodeset enodes = Some res ->
  NS.In e enodes ->
  reachable code successors e n ->
  code!n = Some instr ->
  In s (successors instr) ->
  L.ge res!!s (transf n res!!n).
Proof.
  unfold fixpoint_nodeset; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit steps_state_good; eauto. apply start_state_nodeset_good. intros GOOD.
  exploit (steps_incr e); eauto. simpl. intros [U V].
  assert (st.(visited) n).
  { eapply reachable_visited; eauto. }
  destruct GOOD as [GOOD1 GOOD2].
  exploit (GOOD1 n); eauto. intros [P|P].
  eelim NS.pick_none; eauto.
  exploit P; eauto. intros OGE. rewrite RES; unfold PMap.get; simpl.
  inv OGE. assumption.
Qed.

(** ** Preservation of a property over solutions *)
Theorem fixpoint_invariant:
  forall ep ev
    (P: L.t -> Prop)
    (P_bot: P L.bot)
    (P_lub: forall x y, P x -> P y -> P (L.lub x y))
    (P_transf: forall pc instr x, code!pc = Some instr -> P x -> P (transf pc x))
    (P_entrypoint: P ev)
    res pc,
  fixpoint ep ev = Some res ->
  P res!!pc.
Proof.
  intros.
  set (inv := fun st => forall x, P (abstr_value x st)).
  assert (inv (start_state ep ev)).
  {
    red; simpl; intros. unfold abstr_value, start_state; simpl.
    rewrite PTree.gsspec. rewrite PTree.gempty.
    destruct (peq x ep). auto. auto.
  }
  assert (forall st v n, inv st -> P v -> inv (propagate_succ st v n)).
  {
    unfold inv, propagate_succ. intros.
    destruct (aval st)!n as [oldl|] eqn:E.
    destruct (L.beq oldl (L.lub oldl v)).
    auto.
    unfold abstr_value. simpl. rewrite PTree.gsspec. destruct (peq x n).
    apply P_lub; auto. replace oldl with (abstr_value n st). auto.
    unfold abstr_value; rewrite E; auto.
    apply H1.
    unfold abstr_value. simpl. rewrite PTree.gsspec. destruct (peq x n).
    auto.
    apply H1.
  }
  assert (forall l st v, inv st -> P v -> inv (propagate_succ_list st v l)).
  {
    induction l; intros; simpl. auto.
    apply IHl; auto.
  }
  assert (forall st1 st2, steps st1 st2 -> inv st1 -> inv st2).
  {
    induction 1; intros.
    auto.
    unfold step in e. destruct (NS.pick (worklist s2)) as [[n rem]|]; try discriminate.
    destruct (code!n) as [instr|] eqn:INSTR; inv e.
    apply H2. apply IHsteps; auto. eapply P_transf; eauto. apply IHsteps; auto.
    apply IHsteps; auto.
  }
  unfold fixpoint in H. exploit fixpoint_from_charact; eauto.
  intros (st & STEPS & PICK & RES).
  replace (res!!pc) with (abstr_value pc st). eapply H3; eauto.
  rewrite RES; auto.
Qed.

End Kildall.

Section RtlSolver.

  Definition fixpoint_blk 
             (cdhp: CodeHeap) 
             (successors: BBlock.t -> list (Language.fid)) 
             (enode: positive) (eval: AI.t) 
             (transf_blk: positive -> AI.t -> AI.b): option AI.ACdhp := 
    let transf := (fun n ai => AI.getLast (transf_blk n ai)) in
    match (fixpoint cdhp successors transf enode eval) with 
    | None => None 
    | Some res => Some (AI.bots, PTree.map transf_blk (snd res))
    end.

  (* Require Import Syntax. *)
  Theorem fixpoint_blk_entry:
    forall cdhp_s succ fentry_s eval transf_blk acdhp,
      (forall i l, (AI.getFirst (transf_blk i l)) = l) 
      ->
      fixpoint_blk cdhp_s succ fentry_s eval transf_blk = Some acdhp 
      -> 
      AI.ge (AI.getFirst (acdhp !! fentry_s)) eval.
  Proof.
    intros until acdhp. intro GOOD_TRANF_BLK. intros. 
    unfolds fixpoint_blk.
    remember (fixpoint cdhp_s succ
                       (fun (n : positive) (ai : AI.t) => AI.getLast (transf_blk n ai))
                       fentry_s eval) as fx.
    destruct fx eqn:EQFX.
    - inversion H. rename t into realfx. 
      assert (L.ge realfx!!fentry_s eval). {
        eapply fixpoint_entry; eauto.
      }
      assert (AI.getFirst (acdhp !! fentry_s) = realfx!!fentry_s). {
        remember acdhp!!fentry_s as aentry_blk.
        unfold "!!" in Heqaentry_blk.
        rewrite <- H1 in Heqaentry_blk; simpls.
        remember ((PTree.map transf_blk (snd realfx)) ! fentry_s) as ablks.
        rewrite PTree.gmap in Heqablks; unfolds option_map; simpls.
        remember ((snd realfx) ! fentry_s) as realaentry.
        assert (exists l, realaentry = Some l). {
          rewrite Heqrealaentry.
          eapply fixpoint_entry_exists; eauto.
        }
        destruct H2 as (l & H2).
        rewrite H2 in Heqablks.
        rewrite Heqablks in Heqaentry_blk.
        rewrite Heqaentry_blk.
        rewrite GOOD_TRANF_BLK.
        unfold "!!".
        rewrite <- Heqrealaentry. rewrite H2; auto.
      }
      rewrite <- H1 in H2.
      rewrite H2; auto.
    - discriminate. 
  Qed.

  Definition analyze_func (** thrd *)
             (func: Func) 
             (successors: BBlock.t -> list (Language.fid)) 
             (eval: AI.t) 
             (transf_blk': AI.t -> BBlock.t -> AI.b): option AI.ACdhp := 
    let (cdhp, fid) := func in 
    let transf_blk := (fun n ai =>
                         match (cdhp!n) with 
                         | Some b => transf_blk' ai b 
                         | None => AI.Atom ai(*AI.bots*) 
                         end
                      ) in
    fixpoint_blk cdhp successors fid eval (transf_blk).

  Theorem analyze_func_solution_get
            succ transf_blk acdhp cdhp_s fentry_s n blk ep
            (WF_TRANS_FORWARD: forall l blk, (AI.getFirst (transf_blk l blk)) = l)
            (BOT_TRANS: forall b, AI.getLast (transf_blk AI.bot b) = AI.bot)
            (ANALYSIS: analyze_func (cdhp_s, fentry_s) succ ep transf_blk = Some acdhp)
            (GET_BLK: cdhp_s ! n = Some blk):
    transf_blk (AI.getFirst acdhp !! n) blk = acdhp !! n \/
    acdhp !! n = AI.bots.
  Proof.
    unfold analyze_func in ANALYSIS.
    unfold fixpoint_blk in ANALYSIS.
    remember (fun (n : positive) (ai : AI.t) =>
                  AI.getLast match cdhp_s ! n with
                             | Some b => transf_blk ai b
                             | None => AI.Atom ai
                             end) as transf.
    destruct (fixpoint cdhp_s succ transf fentry_s ep) eqn:Heqe; simpls; tryfalse.
    inv ANALYSIS. unfold "!!". simpl.
    rewrite PTree.gmap. unfold option_map.
    rewrite GET_BLK; simpl.
    destruct ((snd t) ! n) eqn:ANALYSIS; eauto.
    rewrite WF_TRANS_FORWARD. eauto. 
  Qed.

  Theorem analyze_func_solution1
          succ transf_blk acdhp cdhp_s fentry_s n blk s blk_s ep
          (WF_TRANS_FORWARD: forall l blk, (AI.getFirst (transf_blk l blk)) = l)
          (BOT_TRANS: forall b, AI.getLast (transf_blk AI.bot b) = AI.bot)
          (ANALYSIS: analyze_func (cdhp_s, fentry_s) succ ep transf_blk = Some acdhp)
          (GET_BLK: cdhp_s ! n = Some blk)
          (SUCC: In s (succ blk))
          (SUCC_BB: cdhp_s ! s = Some blk_s):
    AI.ge (AI.getFirst acdhp !! s) (AI.getLast (transf_blk (AI.getFirst (acdhp !! n)) blk)).
  Proof.
    unfold analyze_func in ANALYSIS.
    unfold fixpoint_blk in ANALYSIS.
    remember (fun (n : positive) (ai : AI.t) =>
                  AI.getLast match cdhp_s ! n with
                             | Some b => transf_blk ai b
                             | None => AI.Atom ai
                             end) as transf.
    destruct (fixpoint cdhp_s succ transf fentry_s ep) eqn:Heqe; simpls; tryfalse.
    lets DEFAULT: Heqe. eapply fixpoint_solution_fst_bot in DEFAULT.
    inv ANALYSIS.
    eapply fixpoint_solution with (s0 := s) (instr := blk) in Heqe; eauto.
    rewrite GET_BLK in Heqe.
    unfold "!!". simpl.
    repeat (rewrite PTree.gmap). unfold option_map.
    rewrite GET_BLK. rewrite SUCC_BB.
    destruct ((snd t) ! s) eqn:ANALYSIS_s.
    {
      destruct ((snd t) ! n) eqn:ANALYSIS_n.
      rewrite WF_TRANS_FORWARD. rewrite WF_TRANS_FORWARD.
      unfold "!!" in Heqe. rewrite ANALYSIS_s, ANALYSIS_n in Heqe. eauto.
      simpl. rewrite BOT_TRANS. 
      eapply L.ge_bot; eauto.
    }
    {
      destruct ((snd t) ! n) eqn:ANALYSIS_n.
      rewrite WF_TRANS_FORWARD. simpl.
      unfold "!!" in Heqe. rewrite ANALYSIS_s, ANALYSIS_n in Heqe.
      rewrite DEFAULT in Heqe. eauto.
      simpl. unfold "!!" in Heqe. rewrite ANALYSIS_s, ANALYSIS_n in Heqe.
      rewrite DEFAULT in Heqe. eauto.
    }
    intro. destruct (cdhp_s ! n0); simpl.
    rewrite BOT_TRANS; eauto. eapply L.eq_refl; eauto.
    eapply L.eq_refl; eauto.
  Qed.

  Theorem analyze_func_entry1
          succ eval transf_blk acdhp cdhp_s fentry_s
          (WF_TRANS_FORWARD: forall l blk, (AI.getFirst (transf_blk l blk)) = l) 
          (ANALYSIS: analyze_func (cdhp_s, fentry_s) succ eval transf_blk = Some acdhp):
    AI.ge (AI.getFirst (acdhp !! fentry_s)) eval.
  Proof.
    unfold analyze_func in ANALYSIS.
    unfold fixpoint_blk in ANALYSIS.
    remember (fun (n : positive) (ai : AI.t) =>
                  AI.getLast match cdhp_s ! n with
                             | Some b => transf_blk ai b
                             | None => AI.Atom ai
                             end) as transf.
    destruct (fixpoint cdhp_s succ transf fentry_s eval) eqn:Heqe; simpls; tryfalse.
    inv ANALYSIS.
    lets Heqe': Heqe.
    eapply fixpoint_solution_fst_bot in Heqe'; simpls.
    eapply fixpoint_entry in Heqe.
    unfold "!!" in *. simpl.
    rewrite PTree.gmap.
    unfold option_map.
    destruct ((snd t) ! fentry_s) eqn:ENTRY; tryfalse.
    destruct (cdhp_s ! fentry_s); simpl; eauto.
    rewrite WF_TRANS_FORWARD; eauto.
    simpl. rewrite Heqe' in Heqe. eauto.
  Qed.
    
  Definition analyze_program 
             (prog: Code) 
             (successors: BBlock.t -> list (Language.fid))
             (eval: AI.t) 
             (transf_blk': AI.t -> BBlock.t -> AI.b): AI.AProg := 
    let func := (fun f =>
                   match (analyze_func f successors eval transf_blk') with 
                   | Some result => result 
                   | None => PMap.init (AI.Atom eval)  (** other way to deal with this ? *)
                   end
                ) 
    in
    PTree.map1 func prog.

  Theorem wf_analyze_func: 
    forall code_s fid cdhp_s fentry_s eval transfb,
      code_s ! fid = Some (cdhp_s, fentry_s)
      ->
      exists acdhp,
        (analyze_program code_s succ eval transfb) ! fid = Some acdhp.
  Proof.
    intros.
    unfolds analyze_program.
    rewrite PTree.gmap1; unfolds option_map.
    (* Set Printing All. *)
    unfold Func.
    rewrite H.
    destruct (analyze_func (cdhp_s, fentry_s) succ eval transfb) eqn:EqAFunc; eauto.
  Qed.

  Theorem analyze_func_entry:
    forall code_s succ eval transf_blk fid acdhp cdhp_s fentry_s,
      (forall l blk, (AI.getFirst (transf_blk l blk)) = l) 
      ->
      (analyze_program code_s succ eval transf_blk) ! fid = Some acdhp 
      -> 
      code_s ! fid = Some (cdhp_s, fentry_s)
      -> 
      AI.ge (AI.getFirst (acdhp !! fentry_s)) eval.
  Proof.
    intros until fentry_s. intro HH. intros. unfolds analyze_program.
    rewrite PTree.gmap1 in H; unfolds option_map. rewrite H0 in H.
    remember (analyze_func (cdhp_s, fentry_s) succ eval transf_blk) 
      as analysis_func_partial.
    inversion H.
    destruct analysis_func_partial eqn:EQH.
    2: { (** bot *)
      unfolds AI.getFirst. 
      rewrite PMap.gi; simpls; auto.
      eapply L.ge_refl. eapply L.eq_refl.
    } (** eval *)
    simpls.
    eapply fixpoint_blk_entry; eauto.
    intros.
    unfolds AI.getFirst.
    destruct (cdhp_s!i); eauto.
  Qed.

  (* Axiom fixpoint_solution:
    forall A (code: PTree.t A) successors transf res n instr s,
    fixpoint code successors transf = Some res ->  
    code!n = Some instr -> In s (successors instr) ->
    (forall n a, code!n = None -> L.eq (transf n a) L.bot) ->
    L.ge res!!s (transf s res!!n). *)

  Theorem analyze_func_solution:
    forall code_s succ eval transf_blk fid acdhp cdhp_s fentry_s n blk s,
      (** wf transf_blk*)
      (forall l blk, (AI.getFirst (transf_blk l blk)) = l)  ->
      (forall b,
          AI.getLast (transf_blk AI.bot b) = AI.bot) -> 
      (analyze_program code_s succ eval transf_blk) ! fid = Some acdhp 
      -> 
      code_s ! fid = Some (cdhp_s, fentry_s) -> 
      cdhp_s!n = Some blk -> 
      In s (succ blk) -> 
      (* (forall n a, cdhp_s!n = None -> L.eq (transf n a) L.bot) -> *)
      AI.ge (AI.getFirst acdhp !! s)  (AI.getLast (acdhp !! n)).
  Proof.
    intros until s. intros HH0 HH. intros.
    unfolds analyze_program.
    rewrite PTree.gmap1 in H; unfolds option_map.
    rewrite H0 in H.
    remember (analyze_func (cdhp_s, fentry_s) succ eval transf_blk) as afunc.
    inversion H.
    destruct afunc eqn:EQAFunc.     
    2: {
      repeat rewrite PMap.gi.
      unfolds AI.getFirst; unfolds AI.getLast; simpls.
      eapply L.ge_refl. eapply L.eq_refl.
    }
    unfolds analyze_func.
    unfolds fixpoint_blk.
    remember ((fun (n : positive) (ai : AI.t) =>
                 AI.getLast
                   match cdhp_s ! n with
                   | Some b => transf_blk ai b
                   | None => AI.Atom ai
                   end)) as transf.
    remember (fixpoint cdhp_s succ transf fentry_s eval) as realfx.
    destruct realfx eqn:EQRealFx.
    2: { discriminate. }
    rename t into res.
    assert (AI.ge res!!s (transf n res!!n)). {
      eapply fixpoint_solution; eauto.
      intros.
      rewrite Heqtransf.
      destruct (cdhp_s ! n0) eqn: EQBlk.
      2: { unfolds AI.getLast. eapply L.eq_refl. }
      rewrite HH. unfolds AI.bot. eapply L.eq_refl.
    }
    assert (AI.getLast a !! n = transf n (res !! n) ). {
      rewrite Heqtransf.
      rewrite H1.  
      inversion Heqafunc. unfold "!!"; simpls. 
      rewrite PTree.gmap; unfolds option_map.
      rewrite H1.
      remember ((snd res) ! n) as former. 
      destruct former; eauto. (** FIXME: maybe some def inconsistency *) 
      assert (fst res = AI.bot). {
        eapply fixpoint_solution_fst_bot; eauto.
      }
      rewrite H5. 
      rewrite HH.
      unfolds AI.getLast; simpls. trivial.
    }
    assert (AI.getFirst a !! s = res !! s). {
      remember (a !! s) as ablk.
      inversion Heqafunc.
      rewrite H7 in Heqablk. 
      unfold "!!" in Heqablk. simpls.
      rewrite PTree.gmap in Heqablk; unfolds option_map.
      unfold "!!". 
      remember ((snd res) ! s) as asblk.
      rewrite Heqablk. unfolds AI.getFirst.
      destruct asblk eqn:EqAsblk; simpls. 
      2: {        
        assert (fst res = AI.bot). {
          eapply fixpoint_solution_fst_bot; eauto.
        } rewrite H6. trivial. 
      }
      remember (cdhp_s!s) as sblk.
      destruct sblk eqn:EqSblk; eauto.
    }
    rewrite H6.
    rewrite H5.
    auto.
  Qed.

  Theorem analyze_func_solution':
  forall succ eval transf_blk acdhp cdhp_s fentry_s n blk s,
    (** wf transf_blk*)
    (forall l blk, (AI.getFirst (transf_blk l blk)) = l)  ->
    (forall b,
        AI.getLast (transf_blk AI.bot b) = AI.bot) -> 
    analyze_func (cdhp_s, fentry_s) succ eval transf_blk = Some acdhp ->
    cdhp_s!n = Some blk -> 
    In s (succ blk) -> 
    AI.ge (AI.getFirst acdhp !! s)  (AI.getLast (acdhp !! n)).
Proof.
  intros until s. intros HH0 HH. intros.
  remember (analyze_func (cdhp_s, fentry_s) succ eval transf_blk) as afunc.
  inversion H.
  destruct afunc eqn:EQAFunc.     
  2: {
    discriminate.
  }
  unfolds analyze_func.
  unfolds fixpoint_blk.
  remember ((fun (n : positive) (ai : AI.t) =>
               AI.getLast
                 match cdhp_s ! n with
                 | Some b => transf_blk ai b
                 | None => AI.Atom ai
                 end)) as transf.
  remember (fixpoint cdhp_s succ transf fentry_s eval) as realfx.
  destruct realfx eqn:EQRealFx.
  2: { discriminate. }
  rename t into res.
  assert (AI.ge res!!s (transf n res!!n)). {
    eapply fixpoint_solution; eauto.
    intros.
    rewrite Heqtransf.
    destruct (cdhp_s ! n0) eqn: EQBlk.
    2: { unfolds AI.getLast. eapply L.eq_refl. }
    rewrite HH. unfolds AI.bot. eapply L.eq_refl.
  }
  assert (AI.getLast a !! n = transf n (res !! n) ). {
    rewrite Heqtransf.
    rewrite H0.  
    inversion Heqafunc. unfold "!!"; simpls. 
    rewrite PTree.gmap; unfolds option_map.
    rewrite H0.
    remember ((snd res) ! n) as former. 
    destruct former; eauto. (** FIXME: maybe some def inconsistency *) 
    assert (fst res = AI.bot). {
      eapply fixpoint_solution_fst_bot; eauto.
    }
    rewrite H4. 
    rewrite HH.
    unfolds AI.getLast; simpls. trivial.
  }
  assert (AI.getFirst a !! s = res !! s). {
    remember (a !! s) as ablk.
    inversion Heqafunc.
    rewrite H6 in Heqablk. 
    unfold "!!" in Heqablk. simpls.
    rewrite PTree.gmap in Heqablk; unfolds option_map.
    unfold "!!". 
    remember ((snd res) ! s) as asblk.
    rewrite Heqablk. unfolds AI.getFirst.
    destruct asblk eqn:EqAsblk; simpls. 
    2: {        
      assert (fst res = AI.bot). {
        eapply fixpoint_solution_fst_bot; eauto.
      } rewrite H5. trivial. 
    }
    remember (cdhp_s!s) as sblk.
    destruct sblk eqn:EqSblk; eauto.
  }
  inversion H2. 
  rewrite <- H7.
  rewrite H5.
  rewrite H4.
  auto.
Qed.

End RtlSolver.
End Dataflow_Solver.

(** * Solving backward dataflow problems using Kildall's algorithm *)

(** A backward dataflow problem on a given flow graph is a forward
  dataflow program on the reversed flow graph, where predecessors replace
  successors.  We exploit this observation to cheaply derive a backward
  solver from the forward solver. *)

(** ** Construction of the reversed flow graph (the predecessor relation) *)
(* successors_list: return the list of the successors of pc *)
Definition successors_list (successors: PTree.t (list positive)) (pc: positive) : list positive :=
  match successors!pc with None => nil | Some l => l end.

Notation "a !!! b" := (successors_list a b) (at level 1).

Section Predecessor.

Context {A: Type}.
Variable code: PTree.t A.
Variable successors: A -> list positive.

(* from -> tolist, add the node 'from' to the precessors of tolist
 from -> (to1 :: to2 :: to3) *)
Fixpoint add_successors (pred: PTree.t (list positive))
                        (from: positive) (tolist: list positive)
                        {struct tolist} : PTree.t (list positive) :=
  match tolist with
  | nil => pred
  | to :: rem => add_successors (PTree.set to (from :: pred!!!to) pred) from rem
  end.

Lemma add_successors_correct:
  forall tolist from pred n s,
  In n pred!!!s \/ (n = from /\ In s tolist) ->
  In n (add_successors pred from tolist)!!!s.
Proof.
  induction tolist; simpl; intros.
  tauto.
  apply IHtolist.
  unfold successors_list at 1. rewrite PTree.gsspec. destruct (peq s a).
  subst a. destruct H. auto with coqlib.
  destruct H. subst n. auto with coqlib.
  fold (successors_list pred s). intuition congruence.
Qed.

(* return: node -> list node, evaluates each node's precessors *)
Definition make_predecessors : PTree.t (list positive) :=
  PTree.fold (fun pred pc instr => add_successors pred pc (successors instr))
             code (PTree.empty (list positive)).

Lemma make_predecessors_correct_1:
  forall n instr s,
  code!n = Some instr -> In s (successors instr) ->
  In n make_predecessors!!!s.
Proof.
  intros until s.
  set (P := fun m p => m!n = Some instr -> In s (successors instr) ->
                       In n p!!!s).
  unfold make_predecessors.
  apply PTree_Properties.fold_rec with (P := P); unfold P; intros.
(* extensionality *)
  apply H0; auto. rewrite H; auto.
(* base case *)
  rewrite PTree.gempty in H; congruence.
(* inductive case *)
  apply add_successors_correct.
  rewrite PTree.gsspec in H2. destruct (peq n k).
  inv H2. auto.
  auto.
Qed.

Lemma make_predecessors_correct_2:
  forall n instr s,
  code!n = Some instr -> In s (successors instr) ->
  exists l, make_predecessors!s = Some l /\ In n l.
Proof.
  intros. exploit make_predecessors_correct_1; eauto.
  unfold successors_list. destruct (make_predecessors!s); simpl; intros.
  exists l; auto.
  contradiction.
Qed.

Lemma reachable_predecessors:
  forall p q,
  reachable code successors p q ->
  reachable make_predecessors (fun l => l) q p.
Proof.
  induction 1.
  - constructor.
  - exploit make_predecessors_correct_2; eauto. intros [l [P Q]].
    eapply reachable_right; eauto.
Qed.

End Predecessor.

(** ** Solving backward dataflow problems *)

(** The interface to a backward dataflow solver is as follows. *)
Module Type BACKWARD_DATAFLOW_SOLVER.
  Declare Module L : SEMILATTICE.
  Module AI := AI(L).

  (** [fixpoint successors transf] is the solver.
    It returns either an error or a mapping from program points to
    values of type [L.t] representing the solution.  [successors]
    is a finite map returning the list of successors of the given program
    point. [transf] is the transfer function. *)

  Parameter fixpoint:
    forall {A: Type} (code: PTree.t A) (successors: A -> list positive)
           (transf: positive -> L.t -> L.t),
    option (PMap.t L.t).

  (** The [fixpoint_solution] theorem shows that the returned solution,
    if any, satisfies the backward dataflow inequations. *)

  Axiom fixpoint_solution:
    forall A (code: PTree.t A) successors transf res n BB s,
    fixpoint code successors transf = Some res ->
    code!n = Some BB -> In s (successors BB) ->
    (forall n a, code!n = None -> L.eq (transf n a) L.bot) ->
    L.ge res!!n (transf s res!!s).

  (** [fixpoint_allnodes] is a variant of [fixpoint], less algorithmically
    efficient, but correct without any hypothesis on the transfer function. *)

  Parameter fixpoint_allnodes:
    forall {A: Type} (code: PTree.t A) (successors: A -> list positive)
           (transf: positive -> L.t -> L.t),
    option (PMap.t L.t).

  Axiom fixpoint_allnodes_solution:
    forall A (code: PTree.t A) successors transf res n BB s,
    fixpoint_allnodes code successors transf = Some res ->
    code!n = Some BB -> In s (successors BB) ->
    L.ge res!!n (transf s res!!s).

End BACKWARD_DATAFLOW_SOLVER.

(** We construct a generic backward dataflow solver, working over any
  semi-lattice structure, by applying the forward dataflow solver
  with the predecessor relation instead of the successor relation. *)

Module Backward_Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET) <:
                   BACKWARD_DATAFLOW_SOLVER with Module L := LAT.

  Module L := LAT.
  Module AI := AI(L).

  Module DS := Dataflow_Solver L NS.

  Section Kildall.

    Context {A: Type}.
    Variable code: PTree.t A.
    Variable successors: A -> list positive.
    Variable transf: positive -> AI.t -> AI.t.

    (** Finding entry points for the reverse control-flow graph. *)

    Section Exit_points.

      (** Assuming that the nodes of the CFG [code] are numbered in reverse
          postorder (cf. pass [Renumber]), an edge from [n] to [s] is a
          normal edge if [s < n] and a back-edge otherwise.

          [sequential_node] returns

          - [true] if the given node has at least one normal outgoing edge.

          - It returns [false] if the given node is an exit node (no outgoing edges)
            or the final node of a loop body (all outgoing edges are back-edges).

          As we prove later, the set
          of all non-sequential node is an appropriate set of entry points
          for exploring the reverse CFG. *)

      Definition sequential_node (pc: positive) (instr: A): bool :=
        existsb (fun s => match code!s with None => false | Some _ => plt s pc end)
                (successors instr).

      (* exit points: exit nodes + final node of a loop baby *)
      Definition exit_points : NS.t :=
        PTree.fold
          (fun ep pc instr =>
             if sequential_node pc instr
             then ep
             else NS.add pc ep)
          code NS.empty.

      Lemma exit_points_charact:
        forall n,
          NS.In n exit_points <-> exists i, code!n = Some i /\ sequential_node n i = false.
      Proof.
        intros n. unfold exit_points. eapply PTree_Properties.fold_rec.
        - (* extensionality *)
          intros. rewrite <- H. auto.
        - (* base case *)
          simpl. split; intros.
          eelim NS.empty_spec; eauto.
          destruct H as [i [P Q]]. rewrite PTree.gempty in P. congruence.
        - (* inductive case *)
          intros. destruct (sequential_node k v) eqn:SN.
          + rewrite H1. rewrite PTree.gsspec. destruct (peq n k).
            subst. split; intros [i [P Q]]. congruence. inv P. congruence.
            tauto.
          + rewrite NS.add_spec. rewrite H1. rewrite PTree.gsspec. destruct (peq n k).
            subst. split. intros. exists v; auto. auto.
            split. intros [P | [i [P Q]]]. congruence. exists i; auto.
            intros [i [P Q]]. right; exists i; auto.
      Qed.

      Lemma reachable_exit_points:
        forall pc i,
          code!pc = Some i -> exists x, NS.In x exit_points /\ reachable code successors pc x.
      Proof.
        intros pc0. pattern pc0. apply (well_founded_ind Plt_wf).
        intros pc HR i CODE.
        destruct (sequential_node pc i) eqn:SN.
        - (* at least one successor that decreases the pc *)
          unfold sequential_node in SN. rewrite existsb_exists in SN.
          destruct SN as [s [P Q]]. destruct (code!s) as [i'|] eqn:CS; try discriminate. InvBooleans.
          exploit (HR s); eauto. intros [x [U V]].
          exists x; split; auto. eapply reachable_left; eauto.
        - (* otherwise we are an exit point *)
          exists pc; split.
          rewrite exit_points_charact. exists i; auto. constructor.
      Qed.

      (** The crucial property of exit points is that any nonempty node in the
          CFG is reverse-reachable from an exit point. *)

      Lemma reachable_exit_points_predecessor:
        forall pc i,
          code!pc = Some i ->
          exists x, NS.In x exit_points /\ reachable (make_predecessors code successors) (fun l => l) x pc.
      Proof.
        intros. exploit reachable_exit_points; eauto. intros [x [P Q]].
        exists x; split; auto. apply reachable_predecessors. auto.
      Qed.

    End Exit_points.

    (** The efficient backward solver.  *)

    Definition fixpoint :=
      DS.fixpoint_nodeset
        (make_predecessors code successors) (fun l => l)
        transf exit_points.

    Theorem fixpoint_solution:
      forall res n BB s,
        fixpoint = Some res ->
        code!n = Some BB -> In s (successors BB) ->
        (forall n a, code!n = None -> L.eq (transf n a) L.bot) ->
        L.ge res!!n (transf s res!!s).
    Proof.
      intros.
      exploit (make_predecessors_correct_2 code); eauto. intros [l [P Q]].
      destruct code!s as [BB'|] eqn:CS.
      - exploit reachable_exit_points_predecessor. eexact CS. intros (ep & U & V).
        unfold fixpoint in H. eapply DS.fixpoint_nodeset_solution; eauto.
      - apply L.ge_trans with L.bot. apply L.ge_bot.
        apply L.ge_refl. apply L.eq_sym. auto.
    Qed.

    (** The alternate solver that starts with all nodes of the CFG instead
        of just the exit points. *)

    Definition fixpoint_allnodes :=
      DS.fixpoint_allnodes
        (make_predecessors code successors) (fun l => l)
        transf. 

    Theorem fixpoint_allnodes_solution:
      forall res n instr s,
        fixpoint_allnodes = Some res ->
        code!n = Some instr -> In s (successors instr) ->
        L.ge res!!n (transf s res!!s).
    Proof.
      intros. 
      exploit (make_predecessors_correct_2 code); eauto. intros [l [P Q]].
      unfold fixpoint_allnodes in H.
      eapply DS.fixpoint_allnodes_solution; eauto.
    Qed.

    Theorem fixpoint_allnodes_solution_fst_bot: 
      forall res,
        fixpoint_allnodes = Some res ->
        fst res = AI.bot.
    Proof.
      intros.
      unfolds fixpoint_allnodes, DS.fixpoint_allnodes. 
      remember (DS.start_state_allnodes (make_predecessors code successors)) as start.
      pose proof (DS.fixpoint_from_charact _ _ transf start res) H.
      destruct H0 as (a & b & c & HH).
      rewrite HH. simpls. trivial.
    Qed.

  End Kildall.

  Section RtlSolverBackward.   
    
    Definition fixpoint_blk_backward 
               (cdhp: CodeHeap) 
               (successors: BBlock.t -> list (Language.fid)) 
               (transf_blk: positive -> AI.t -> AI.b): option AI.ACdhp := 
      let transf := (fun n ai => AI.getFirst (transf_blk n ai)) in
      match (fixpoint_allnodes cdhp successors transf) with
      | None => None
      | Some res => Some (AI.bots, PTree.map transf_blk (snd res))
      end.

    Definition analyze_func_backward (** thrd *)
               (func: Func) 
               (successors: BBlock.t -> list (Language.fid)) 
               (transf_blk': AI.t -> BBlock.t -> AI.b): option AI.ACdhp := 
      let (cdhp, fid) := func in 
      let transf_blk := (fun n ai =>
                           match (cdhp!n) with 
                           | Some b => transf_blk' ai b 
                           | None => AI.Atom ai
                           end
                        ) in
      fixpoint_blk_backward cdhp successors (transf_blk).

    Theorem analyze_func_solution_backward_get
            succ transf_blk acdhp cdhp_s fentry_s n blk ablk
            (WF_TRANS_BACK: forall l blk, (AI.getLast (transf_blk l blk)) = l)
            (ANALYSIS: analyze_func_backward (cdhp_s, fentry_s) succ transf_blk = Some acdhp)
            (GET_BLK: cdhp_s ! n = Some blk)
            (ANALYSIS_GET: (snd acdhp) ! n = Some ablk):
      transf_blk (AI.getLast acdhp !! n) blk = ablk.
    Proof.
      unfold analyze_func_backward in ANALYSIS.
      unfold fixpoint_blk_backward in ANALYSIS.
      remember  (fun (n : positive) (ai : AI.t) =>
                   AI.getFirst match cdhp_s ! n with
                               | Some b => transf_blk ai b
                               | None => AI.Atom ai
                               end) as transf.
      destruct (fixpoint_allnodes cdhp_s succ transf) eqn:ANALYZE_NODE; tryfalse. inv ANALYSIS; simpl.
      unfold "!!"; simpl.
      rewrite PTree.gmap. rewrite GET_BLK.
      unfold option_map; simpl.
      destruct ((snd t) ! n) eqn:Heqe; simpl.
      unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
      rewrite Heqe.
      rewrite WF_TRANS_BACK; eauto. simpls.
      rewrite PTree.gmap in ANALYSIS_GET. unfold option_map in ANALYSIS_GET.
      unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
      rewrite Heqe in ANALYSIS_GET. rewrite GET_BLK in ANALYSIS_GET. inv ANALYSIS_GET; eauto.
      simpl in *.
      rewrite PTree.gmap in ANALYSIS_GET.
      unfold option_map in ANALYSIS_GET.
      unfold DS.AI.t, AI.t in *. 
      rewrite Heqe in ANALYSIS_GET. tryfalse.
    Qed.

    Theorem analyze_func_solution_backward_get_none
            succ transf_blk acdhp cdhp_s fentry_s n blk 
            (WF_TRANS_BACK: forall l blk, (AI.getLast (transf_blk l blk)) = l)
            (ANALYSIS: analyze_func_backward (cdhp_s, fentry_s) succ transf_blk = Some acdhp)
            (GET_BLK: cdhp_s ! n = Some blk)
            (ANALYSIS_GET: (snd acdhp) ! n = None):
      acdhp !! n = AI.bots.
    Proof.
      unfold analyze_func_backward in ANALYSIS.
      unfold fixpoint_blk_backward in ANALYSIS.
      remember  (fun (n : positive) (ai : AI.t) =>
                   AI.getFirst match cdhp_s ! n with
                               | Some b => transf_blk ai b
                               | None => AI.Atom ai
                               end) as transf.
      destruct (fixpoint_allnodes cdhp_s succ transf) eqn:ANALYZE_NODE; tryfalse. inv ANALYSIS; simpl. 
      unfold "!!"; simpl.
      rewrite PTree.gmap. rewrite GET_BLK.
      unfold option_map; simpl.
      simpls. rewrite PTree.gmap in ANALYSIS_GET.
      unfold option_map in ANALYSIS_GET.
      destruct ((snd t) ! n) eqn:Heqe; simpl.
      unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
      rewrite Heqe in ANALYSIS_GET. tryfalse.
      unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
      rewrite Heqe.
      eauto.
    Qed.

    Theorem analyze_func_solution_backward':
      forall succ transf_blk acdhp cdhp_s fentry_s n blk s blk_s,
        (forall l blk, (AI.getLast (transf_blk l blk)) = l) ->
        analyze_func_backward (cdhp_s, fentry_s) succ transf_blk = Some acdhp ->
        cdhp_s ! n = Some blk ->
        In s (succ blk) -> cdhp_s ! s = Some blk_s ->
        AI.ge (AI.getLast acdhp !! n)  (AI.getFirst (transf_blk (AI.getLast (acdhp !! s)) blk_s)).
    Proof.
      introv GET_LAST_PROP ANALYZE BLK SUCC SUCC_BLK.
      unfold analyze_func_backward in ANALYZE.
      unfold fixpoint_blk_backward in ANALYZE.
      remember  (fun (n : positive) (ai : AI.t) =>
                   AI.getFirst match cdhp_s ! n with
                               | Some b => transf_blk ai b
                               | None => AI.Atom ai
                               end) as transf.
      destruct (fixpoint_allnodes cdhp_s succ transf) eqn:ANALYZE_NODE; tryfalse.
      lets ANALYZE_NODE': ANALYZE_NODE.
      eapply fixpoint_allnodes_solution with (instr := blk) in ANALYZE_NODE'; eauto.
      subst transf. rewrite SUCC_BLK in ANALYZE_NODE'.
      assert (GET: AI.getLast acdhp !! n = t !! n).
      { 
        inv ANALYZE. unfold "!!" in *; simpls.
        rewrite PTree.gmap. unfold option_map. rewrite BLK.
        destruct ((snd t) ! n) eqn:Heqe.
        unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
        rewrite Heqe. eauto.
        unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
        rewrite Heqe.
        eapply fixpoint_allnodes_solution_fst_bot in ANALYZE_NODE.
        unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
        rewrite ANALYZE_NODE. simpls. eauto.
      }
      rewrite GET.
      assert (GET': AI.getLast acdhp !! s = t !! s).
      {
        clear GET. inv ANALYZE.
        unfold "!!"; simpls. rewrite PTree.gmap.
        unfold option_map.
        destruct ((snd t) ! s) eqn:Heqe; simpls.
        unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
        rewrite Heqe. rewrite SUCC_BLK. eauto.
        unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
        rewrite Heqe.
        eapply fixpoint_allnodes_solution_fst_bot in ANALYZE_NODE.
        unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
        rewrite ANALYZE_NODE. eauto.
      }
      rewrite GET'. eauto.
    Qed.
      

    Theorem analyze_func_solution_backward:
      forall succ transf_blk acdhp cdhp_s fentry_s n blk s,
        (** wf transf_blk*)
        (forall l blk, (AI.getLast (transf_blk l blk)) = l) ->
        analyze_func_backward (cdhp_s, fentry_s) succ transf_blk = Some acdhp ->
        cdhp_s ! n = Some blk ->
        In s (succ blk) ->
        AI.ge (AI.getLast acdhp !! n)  (AI.getFirst (acdhp !! s)).
    Proof.
      introv GET_LAST_PROP ANALYZE BLK SUCC.
      unfold analyze_func_backward in ANALYZE.
      unfold fixpoint_blk_backward in ANALYZE.
      remember  (fun (n : positive) (ai : AI.t) =>
                   AI.getFirst match cdhp_s ! n with
                               | Some b => transf_blk ai b
                               | None => AI.Atom ai
                               end) as transf.
      destruct (fixpoint_allnodes cdhp_s succ transf) eqn:ANALYZE_NODE; tryfalse.
      lets ANALYZE_NODE': ANALYZE_NODE.
      eapply fixpoint_allnodes_solution in ANALYZE_NODE'; eauto.  
      assert (TRANS: L.ge (transf s (t!!s)) (AI.getFirst acdhp!!s)).
      {
        inv ANALYZE. unfold "!!"; simpls.
        rewrite PTree.gmap. unfold option_map.
        destruct ((snd t) ! s) eqn:Heqe.
        unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
        rewrite Heqe.
        eapply L.ge_refl. eapply L.eq_refl.
        unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
        rewrite Heqe. simpls.
        eapply L.ge_bot.
      } 
      assert (GET: AI.getLast acdhp !! n = t !! n).
      { 
        inv ANALYZE. unfold "!!" in *; simpls.
        rewrite PTree.gmap. unfold option_map. rewrite BLK.
        destruct ((snd t) ! n) eqn:Heqe.
        unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
        rewrite Heqe. eauto.
        unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
        rewrite Heqe.
        eapply fixpoint_allnodes_solution_fst_bot in ANALYZE_NODE.
        unfold DS.AI.t, AI.t in *. unfold DS.L.t in *.
        rewrite ANALYZE_NODE. simpls. eauto.
      }
      rewrite GET. unfold AI.ge.
      eapply L.ge_trans; eauto.
    Qed.
  End RtlSolverBackward.

End Backward_Dataflow_Solver.

(** ** Node sets *)

(** We now define implementations of the [NODE_SET] interface
  appropriate for forward and backward dataflow analysis.
  As mentioned earlier, we aim for a traversal of the CFG nodes
  in reverse postorder (for forward analysis) or postorder
  (for backward analysis).  We take advantage of the following
  fact, valid for all CFG generated by translation from Cminor:
  the enumeration [n-1], [n-2], ..., 3, 2, 1 where [n] is the
  top CFG node is a reverse postorder traversal.
  Therefore, for forward analysis, we will use an implementation
  of [NODE_SET] where the [pick] operation selects the
  greatest node in the working list.  For backward analysis,
  we will similarly pick the smallest node in the working list. *)

Require Import Heaps.

Module NodeSetForward <: NODE_SET.
  Definition t := PHeap.t.
  Definition empty := PHeap.empty.
  Definition add (n: positive) (s: t) : t := PHeap.insert n s.
  Definition pick (s: t) :=
    match PHeap.findMax s with
    | Some n => Some(n, PHeap.deleteMax s)
    | None => None
    end.
  Definition all_nodes {A: Type} (code: PTree.t A) :=
    PTree.fold (fun s pc instr => PHeap.insert pc s) code PHeap.empty.
  Definition In := PHeap.In.
  
  Lemma empty_spec:
    forall n, ~In n empty.
  Proof.
    intros. apply PHeap.In_empty.
  Qed.
  
  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof.
    intros. rewrite PHeap.In_insert. unfold In. intuition.
  Qed.
  
  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick. caseEq (PHeap.findMax s); intros.
    congruence.
    apply PHeap.findMax_empty. auto.
  Qed.
  
  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
              forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick. caseEq (PHeap.findMax s); intros.
    inv H0.
    generalize (PHeap.In_deleteMax s n n' H). unfold In. intuition.
    congruence.
  Qed.
  
  Lemma all_nodes_spec:
    forall A (code: PTree.t A) n instr,
      code!n = Some instr -> In n (all_nodes code).
  Proof.
    intros A code n instr.
    apply PTree_Properties.fold_rec with
        (P := fun m set => m!n = Some instr -> In n set).
    (* extensionality *)
    intros. apply H0. rewrite H. auto.
    (* base case *)
    rewrite PTree.gempty. congruence.
    (* inductive case *)
    intros. rewrite PTree.gsspec in H2. rewrite add_spec.
    destruct (peq n k). auto. eauto.
  Qed.
End NodeSetForward.

Module NodeSetBackward <: NODE_SET.
  Definition t := PHeap.t.
  Definition empty := PHeap.empty.
  Definition add (n: positive) (s: t) : t := PHeap.insert n s.
  Definition pick (s: t) :=
    match PHeap.findMin s with
    | Some n => Some(n, PHeap.deleteMin s)
    | None => None
    end.
  Definition all_nodes {A: Type} (code: PTree.t A) :=
    PTree.fold (fun s pc instr => PHeap.insert pc s) code PHeap.empty.
  Definition In := PHeap.In.
  
  Lemma empty_spec:
    forall n, ~In n empty.
  Proof NodeSetForward.empty_spec.
  
  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof NodeSetForward.add_spec.
  
  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick. caseEq (PHeap.findMin s); intros.
    congruence.
    apply PHeap.findMin_empty. auto.
  Qed.
  
  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
              forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick. caseEq (PHeap.findMin s); intros.
    inv H0.
    generalize (PHeap.In_deleteMin s n n' H). unfold In. intuition.
    congruence.
  Qed.
  
  Lemma all_nodes_spec:
    forall A (code: PTree.t A) n instr,
      code!n = Some instr -> In n (all_nodes code).
  Proof NodeSetForward.all_nodes_spec.
End NodeSetBackward.


