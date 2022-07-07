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
Require Import Lib_Ordering.
Set Implicit Arguments.

(** * Loop Invariant Detecting *)

(** This file defines the analysis to detect loop invariants. *)

(** ** Evaluation of the Dominator *)
(** For each block labelled f, its NDominators returns whether a node f' is
    its dominators.
    If f' maps to true, it means that f' is not the dominator of f;
    if f' maps to false, it means that f' is the dominator of f. *)
Module NDominators := LPMap(LBoolean).
Module NDomDS := Dataflow_Solver(NDominators)(NodeSetForward).

(** [dominator] justifies that whether the block labelled f' is the
    dominator of the block that we focus on. *) 
Definition dominator (ndom: NDominators.t) (f': positive) :=
  if NDominators.get f' ndom then false else true.

(** ** Back Edge *)
(** After evaluating the dominators of each block, we can find the loop.
    l_entry and l_exit are entry and exit of a loop,
    if l_exit points to l_entry and l_entry dominates l_exit. *) 
Definition back_edge (l_exit l_entry: positive)
           (ndom: NDominators.t) (cdhp: CodeHeap) :=
  match PTree.get l_exit cdhp with
  | Some BB =>
    In l_entry (succ BB) /\ dominator ndom l_entry = true
  | None => False
  end.

Lemma back_edge_eq_dec
      l_exit l_entry ndom cdhp:
  {back_edge l_exit l_entry ndom cdhp} + {~ back_edge l_exit l_entry ndom cdhp}.
Proof.
  unfold back_edge.
  destruct (cdhp ! l_exit) eqn:EXIT; ss.
  2: { right. ii; eauto. }
  pose proof in_dec as LIST_IN_EQ_DEC.
  specialize (LIST_IN_EQ_DEC Language.fid).
  assert (forall x y: positive, {x = y} + {x <> y}).
  {
    ii. eapply Pos.eq_dec; eauto.
  } 
  eapply LIST_IN_EQ_DEC with (l := succ t) (a := l_entry) in H.
  destruct H.
  {
    destruct (dominator ndom l_entry) eqn:IS_IN_DOM; ss.
    eauto.
    right. ii. des. ss.
  }
  {
    right. ii. des. eapply n in H. tryfalse.
  }
Qed.

(** Finding the back edge, whose exit node is l_exit. *)
Fixpoint back_edge' (l_exit: positive) (ls: list (positive * BBlock.t))
         (ndom: NDominators.t) (cdhp: CodeHeap) :=
  match ls with
  | nil => nil
  | (l, _) :: ls' =>
    if back_edge_eq_dec l_exit l ndom cdhp then
      (l_exit, l) :: back_edge' l_exit ls' ndom cdhp
    else
      back_edge' l_exit ls' ndom cdhp
  end.

(** Finding all the back edges in the code heap. *) 
Fixpoint back_edges' (ls: list (positive * BBlock.t))
         (ndoms: PMap.t NDomDS.L.t) (cdhp: CodeHeap) :=
  match ls with
  | nil => nil
  | (l_exit, _) :: ls' =>
    match ((snd ndoms) ! l_exit) with
    | None => back_edges' ls' ndoms cdhp
    | Some ndom =>
      (back_edge' l_exit (PTree.elements cdhp) ndom cdhp)
        ++ back_edges' ls' ndoms cdhp
    end
  end.
                                                         
Definition back_edges (ndoms: PMap.t NDomDS.L.t) (cdhp: CodeHeap):
  list (Language.fid * Language.fid) :=
  back_edges' (PTree.elements cdhp) ndoms cdhp.  

(** ** Detecting Loops *)
(** We define [Reach](l, l', cdhp, l_entry) to determinate
    whether l can reach l' and does not pass l_entry *)     
Fixpoint Reach'(l l': positive) (cdhp: CodeHeap) (l_entry: positive)
         (ls: list positive) (n: nat) : bool :=
  match n with
  | 0%nat => false
  | S n' =>
    match ls with
    | nil => false
    | l0 :: ls' =>
      if Ident.eq_dec l0 l' then true else
        if Ident.eq_dec l0 l_entry then
          Reach' l l' cdhp l_entry ls' n'
        else
          match (PTree.get l0 cdhp) with
          | None => Reach' l l' cdhp l_entry ls' n'
          | Some BB =>
            match (Reach' l0 l' cdhp l_entry (succ BB) n') with
            | true => true
            | false => 
              Reach' l l' cdhp l_entry ls' n'
            end
          end
    end
  end. 

Definition Reach (l l': Language.fid) (cdhp: CodeHeap) (l_entry: positive) : bool :=
  if Ident.eq_dec l l_entry then false else
    match (PTree.get l cdhp) with
    | None => false
    | Some BB =>
      Reach' l l' cdhp l_entry (succ BB) (Pos.to_nat PrimIter.num_iterations)
    end.

(** ** Natural Loop *)
(** [natural_loop] returns the list of nodes that belong to the loop,
    where l_exit and l_entry construct the back edge of the loop. *)
Definition in_loop (l l_exit l_entry: positive) (cdhp: CodeHeap) (ndom: NDominators.t) :=
  dominator ndom l_entry && Reach l l_exit cdhp l_entry.
Fixpoint natural_loop' 
         (l_exit l_entry: Language.fid) (cdhp: CodeHeap) (ndoms: PMap.t NDomDS.L.t)
         (ls: list (Language.fid * BBlock.t)) :=
  match ls with
  | nil => IdentSet.empty
  | (l, _) :: ls' =>
    match ((snd ndoms) ! l) with
    | None => IdentSet.empty
    | Some ndom => if in_loop l l_exit l_entry cdhp ndom then
                    IdentSet.add l (natural_loop' l_exit l_entry cdhp ndoms ls')
                  else
                    natural_loop' l_exit l_entry cdhp ndoms ls'
    end
  end. 
  
Definition natural_loop (l_exit l_entry: positive) (cdhp: CodeHeap) (ndoms: PMap.t NDomDS.L.t) :=
  natural_loop' l_exit l_entry cdhp ndoms (PTree.elements cdhp).

(** ** Detecting Loops  *)
(** [det_loops] returns the list of loops.
    The loop is represented as a tuple:
    - l_entry: entry point;
    - l_exit: exit point;
    - ls: list of nodes in the loop. *)
Fixpoint det_loops' (cdhp: CodeHeap) (ndoms: PMap.t NDomDS.L.t)
         (bk_edges: list (positive * positive)) :=
  match bk_edges with
  | nil => nil
  | (l_exit, l_entry) :: bk_edges' =>
    match (PTree.get l_exit cdhp), (PTree.get l_entry cdhp) with
    | Some BB_exit, Some BB_entry => 
      (l_entry, l_exit, natural_loop l_exit l_entry cdhp ndoms) :: det_loops' cdhp ndoms bk_edges'
    | _, _ => det_loops' cdhp ndoms bk_edges'
    end
  end. 

Definition transf (p: positive) (ndom: NDomDS.L.t) :=
  NDominators.set p false ndom. 

Definition det_loops (cdhp: CodeHeap) (ep: positive) :=
  match NDomDS.fixpoint cdhp succ transf ep NDominators.top with
  | Some ndoms =>
    det_loops' cdhp ndoms (back_edges ndoms cdhp)
  | None => nil
  end.

(** ** Loop Invariants *)
Inductive LOOP_INV : Set :=
| LINV_EXPR (r: Reg.t) (e: Inst.expr)
| LINV_LOC (r: Reg.t) (loc: Loc.t). 

Fixpoint expr_is_loop_inv (e: Inst.expr) (loop_invs: list LOOP_INV) :=
  match loop_invs with
  | nil => False
  | (LINV_EXPR r' e') :: loop_invs =>
    if Inst.expr_eq_dec e e' then True
    else  expr_is_loop_inv e loop_invs
  | _ :: loop_invs => expr_is_loop_inv e loop_invs
  end.

Lemma in_expr_linv_eq_dec:
  forall(loop_invs: list LOOP_INV) e,
    {expr_is_loop_inv e loop_invs} + {~ expr_is_loop_inv e loop_invs}.
Proof.
  induction loop_invs; ss; ii.
  - right. ii; ss.
  - destruct a; ss.
    des_if; eauto.
Qed. 

(** [not_write_regs](rs, RS_W) returns true,
    if all the registers in rs have not been written. *)
Fixpoint not_write_regs (rs: list Reg.t) (RS_W: RegSet.t) :=
  match rs with
  | r :: rs' => if RegSet.mem r RS_W then false
               else not_write_regs rs' RS_W
  | nil => true
  end. 

(** An expression e is an loop invariant, if
    - all its registers have not been written;
    - it has not been detected as a loop invariant.

    Reading from a location loc is an loop invariant, if
    - it is a non-atomic location;
    - it has not been written by other instrucitons.
 *) 
Fixpoint loop_invB (BB: BBlock.t) (RS_W: RegSet.t) (LS_W: LocSet.t)
         (max_reg: Reg.t) (loop_invs: list LOOP_INV) (lo: Ordering.LocOrdMap) := 
  match BB with
  | (Inst.assign r e) ## BB' =>
    if (not_write_regs (RegSet.elements (Inst.regs_of_expr e)) RS_W) then
      if in_expr_linv_eq_dec loop_invs e then
        loop_invB BB' RS_W LS_W max_reg loop_invs lo
      else
        loop_invB BB' RS_W LS_W (Pos.succ max_reg) ((LINV_EXPR max_reg e) :: loop_invs) lo
    else
      loop_invB BB' RS_W LS_W max_reg loop_invs lo
  | (Inst.load r loc Ordering.plain) ## BB' =>
    match (lo loc) with
    | Ordering.nonatomic =>
      if LocSet.mem loc LS_W then
        loop_invB BB' RS_W LS_W max_reg loop_invs lo
      else
        loop_invB BB' RS_W LS_W (Pos.succ max_reg) ((LINV_LOC max_reg loc) :: loop_invs) lo
    | Ordering.atomic =>
      loop_invB BB' RS_W LS_W max_reg loop_invs lo
    end
  | _ ## BB' =>
    loop_invB BB' RS_W LS_W max_reg loop_invs lo
  | _ => (loop_invs, max_reg)
  end.

Fixpoint loop_invBS (BS: list BBlock.t) (RS_W: RegSet.t) (LS_W: LocSet.t)
         (max_reg: Reg.t) (loop_invs: list LOOP_INV) (lo: Ordering.LocOrdMap) :=
  match BS with
  | BB :: BS' =>
    match loop_invB BB RS_W LS_W max_reg loop_invs lo with
    | (loop_invs', max_reg') =>
      loop_invBS BS' RS_W LS_W max_reg' loop_invs' lo
    end
  | nil => (loop_invs, max_reg)
  end.

(** [loop_invC] returns the loop invariants in the code heap. *)
Definition RS_W_instr (c: Inst.t) :=
  match c with
  | Inst.skip => RegSet.empty
  | Inst.assign reg rhs => RegSet.singleton reg
  | Inst.load reg loc _ => RegSet.singleton reg
  | Inst.store loc rhs _ => RegSet.empty
  | Inst.cas reg loc er ew _ _ => RegSet.singleton reg
  | Inst.print e => RegSet.empty 
  | _ => RegSet.empty
  end.

Definition LS_W_instr (c: Inst.t) :=
  match c with
  | Inst.skip => LocSet.empty
  | Inst.assign reg rhs => LocSet.empty
  | Inst.load reg loc _ => LocSet.empty
  | Inst.store loc rhs _ => LocSet.singleton loc
  | Inst.cas reg loc er ew _ _ => LocSet.empty
  | Inst.print e => LocSet.empty 
  | _ => LocSet.empty
  end.

Fixpoint RS_LS_W_evalB (BB: BBlock.t) :=
  match BB with
  | c ## BB' => match RS_LS_W_evalB BB' with
               | (rsw, lsw) =>
                 (RegSet.union (RS_W_instr c) rsw, LocSet.union (LS_W_instr c) lsw)
               end
  | _ => (RegSet.empty, LocSet.empty)
  end.

Fixpoint RS_LS_W_eval (ls: list Language.fid) (cdhp: CodeHeap) :=
  match ls with
  | l :: ls' =>
    match (PTree.get l cdhp) with
    | Some BB =>
      let (rsw1, lsw1) := RS_LS_W_evalB BB in
      let (rsw2, lsw2) := RS_LS_W_eval ls' cdhp in 
      (RegSet.union rsw1 rsw2, LocSet.union lsw1 lsw2)
    | None => RS_LS_W_eval ls' cdhp
    end
  | nil => (RegSet.empty, LocSet.empty)
  end.

Fixpoint BS_in_loops (ls: list Language.fid) (cdhp: CodeHeap) :=
  match ls with
  | l :: ls' =>
    match (PTree.get l cdhp) with
    | Some BB => BB :: (BS_in_loops ls' cdhp)
    | None => BS_in_loops ls' cdhp
    end
  | nil => nil
  end. 

Fixpoint loop_invC' (loops: list (positive * positive * IdentSet.t))
         (max_reg0: Reg.t) (cdhp: CodeHeap) (lo: Ordering.LocOrdMap) :=
  match loops with
  | (l_entry, l_exit, iset) :: loops' =>
    let ls := IdentSet.elements iset in
    let (rsw, lsw) := RS_LS_W_eval ls cdhp in 
    let BS := BS_in_loops ls cdhp in
    let (loop_invs, max_reg) :=
        loop_invBS BS rsw lsw max_reg0 nil lo in
    (l_entry, l_exit, loop_invs) :: loop_invC' loops' max_reg cdhp lo
  | nil => nil
  end.

Definition loop_invC (lo: Ordering.LocOrdMap) (func: Func) :=
  let (cdhp, ep) := func in
  let loops := det_loops cdhp ep in
  let rs := regs_of_cdhp cdhp in
  match (RegSet.max_elt rs) with
  | None => loop_invC' loops 1%positive cdhp lo
  | Some max_reg => loop_invC' loops (Pos.succ max_reg) cdhp lo
  end.

Lemma loopinv_det_prop1:
  forall loops max_reg cdhp lo l_entry l_exit loopinvs
    (IN: In (l_entry, l_exit, loopinvs) (loop_invC' loops max_reg cdhp lo)),
  exists ls, In (l_entry, l_exit, ls) loops.
Proof.
  induction loops; ii; ss.
  destruct a. destruct p.
  destruct (RS_LS_W_eval (IdentSet.elements t) cdhp) eqn:Heqe1; ss.
  destruct (loop_invBS (BS_in_loops (IdentSet.elements t) cdhp) t0 t1 max_reg nil lo) eqn:Heqe2; ss.
  des1. inv IN; ss. eexists. left. eauto.
  eapply IHloops in IN; eauto. des1.
  exists ls. right; eauto.
Qed.

Lemma loopinv_det_prop2':
    forall bk_edges cdhp ndoms l_entry l_exit ls
      (IN: In (l_entry, l_exit, ls) (det_loops' cdhp ndoms bk_edges)),
      <<ENTRY_IN: exists BB, PTree.get l_entry cdhp = Some BB>> /\
      <<EXIT_IN: exists BB, PTree.get l_exit cdhp = Some BB>>.
Proof.
  induction bk_edges; ii; ss.
  destruct a; ss.
  destruct (cdhp ! p) eqn:GET_FID1; ss;
    destruct (cdhp ! p0) eqn:GET_FID2; ss;
      try solve [eapply IHbk_edges in IN; eauto].
  des1. inv IN; ss. split; eauto.
  eapply IHbk_edges in IN; eauto.
Qed.

Lemma loopinv_det_prop2
          cdhp ep l_entry l_exit ls
          (IN: In (l_entry, l_exit, ls) (det_loops cdhp ep)):
  <<ENTRY_IN: exists BB, PTree.get l_entry cdhp = Some BB>> /\
  <<EXIT_IN: exists BB, PTree.get l_exit cdhp = Some BB>>.
Proof.
  unfold det_loops in *.
  destruct (NDomDS.fixpoint cdhp succ transf ep NDominators.top) eqn:Heqe; ss.
  eapply loopinv_det_prop2'; eauto.
Qed.
  
Lemma wf_loop_invC1
      cdhp l_entry l_exit loopinvs lo ep
      (LOOP_INV: In (l_entry, l_exit, loopinvs) (loop_invC lo (cdhp, ep))):
  <<ENTRY_IN: exists BB, PTree.get l_entry cdhp = Some BB>> /\
  <<EXIT_IN: exists BB, PTree.get l_exit cdhp = Some BB>>.
Proof.
  unfold loop_invC in *.
  destruct (RegSet.max_elt (regs_of_cdhp cdhp)) eqn: MAX_REG.
  - renames e to max_reg.
    eapply loopinv_det_prop1 in LOOP_INV; eauto. des1.
    eapply loopinv_det_prop2; eauto.
  - eapply loopinv_det_prop1 in LOOP_INV; eauto. des1.
    eapply loopinv_det_prop2; eauto.
Qed.

Lemma loop_invB_reg_prop:
  forall BB rsw lsw max_reg loopinvs lo loopinvs' t
    (LOOP_INVB: loop_invB BB rsw lsw max_reg loopinvs lo = (loopinvs', t)),
    (max_reg <= t)%positive.
Proof.
  induction BB; ii; ss; eauto;
    try solve [inv LOOP_INVB; rewrite Pos.compare_refl in H; ss].
  destruct c; ss; eauto; try solve [eapply IHBB in LOOP_INVB; eauto].
  des_ifH LOOP_INVB; ss;
    try solve [eapply IHBB in LOOP_INVB; eauto].
  des_ifH LOOP_INVB; ss;
    try solve [eapply IHBB in LOOP_INVB; eauto].
  eapply IHBB in LOOP_INVB; eauto.
  assert (SUCC_LT: (max_reg < Pos.succ max_reg)%positive).
  {
    eapply Pos.lt_succ_diag_r; eauto.
  }
  assert (SUCC_LT': (max_reg < t)%positive).
  {
    eapply Pos.lt_le_trans; eauto.
  }
  rewrite SUCC_LT' in H. ss.
  pose proof (nonatomic_or_atomic or). des1.
  - subst.
    destruct (lo loc) eqn:LOC_AT_OR_NA; ss.
    eapply IHBB in LOOP_INVB; eauto.
    des_ifH LOOP_INVB; ss.
    {
      eapply IHBB in LOOP_INVB; eauto.
    }
    {
      eapply IHBB in LOOP_INVB; eauto.
      assert (SUCC_LT: (max_reg < Pos.succ max_reg)%positive).
      {
        eapply Pos.lt_succ_diag_r; eauto.
      }
      assert (SUCC_LT': (max_reg < t)%positive).
      {
        eapply Pos.lt_le_trans; eauto.
      }
      rewrite SUCC_LT' in H. ss.
    }
  - assert (match or with
              | Ordering.plain =>
                  match lo loc with
                  | Ordering.atomic => loop_invB BB rsw lsw max_reg loopinvs lo
                  | Ordering.nonatomic =>
                      if LocSet.mem loc lsw
                      then loop_invB BB rsw lsw max_reg loopinvs lo
                      else loop_invB BB rsw lsw (Pos.succ max_reg) (LINV_LOC max_reg loc :: loopinvs) lo
                  end
              | _ => loop_invB BB rsw lsw max_reg loopinvs lo
            end =
            loop_invB BB rsw lsw max_reg loopinvs lo).
    {
      destruct or; ss; eauto.
    }
    rewrite H1 in LOOP_INVB. clear H1.
    eapply IHBB in LOOP_INVB; eauto.
Qed.

Lemma loop_invB_reg_prop':
  forall BB rsw lsw max_reg loopinvs loopinvs' lo max_reg' r
    (LOOP_INVB: loop_invB BB rsw lsw max_reg loopinvs lo = (loopinvs', max_reg'))
    (IN: (exists e, In (LINV_EXPR r e) loopinvs') \/ (exists loc, In (LINV_LOC r loc) loopinvs')),
    ((exists e, In (LINV_EXPR r e) loopinvs) \/ (exists loc, In (LINV_LOC r loc) loopinvs)) \/
    (max_reg <= r)%positive.
Proof.
  induction BB; ii; ss; eauto;
    try solve [inv LOOP_INVB; eauto].
  destruct c; ss; eauto.
  - des_ifH LOOP_INVB; ss.
    des_ifH LOOP_INVB; ss;
      try solve [eapply IHBB in LOOP_INVB; eauto].
    eapply IHBB in LOOP_INVB; eauto.
    des1.
    {
      des1; ss. des1; ss. des1. inv LOOP_INVB. right.
      eapply POrderedType.Positive_as_DT.le_refl; eauto.
      left. eauto.
      des1. des1. inv LOOP_INVB. eauto.
    }
    {
      assert (SUCC_LT: (max_reg < Pos.succ max_reg)%positive).
      {
        eapply Pos.lt_succ_diag_r; eauto.
      }
      assert (SUCC_LT': (max_reg < r)%positive).
      {
        eapply Pos.lt_le_trans; eauto.
      }
      right. eapply POrderedType.Positive_as_DT.lt_le_incl; eauto.
    }
    eapply IHBB in LOOP_INVB; eauto.
  - pose proof (nonatomic_or_atomic or). des1.
    {
      subst.
      destruct (lo loc) eqn:LOC; ss.
      eapply IHBB in LOOP_INVB; eauto.
      des_ifH LOOP_INVB; ss; eauto.
      eapply IHBB in LOOP_INVB; eauto.
      des1.
      des1.
      des1; ss. des1. inv LOOP_INVB. eauto.
      des1; ss. des1. inv LOOP_INVB.
      right. eapply POrderedType.Positive_as_DT.le_refl; eauto.
      eauto.
      assert (SUCC_LT: (max_reg < Pos.succ max_reg)%positive).
      {
        eapply Pos.lt_succ_diag_r; eauto.
      }
      assert (SUCC_LT': (max_reg < r)%positive).
      {
        eapply Pos.lt_le_trans; eauto.
      }
      right. eapply POrderedType.Positive_as_DT.lt_le_incl; eauto.
    }
    {
      assert (match or with
              | Ordering.plain =>
                  match lo loc with
                  | Ordering.atomic => loop_invB BB rsw lsw max_reg loopinvs lo
                  | Ordering.nonatomic =>
                      if LocSet.mem loc lsw
                      then loop_invB BB rsw lsw max_reg loopinvs lo
                      else loop_invB BB rsw lsw (Pos.succ max_reg) (LINV_LOC max_reg loc :: loopinvs) lo
                  end
              | _ => loop_invB BB rsw lsw max_reg loopinvs lo
              end = loop_invB BB rsw lsw max_reg loopinvs lo).
      {
        destruct or; ss.
      }
      rewrite H0 in LOOP_INVB; clear H0; ss.
      eapply IHBB in LOOP_INVB; eauto.
    }
Qed.
  
Lemma loop_invBS_reg_prop:
  forall BS rsw lsw max_reg max_reg' loopinvs0 loopinvs max_reg'' lo r
    (LOOP_INVBS: loop_invBS BS rsw lsw max_reg' loopinvs0 lo = (loopinvs, max_reg''))
    (REG: (exists e, In (LINV_EXPR r e) loopinvs) \/ (exists loc, In (LINV_LOC r loc) loopinvs))
    (GT: (max_reg < max_reg')%positive),
    ((exists e, In (LINV_EXPR r e) loopinvs0) \/ (exists loc, In (LINV_LOC r loc) loopinvs0)) \/ 
    (max_reg' <= r)%positive.
Proof.
  induction BS; ii; ss.
  - inv LOOP_INVBS.
    left. eauto.
  - destruct (loop_invB a rsw lsw max_reg' loopinvs0 lo) eqn:Heqe; ss. 
    eapply IHBS in LOOP_INVBS; eauto.
    2: {  
      instantiate (1 := max_reg). renames a to BB.
      eapply loop_invB_reg_prop in Heqe; eauto. 
      eapply Pos.lt_le_trans; eauto. }
    renames a to BB. des1.
    {
      eapply loop_invB_reg_prop'; eauto.
    }
    {
      eapply loop_invB_reg_prop in Heqe; eauto.
      right. eapply Pos.le_trans; eauto.
    }
Qed.

Lemma loop_invBS_reg_prop2:
  forall BS rsw lsw max_reg max_reg' loopinvs0 loopinvs lo
    (LOOP_INVBS: loop_invBS BS rsw lsw max_reg loopinvs0 lo = (loopinvs, max_reg')),
    (max_reg <= max_reg')%positive.
Proof.
  induction BS; ii; ss; eauto.
  - inv LOOP_INVBS. rewrite Pos.compare_refl in H; ss.
  - destruct (loop_invB a rsw lsw max_reg loopinvs0 lo) eqn:Heqe; ss.
    eapply IHBS in LOOP_INVBS; eauto.
    eapply loop_invB_reg_prop in Heqe; eauto.
    assert ((max_reg <= max_reg')%positive).
    eapply Pos.le_trans; eauto. tryfalse.
Qed.
    
Lemma wf_loop_invC2':
  forall loops max_reg max_reg' l_entry l_exit loopinvs lo cdhp r
    (MAX_REG: RegSet.max_elt (regs_of_cdhp cdhp) = Some max_reg)
    (IN: In (l_entry, l_exit, loopinvs) (loop_invC' loops max_reg' cdhp lo))
    (REG: (exists e, In (LINV_EXPR r e) loopinvs) \/ (exists loc, In (LINV_LOC r loc) loopinvs))
    (GT: (max_reg < max_reg')%positive),
    ~ (RegSet.In r (regs_of_cdhp cdhp)).
Proof.
  induction loops; ii; ss.
  destruct a; ss. destruct p; ss.
  destruct (RS_LS_W_eval (IdentSet.elements t) cdhp) eqn:Heqe1; ss.
  destruct (loop_invBS (BS_in_loops (IdentSet.elements t) cdhp) t0 t1 max_reg' nil lo) eqn:Heqe2; ss.
  destruct IN as [IN1 | IN2]; ss; eauto.
  - inv IN1.
    renames t0 to rsw, t1 to lsw.
    eapply loop_invBS_reg_prop in Heqe2; eauto.
    des1. simpl in Heqe2. des1; des1; ss.
    eapply RegSet.max_elt_spec2 in MAX_REG.
    2: { eapply H. }
    contradiction MAX_REG.
    assert ((max_reg < r)%positive).
    {
      eapply Pos.lt_le_trans; eauto.
    }
    eauto.
  - renames t0 to rsw, t1 to lsw.
    eapply IHloops in MAX_REG; eauto.
    eapply loop_invBS_reg_prop2 in Heqe2; eauto.
    eapply Pos.lt_le_trans; eauto.
Qed.
    
Lemma wf_loop_invC2
      cdhp l_entry l_exit loopinvs lo ep r
      (LOOP_INV: In (l_entry, l_exit, loopinvs) (loop_invC lo (cdhp, ep)))
      (REG: (exists e, In (LINV_EXPR r e) loopinvs) \/ (exists loc, In (LINV_LOC r loc) loopinvs)):
  <<NEW_REG: ~ (RegSet.In r (regs_of_cdhp cdhp))>>.
Proof.
  unfold loop_invC in *.
  destruct (RegSet.max_elt (regs_of_cdhp cdhp)) eqn:Heqe; ss.
  - renames e to max_reg.
    eapply wf_loop_invC2'; eauto.
    eapply Pos.lt_succ_diag_r; eauto.
  - eapply RegSet.max_elt_spec3 in Heqe.
    unfold RegSet.Empty in *. specialize (Heqe r). eauto.
Qed.

Lemma loop_invB_loc_prop:
  forall BB rsw lsw max_reg loopinvs0 lo loopinvs max_reg' r loc
    (LOOP_INVB: loop_invB BB rsw lsw max_reg loopinvs0 lo = (loopinvs, max_reg'))
    (IN: In (LINV_LOC r loc) loopinvs),
    In (LINV_LOC r loc) loopinvs0 \/ lo loc = Ordering.nonatomic.
Proof.
  induction BB; ii; ss;
    try solve [inv LOOP_INVB; eauto].
  destruct c; ss; eauto.
  - des_ifH LOOP_INVB; ss; eauto.
    des_ifH LOOP_INVB; ss; eauto.
    eapply IHBB in LOOP_INVB; eauto.
    des1; eauto.
    simpl in LOOP_INVB.
    des1; eauto.
    inv LOOP_INVB.
  - pose proof (nonatomic_or_atomic or); ss.
    des1; subst.
    {
      destruct (lo loc0) eqn:Heqe; ss; eauto.
      des_ifH LOOP_INVB; ss; eauto.
      eapply IHBB in LOOP_INVB; eauto.
      des1; eauto.
      simpl in LOOP_INVB. des1; eauto.
      inv LOOP_INVB. eauto.
    }
    {
      assert (match or with
              | Ordering.plain =>
                match lo loc0 with
                | Ordering.atomic => loop_invB BB rsw lsw max_reg loopinvs0 lo
                | Ordering.nonatomic =>
                  if LocSet.mem loc0 lsw
                  then loop_invB BB rsw lsw max_reg loopinvs0 lo
                  else loop_invB BB rsw lsw (Pos.succ max_reg) (LINV_LOC max_reg loc0 :: loopinvs0) lo
                end
              | _ => loop_invB BB rsw lsw max_reg loopinvs0 lo
              end =
              loop_invB BB rsw lsw max_reg loopinvs0 lo).
      {
        destruct or; ss; eauto.
      }
      rewrite H0 in LOOP_INVB. clear H0.
      eapply IHBB in LOOP_INVB; eauto.
    }
Qed.

Lemma loop_invBS_loc_prop:
  forall BS rsw lsw max_reg loopinvs0 lo loopinvs max_reg' r loc
    (LOOP_INVBS: loop_invBS BS rsw lsw max_reg loopinvs0 lo = (loopinvs, max_reg'))
    (LOC: In (LINV_LOC r loc) loopinvs),
    In (LINV_LOC r loc) loopinvs0 \/ lo loc = Ordering.nonatomic.
Proof.
  induction BS; ii; ss.
  - inv LOOP_INVBS. eauto.
  - destruct (loop_invB a rsw lsw max_reg loopinvs0 lo) eqn:Heqe; ss.
    eapply IHBS in LOOP_INVBS; eauto. des1; eauto.
    eapply loop_invB_loc_prop in Heqe; eauto.
Qed.

Lemma wf_loop_invC3':
  forall loops max_reg cdhp lo l_entry l_exit loopinvs r loc
    (IN: In (l_entry, l_exit, loopinvs) (loop_invC' loops max_reg cdhp lo))
    (LOC: In (LINV_LOC r loc) loopinvs),
    lo loc = Ordering.nonatomic.
Proof.
  induction loops; ii; ss; eauto.
  destruct a; ss. destruct p; ss.
  destruct (RS_LS_W_eval (IdentSet.elements t) cdhp) eqn:Heqe1; ss.
  destruct (loop_invBS (BS_in_loops (IdentSet.elements t) cdhp) t0 t1 max_reg nil lo) eqn:Heqe2; ss.
  des1.
  {
    inv IN.
    eapply loop_invBS_loc_prop in Heqe2; eauto. ss.
    des1; ss.
  }
  {
    eapply IHloops in IN; eauto.
  }
Qed.

Lemma wf_loop_invC3
      cdhp l_entry l_exit loopinvs lo ep loc
      (LOOP_INV: In (l_entry, l_exit, loopinvs) (loop_invC lo (cdhp, ep)))
      (LOC: exists r, In (LINV_LOC r loc) loopinvs):
  <<NA_LOC: lo loc = Ordering.nonatomic>>.
Proof.
  des1. unfold loop_invC in *; ss.
  destruct (RegSet.max_elt (regs_of_cdhp cdhp)) eqn:Heqe; ss.
  - eapply wf_loop_invC3'; eauto.
  - eapply wf_loop_invC3'; eauto.
Qed.

(** ** Detecting Loop Invariant in Code Heap *)
Definition det_loop_invs (prog: Code) (lo: Ordering.LocOrdMap) :=
  PTree.map (fun l (func: Func) =>
               let (cdhp, ep) := func in
               match (cdhp ! ep) with
               | Some BB => loop_invC lo (cdhp, ep)
               | None => nil
               end
            ) prog.
