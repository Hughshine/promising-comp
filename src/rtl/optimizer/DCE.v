Require Import RelationClasses.
Require Import List.

Require Import sflib.
From Paco Require Import paco.

Require Import Basic.
Require Import Axioms.
Require Import Loc.
Require Import Coqlib.
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

(** * Dead Code Elimination *)

(** Dead code elimination first uses liveness analysis to analyze program
    and then translates code according to the analysis result. *)

(** ** Code Transformation for the Single Instruction *)
(** [transform_inst] is the code transformation for a single instruction.
    It does three optimizations according to the result the liveness analysis:
    - [r := e]: optimized to skip, if the register r is dead;
    - [r := load(x, na)]: optimized to skip, if the register r is dead;
    - [store(x, e, na)]: optimized to skip, if the location x is dead. *)
Definition transform_inst (inst: Inst.t) (ai: LvLat.t): Inst.t :=
  match inst with
  | Inst.assign r e =>
    match ai with
    | (nr, nm) => if is_dead_reg r nr then Inst.skip else inst
    end
  | Inst.load r loc Ordering.plain =>
    match ai with
    | (nr, nm) => if is_dead_reg r nr then Inst.skip else inst
    end
  | Inst.store loc e Ordering.plain =>
    match ai with
    | (nr, nm) => if is_dead_loc loc nm then Inst.skip else inst
    end
  | _ => inst
  end.

Fixpoint transform_blk' (ai_blk: LvDS.AI.b) (b_s: BBlock.t): BBlock.t :=
  match b_s, ai_blk with
  | i##b_s', LvDS.AI.Cons ai ai_blk' =>
    let b_t' := transform_blk' ai_blk' b_s' in ((transform_inst i ai)##b_t')
  | _, _ => b_s
  end.

(** ** Code Transformation for the Basic Block *)
(** [transform_blk] is the code transformation for a basic block.
    It is a collection of the code transformation [transform_inst] for single instructions in the basic block. *)
Definition transform_blk (ai_blk: LvDS.AI.b) (b_s: BBlock.t): BBlock.t :=
  match ai_blk with
  | LvDS.AI.Cons ai ai_blk' => transform_blk' ai_blk' b_s
  | LvDS.AI.Atom ai => match (transf_blk LvDS.AI.bot b_s) with
                      | LvDS.AI.Cons ai' ai_blk' => transform_blk' ai_blk' b_s
                      | LvDS.AI.Atom _ => b_s (* this condition will never happen *)
                      end
  end.

(** ** Code Transformation for the Code Heap *)
(** [transform_cdhp] translates each basic block in the code heap by [transform_blk]. *)
Definition transform_cdhp (cdhp: CodeHeap) (analysis: LvDS.AI.ACdhp): CodeHeap := 
  PTree.map (fun (i: positive) (b: BBlock.t) => transform_blk (analysis!!i) b) cdhp.

Lemma transform_cdhp_prop
      C_src BB_src f afunc
      (GET: C_src ! f = Some BB_src):
  exists BB_tgt, (transform_cdhp C_src afunc) ! f = Some BB_tgt.
Proof.
  unfold transform_cdhp.
  rewrite PTree.gmap. unfold option_map.
  rewrite GET. eauto.
Qed.

(** ** Code Transformation for the Function *)
Definition transform_func (func: Func): option Func :=
  match LvDS.analyze_func_backward func succ transf_blk with
  | Some analysis =>
    let (cdhp, fid) := func in Some (transform_cdhp cdhp analysis, fid)
  (* transformation error, since there is no analysis result *)
  | None => None
  end.

(** ** Code Transformation for the Program *)
(** [transform_prog] translates each function in the program according to [transform_func]. *)
Fixpoint transform_prog (prog: Code): option Code :=
  match prog with
  | PTree.Leaf => Some PTree.Leaf
  | PTree.Node prog1 None prog2 =>
    match (transform_prog prog1), (transform_prog prog2) with
    | Some progt1, Some progt2 => Some (PTree.Node progt1 None progt2)
    | _, _ => None
    end
  | PTree.Node prog1 (Some func) prog2 =>
    match transform_func func with
    | Some func_t =>
      match (transform_prog prog1), (transform_prog prog2) with
      | Some progt1, Some progt2 => Some (PTree.Node progt1 (Some func_t) progt2)
      | _, _ => None
      end
    | None => None
    end
  end.

Lemma transform_prog_proper:
  forall prog_s prog_t fid func_s
    (TRANS_FORM: transform_prog prog_s = Some prog_t)
    (FUNC: prog_s ! fid = Some func_s),
  exists func_t, prog_t ! fid = Some func_t /\ transform_func func_s = Some func_t.
Proof.
  induction prog_s; ss; ii.
  - rewrite PTree.gleaf in FUNC. tryfalse.
  - destruct fid; ss.
    + destruct o; ss.
      destruct (transform_func f) eqn:TRANS_FUNC; ss.
      destruct (transform_prog prog_s1) eqn:TRANS_PROG1; ss.
      destruct (transform_prog prog_s2) eqn:TRANS_PROG2; ss.
      inv TRANS_FORM.
      eapply IHprog_s2 in FUNC; eauto.
      destruct (transform_prog prog_s1) eqn:TRANS_PROG1; ss.
      destruct (transform_prog prog_s2) eqn:TRANS_PROG2; ss.
      inv TRANS_FORM.
      eapply IHprog_s2 in FUNC; eauto.
    + destruct o; ss.
      destruct (transform_func f) eqn:TRANS_FUNC; ss.
      destruct (transform_prog prog_s1) eqn:TRANS_PROG1; ss.
      destruct (transform_prog prog_s2) eqn:TRANS_PROG2; ss.
      inv TRANS_FORM.
      eapply IHprog_s1 in FUNC; eauto.
      destruct (transform_prog prog_s1) eqn:TRANS_PROG1; ss.
      destruct (transform_prog prog_s2) eqn:TRANS_PROG2; ss.
      inv TRANS_FORM.
      eapply IHprog_s1 in FUNC; eauto.
    + subst; ss.
      destruct (transform_func func_s) eqn:TRANS_FUNC; ss.
      destruct (transform_prog prog_s1) eqn:TRANS_PROG1; ss.
      destruct (transform_prog prog_s2) eqn:TRANS_PROG2; ss.
      inv TRANS_FORM.
      exists f. split; eauto.
Qed.

Lemma transform_prog_proper_none:
  forall prog_s prog_t fid
    (TRANS_FORM: transform_prog prog_s = Some prog_t)
    (FUNC: prog_s ! fid = None),
    prog_t ! fid = None.
Proof.
  induction prog_s; ss; ii.
  - inv TRANS_FORM. rewrite PTree.gleaf; eauto.
  - destruct fid; ss.
    + destruct o; ss.
      destruct (transform_func f) eqn:TRANS_FUNC; ss.
      destruct (transform_prog prog_s1) eqn:TRANS_PROG1; ss.
      destruct (transform_prog prog_s2) eqn:TRANS_PROG2; ss.
      inv TRANS_FORM; eauto.
      destruct (transform_prog prog_s1) eqn:TRANS_PROG1; ss.
      destruct (transform_prog prog_s2) eqn:TRANS_PROG2; ss.
      inv TRANS_FORM; eauto.
    + destruct o; ss.
      destruct (transform_func f) eqn:TRANS_FUNC; ss.
      destruct (transform_prog prog_s1) eqn:TRANS_PROG1; ss.
      destruct (transform_prog prog_s2) eqn:TRANS_PROG2; ss.
      inv TRANS_FORM; eauto.
      destruct (transform_prog prog_s1) eqn:TRANS_PROG1; ss.
      destruct (transform_prog prog_s2) eqn:TRANS_PROG2; ss.
      inv TRANS_FORM; eauto.
    + destruct o; ss.
      destruct (transform_prog prog_s1) eqn:TRANS_PROG1; ss.
      destruct (transform_prog prog_s2) eqn:TRANS_PROG2; ss.
      inv TRANS_FORM; eauto.
Qed.

Lemma transform_func_init
      c_s f_s c_t f_t B_t
      (TRANS_FUNC: transform_func (c_s, f_s) = Some (c_t, f_t))
      (ENTRY_BB_T: c_t ! f_t = Some B_t):
  exists B_s ab, c_s ! f_s = Some B_s /\
            LvDS.analyze_func_backward (c_s, f_s) succ transf_blk = Some ab /\
            transform_cdhp c_s ab = c_t /\ f_s = f_t.
Proof.
  unfold transform_func in *.
  destruct (LvDS.analyze_func_backward (c_s, f_s) succ transf_blk) eqn:ANALYSIS; tryfalse.
  inv TRANS_FUNC. unfold transform_cdhp in ENTRY_BB_T.
  rewrite PTree.gmap in ENTRY_BB_T.
  unfold option_map in ENTRY_BB_T.
  destruct (c_s ! f_t) eqn:Heqe; tryfalse.
  exists t a. split; eauto.
Qed.

Lemma transf_cdhp_prop
      C_src C_tgt afunc BB_tgt f f_s
      (ANALYSIS_FUNC: LvDS.analyze_func_backward (C_src, f_s) succ transf_blk = Some afunc)
      (TRANS_CDHP: transform_cdhp C_src afunc = C_tgt)
      (BB: C_tgt ! f = Some BB_tgt):
  exists BB_src ai ai_pblk,
    C_src ! f = Some BB_src /\
    transf_blk (LvDS.AI.getLast (afunc !! f)) BB_src = LvDS.AI.Cons ai ai_pblk /\
    transform_blk' ai_pblk BB_src = BB_tgt /\
    (forall s BB_src',
        In s (succ BB_src) -> C_src ! s = Some BB_src' ->  
        LvDS.L.ge (LvDS.AI.getLast (afunc !! f))
                  (LvDS.AI.getFirst (transf_blk (LvDS.AI.getLast (afunc !! s)) BB_src'))).
Proof.
  subst. unfold transform_cdhp in *.
  rewrite PTree.gmap in BB. unfold option_map in *.
  destruct (C_src ! f) eqn: GET_CDHP_src; ss. inv BB.
  renames t to BB_src.
  assert (TRANS_BLK: exists ai ai_pblk, transf_blk (LvDS.AI.getLast (afunc !! f)) BB_src = LvDS.AI.Cons ai ai_pblk).
  {
    eapply transf_blk_cons; eauto.
  }
  des.
  exists BB_src ai ai_pblk. splits; eauto.
  destruct ((snd afunc) ! f) eqn:GET_AB.
  {
    unfold transform_blk. unfold "!!". rewrite GET_AB.
    exploit LvDS.analyze_func_solution_backward_get; eauto.
    ii. eapply wf_transf_blk; eauto.
    introv TRANS_BLK'; subst.
    rewrite TRANS_BLK. eauto.
  }
  {
    exploit LvDS.analyze_func_solution_backward_get_none; eauto.
    ii. eapply wf_transf_blk; eauto. introv GET_NONE.
    rewrite GET_NONE in TRANS_BLK. simpl in TRANS_BLK. rewrite GET_NONE.
    simpl. rewrite TRANS_BLK. eauto.
  }

  ii.
  eapply LvDS.analyze_func_solution_backward'; eauto.
  ii. eapply wf_transf_blk; eauto.
  Unshelve. exact f.
  Unshelve. exact f.
  Unshelve. exact f.
Qed.

(*
(** test case *)
Definition r : Reg.t := 1%positive.
Definition x : Loc.t := 1%positive.
Definition y : Loc.t := 2%positive.
Definition bb : BBlock.t :=
  (Inst.store x (Inst.expr_val Int.one) Ordering.plain)
    ##(Inst.load r y Ordering.acqrel)
    ##(Inst.store x (Inst.expr_val (Int.repr 2)) Ordering.plain)
    ##BBlock.ret.
Definition func : Func := (PTree.set 1 bb (PTree.empty BBlock.t), 1%positive).
Compute (LvDS.analyze_func_backward func succ transf_blk).
Definition code_s : Code := PTree.set 1 func (PTree.empty Func).
 *)

(** ** The Implementation of Dead code elimination *)
Definition dce_optimizer: Optimizer rtl_lang :=
  fun (lo: Ordering.LocOrdMap) (prog_s: Code) => transform_prog prog_s.


