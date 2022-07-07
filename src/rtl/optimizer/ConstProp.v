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
Require Import ValAnalysis.
Require Import CorrectOpt.
Set Implicit Arguments.

(** * Constant Propagation *)

(** Constant propagation first uses value analysis to analyze program and
    then translates program according to the result of analysis. *)

(** ** Transformation for the Single Instruction *)
Definition transform_inst (inst: Inst.t) (ae: ValLat.t) : Inst.t :=
  match inst with
  | Inst.assign r e =>
    match (eval_expr_ae e (fst ae)) with
    | LVal.VAL v => Inst.assign r (Inst.expr_val v)
    | _ => Inst.assign r e
    end
  | Inst.load r loc or =>
    match or with
    | Ordering.plain =>
      match (VALSET.get loc (snd ae)) with
      | LVal.VAL v => Inst.assign r (Inst.expr_val v)
      | _ => Inst.load r loc or
      end
    | _ => Inst.load r loc or
    end
  | _ => inst
  end.

Lemma eval_expr_ae_bot_to_val_false:
  forall expr n,
    eval_expr_ae expr VALSET.bot = LVal.VAL n -> False.
Proof.
  induction expr; ss; eauto.
Qed.

Lemma transform_inst_bot
      inst:
  transform_inst inst ValDS.AI.bot = inst.
Proof.
  destruct inst; eauto.
  ss. destruct (eval_expr_ae rhs VALSET.bot) eqn:Heqe; ss; eauto.
  eapply eval_expr_ae_bot_to_val_false in Heqe; eauto. ss.
  ss. destruct or; ss; eauto.
Qed.

(** ** Transformation for the basic block *)
Fixpoint transform_blk (ae_blk: ValDS.AI.b) (b_s: BBlock.t) {struct b_s}: BBlock.t :=
  match b_s, ae_blk with
  | i##b_s', ValDS.AI.Cons ae ae_blk' =>
    (transform_inst i ae)##(transform_blk ae_blk' b_s')
  | _, _ => b_s
  end.

Lemma transform_blk_bot':
  forall BB,
    transform_blk ValDS.AI.bots BB = BB.
Proof.
  destruct BB; ss; eauto.
Qed.

Lemma transform_blk_bot:
  forall BB,
    transform_blk (transf_blk ValDS.AI.bot BB) BB = transform_blk ValDS.AI.bots BB.
Proof.
  induction BB; try solve [ss; eauto].
  assert (transf_blk ValDS.AI.bot (c ## BB) =
          ValDS.AI.Cons ValDS.AI.bot (transf_blk (transf_instr c ValDS.AI.bot) BB)). eauto.
  assert (transf_instr c ValDS.AI.bot = ValDS.AI.bot).
  eapply transf_instr_bot; eauto.
  rewrite H0 in H; clear H0.
  rewrite H. clear H.
  simpl. rewrite IHBB.
  rewrite transform_inst_bot.
  rewrite transform_blk_bot'. eauto.
Qed.

(** ** Transformation for the code heap *)
Definition transform_cdhp (cdhp: CodeHeap) (analysis: ValDS.AI.ACdhp): CodeHeap := 
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

(** ** Code transformation for a function *)
Definition transform_func (func: Func): option Func :=
  match ValDS.analyze_func func succ ValLat.top transf_blk with
  | Some analysis =>
    let (cdhp, fid) := func in Some (transform_cdhp cdhp analysis, fid)
  (* transformation error, since there is no analysis result *)
  | None => None
  end.

(** ** Code transformation for a program *)
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
            ValDS.analyze_func (c_s, f_s) succ ValLat.top transf_blk = Some ab /\
            transform_cdhp c_s ab = c_t /\ f_s = f_t.
Proof.
  unfold transform_func in *.
  destruct (ValDS.analyze_func (c_s, f_s) succ ValLat.top transf_blk) eqn:ANALYSIS; tryfalse.
  inv TRANS_FUNC. unfold transform_cdhp in ENTRY_BB_T.
  rewrite PTree.gmap in ENTRY_BB_T.
  unfold option_map in ENTRY_BB_T.
  destruct (c_s ! f_t) eqn:Heqe; tryfalse.
  exists t a. split; eauto.
Qed.

Lemma transf_cdhp_prop
      C_src C_tgt afunc BB_tgt f f_s ep
      (ANALYSIS_FUNC: ValDS.analyze_func (C_src, f_s) succ ep transf_blk = Some afunc)
      (TRANS_CDHP: transform_cdhp C_src afunc = C_tgt)
      (BB: C_tgt ! f = Some BB_tgt):
  exists BB_src ae_pblk,
    C_src ! f = Some BB_src /\
    transf_blk (ValDS.AI.getFirst (afunc !! f)) BB_src = ae_pblk /\
    transform_blk ae_pblk BB_src = BB_tgt /\
    (forall s BB_src',
        In s (succ BB_src) -> C_src ! s = Some BB_src' ->  
        ValDS.L.ge (ValDS.AI.getFirst (afunc !! s)) (ValDS.AI.getLast ae_pblk)).
Proof.
  unfold transform_cdhp in TRANS_CDHP.
  subst. rewrite PTree.gmap in BB.
  unfold option_map in BB. destruct (C_src ! f) eqn:BB_SRC; ss.
  inv BB. renames t to BB_src.
  do 2 eexists. splits; eauto.
  - exploit ValDS.analyze_func_solution_get; [ | | eapply ANALYSIS_FUNC | eauto..].
    eapply transf_blk_first; eauto.
    eapply transf_blk_bot; eauto.
    i. des1. rewrite H. eauto.
    rewrite H; ss.
    rewrite transform_blk_bot. eauto.
  - ii.
    eapply ValDS.analyze_func_solution1 in ANALYSIS_FUNC; eauto.
    ii. eapply transf_blk_first; eauto.
    ii. eapply transf_blk_bot; eauto.
Qed.

(** ** The Implementation of Constant propagation *)
Definition constprop_optimizer: Optimizer rtl_lang :=
  fun (lo: Ordering.LocOrdMap) (prog_s: Code) => transform_prog prog_s.
