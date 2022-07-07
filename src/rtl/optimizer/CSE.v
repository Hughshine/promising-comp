Require Import RelationClasses.
Require Import List.

Require Import sflib.
From Paco Require Import paco.

Require Import Basic.
Require Import Axioms.
Require Import Loc.
Require Import LibTactics.
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
Require Import AveAnalysis.
Require Import CorrectOpt.
Require Import Lia.

(** * Definition of Common Subexpression Elimination *)

(** assign/load may be optimized if common expression exists *)
Definition transform_inst (inst: Inst.t) (ai: AveLat.t): (Inst.t) :=
    match inst with 
    | Inst.assign reg e => 
        match AveLat.GetRegByExpr e ai with 
        | Some reg' => Inst.assign reg (Inst.expr_reg reg') 
        | None => inst
        end
    | Inst.load reg loc Ordering.plain => 
        match AveLat.GetRegByLoc loc ai with
        | Some reg' => Inst.assign reg (Inst.expr_reg reg') 
        | None => inst
        end 
    | _ => inst
    end.

(** some boring auxiliary inst-level lemmas *)

Lemma skip_transformed_inst_by_skip:
    forall inst l,
    transform_inst inst l = Inst.skip -> inst = Inst.skip.
Proof.
    intros.
    unfolds transform_inst. 
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l); try discriminate; eauto.
    destruct or; 
      destruct (AveLat.GetRegByLoc loc l); try discriminate; eauto.
Qed.

Lemma assign_transformed_inst_by_assign_or_na_load:
    forall inst l e r,
    transform_inst inst l = Inst.assign r e -> 
    (
    (** no opt *)
    (inst = Inst.assign r e)  
    \/ 
    (** load -> assign *)
    (exists loc r', inst = Inst.load r loc Ordering.plain /\ AveLat.GetRegByLoc loc l = Some r' /\ e = (Inst.expr_reg r')) 
    \/ 
    (** assign -> assign *)
    (exists e' r', inst = Inst.assign r e' /\ AveLat.GetRegByExpr e' l = Some r' /\ e = (Inst.expr_reg r'))
    ).
Proof.
    intros.
    unfolds transform_inst.
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l) eqn:GetReg; try discriminate; eauto.
    rename t into r'.
    right. right. inversion H. 
    do 2 eexists; splits; eauto.
    destruct or; try discriminate; eauto. 
    right. left.
    destruct (AveLat.GetRegByLoc loc l) eqn:GetReg; try discriminate; eauto.
    rename t into r'.
    do 2 eexists; splits; eauto. inv H. trivial.
    inv H. trivial.
Qed.

Lemma store_transformed_inst_by_store:
    forall inst l x e o,
    transform_inst inst l = Inst.store x e o -> inst = Inst.store x e o.
Proof.
    intros.
    unfolds transform_inst.
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l); try discriminate; eauto.
    destruct or; 
      destruct (AveLat.GetRegByLoc loc l); try discriminate; eauto.
Qed.

Lemma cas_transformed_inst_by_cas:
    forall inst l x er ew o ow r,
    transform_inst inst l = Inst.cas r x er ew o ow -> inst = Inst.cas r x er ew o ow.
Proof.
    intros.
    unfolds transform_inst.
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l); try discriminate; eauto.
    destruct or; 
      destruct (AveLat.GetRegByLoc loc l); try discriminate; eauto.
Qed.

Lemma load_transformed_inst_by_load:
    forall inst l x r o,
    transform_inst inst l = Inst.load r x o -> inst = Inst.load r x o.
Proof.
    intros.
    unfolds transform_inst.
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l); try discriminate; eauto.
    destruct or; 
      destruct (AveLat.GetRegByLoc loc l); try discriminate; eauto.
Qed.

(** transformation of basic block *)
Fixpoint transform_blk (b: BBlock.t) (ai_blk: AveAI.b): BBlock.t := 
    match b, ai_blk with 
    | i##b', AveAI.Cons ai ai_blk' => 
        let b' := transform_blk b' ai_blk' in ((transform_inst i ai)##b')
    | BBlock.jmp f, AveAI.Atom ai => (BBlock.jmp f)
    | BBlock.call f fret, AveAI.Atom ai => (BBlock.call f fret)
    | BBlock.be e f1 f2, AveAI.Atom ai => (BBlock.be e f1 f2)
    | BBlock.ret, AveAI.Atom ai => (BBlock.ret)
    | _, _ => b 
    end.

Definition transform_blk' (analysis: AveAI.ACdhp) (i: positive) (b: BBlock.t) : BBlock.t := 
    let ai_blk := analysis!!i in transform_blk b ai_blk.

(** transformation of code heap *)
Definition transform_cdhp (cdhp: CodeHeap) (analysis: AveAI.ACdhp): CodeHeap := 
    PTree.map (transform_blk' analysis) cdhp.

(** transformation of function *)
Definition transform_func (analysis: AveAI.AProg) (i: positive) (func: Func) : Func := 
    let (cdhp, fid) := func in 
    match (analysis!i) with 
    | Some result => (transform_cdhp cdhp result, fid)
    | None => func
    end.

(** transformation of whole program
- each function may be optimized and not optimized 
 *)
Definition transform_prog (prog: Code) (analysis: AveAI.AProg): Code := 
    PTree.map (transform_func analysis) prog.

(** Definition of CSE optimizer  *)
Program Definition cse_optimizer: Optimizer rtl_lang :=
    fun lo prog => 
        Some (
            transform_prog prog 
            (AveDS.analyze_program prog succ AveLat.top Ave_B.transf_blk)).

(** Some boring blk-level auxiliary lemmas *)

Theorem ret_transformed_by_ret: 
    forall b ai, 
        transform_blk b ai = BBlock.ret
        -> b = BBlock.ret.
Proof.
    intros. unfold transform_blk in H.
    induction b; destruct ai; try discriminate; eauto.
Qed.

Theorem jmp_transformed_by_jmp: 
    forall b ai f, 
        transform_blk b ai = BBlock.jmp f
        -> b = BBlock.jmp f.
Proof.
    intros. unfold transform_blk in H.
    induction b; destruct ai; try discriminate; eauto.
Qed.

Theorem be_transformed_by_be: 
    forall b ai e f1 f2, 
        transform_blk b ai = BBlock.be e f1 f2
        -> b = BBlock.be e f1 f2.
Proof.
    intros. unfold transform_blk in H.
    induction b; destruct ai; try discriminate; eauto.
Qed.

Theorem call_transformed_by_call: 
    forall b ai f fret, 
        transform_blk b ai = BBlock.call f fret
        -> b = BBlock.call f fret.
Proof.
    intros. unfold transform_blk in H.
    induction b; destruct ai; try discriminate; eauto.
Qed.

Theorem store_transformed_by_store: 
    forall b ai x e o b' , 
        transform_blk b ai = Inst.store x e o ## b'
        -> 
    exists b'',
        b = Inst.store x e o ## b''.
Proof.
    intros. unfold transform_blk in H. 
    destruct b; destruct ai; try discriminate; eauto.
    inversion H. exists b.
    rewrite H1. 
    eapply store_transformed_inst_by_store in H1. rewrite H1. trivial.
Qed.

Theorem cas_transformed_by_cas: 
    forall b ai r x er ew o ow b' , 
        transform_blk b ai = Inst.cas r x er ew o ow ## b'
        -> 
    exists b'',
        b = Inst.cas r x er ew o ow ## b''.
Proof.
    intros. unfold transform_blk in H. 
    destruct b; destruct ai; try discriminate; eauto.
    inversion H. exists b.
    rewrite H1. 
    eapply cas_transformed_inst_by_cas in H1. rewrite H1. trivial.
Qed.

Theorem load_transformed_by_load: 
    forall b ai r x o b' , 
        transform_blk b ai = Inst.load r x o ## b'
        -> 
    exists b'',
        b = Inst.load r x o ## b''.
Proof.
    intros. unfold transform_blk in H. 
    destruct b; destruct ai; try discriminate; eauto.
    inversion H. exists b.
    rewrite H1. 
    eapply load_transformed_inst_by_load in H1. rewrite H1. trivial.
Qed.

Theorem skip_transformed_by_skip: 
    forall b b' ai, 
        transform_blk b ai = Inst.skip ## b'
        -> (
        exists b_tail,
            b = Inst.skip ## b_tail /\ transform_blk b_tail (AveAI.getTail ai) = b'
        ).
Proof.
    intros.
     (* eexists.  *)
    unfold transform_blk in H.
    destruct b; destruct ai; try discriminate; eauto.
    - exists b'. splits; trivial.
      unfold transform_blk. unfold AveAI.getTail.
      destruct b'; try discriminate; eauto.
    - fold transform_blk in H. 
      exists b.
      splits.
      * inversion H.
        rewrite H1. 
        eapply skip_transformed_inst_by_skip in H1. 
        rewrite H1.
        trivial.
      *      
        inversion H.
        unfolds AveAI.getTail. trivial.
Qed.

Lemma at_load_transformed_inst_by_at_load:
    forall inst l r loc ord,
    transform_inst inst l = Inst.load r loc ord 
    -> ord <> Ordering.plain
    -> inst = Inst.load r loc ord.
Proof.
    intros.
    unfolds transform_inst. 
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l) eqn:Eq; try discriminate; eauto.
    destruct or eqn:EqOr;
    destruct (AveLat.GetRegByLoc loc l); try discriminate;  eauto.
    destruct (AveLat.GetRegByLoc loc0 l); try discriminate;  eauto.
    destruct (AveLat.GetRegByLoc loc0 l); try discriminate;  eauto.
Qed.

Lemma write_transformed_inst_by_write:
    forall inst l r loc ord,
    transform_inst inst l = Inst.load r loc ord 
    -> inst = Inst.load r loc ord.
Proof.
    intros.
    unfolds transform_inst. 
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l) eqn:Eq; try discriminate; eauto.
    destruct or eqn:EqOr;
    destruct (AveLat.GetRegByLoc loc l); try discriminate;  eauto.
    destruct (AveLat.GetRegByLoc loc0 l); try discriminate;  eauto.
    destruct (AveLat.GetRegByLoc loc0 l); try discriminate;  eauto.
Qed.

Lemma fence_rel_transformed_inst_by_fence_rel:
    forall inst l,
    transform_inst inst l = Inst.fence_rel
    -> inst = Inst.fence_rel.
Proof.
    intros.
    unfolds transform_inst. 
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l) eqn:Eq; try discriminate; eauto.
    destruct or eqn:EqOr;
    destruct (AveLat.GetRegByLoc loc l); try discriminate;  eauto.
Qed.

Lemma fence_acq_transformed_inst_by_fence_acq:
    forall inst l,
    transform_inst inst l = Inst.fence_acq
    -> inst = Inst.fence_acq.
Proof.
    intros.
    unfolds transform_inst. 
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l) eqn:Eq; try discriminate; eauto.
    destruct or eqn:EqOr;
    destruct (AveLat.GetRegByLoc loc l); try discriminate;  eauto.
Qed.


Lemma fence_sc_transformed_inst_by_fence_sc:
    forall inst l,
    transform_inst inst l = Inst.fence_sc
    -> inst = Inst.fence_sc.
Proof.
    intros.
    unfolds transform_inst. 
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l) eqn:Eq; try discriminate; eauto.
    destruct or eqn:EqOr;
    destruct (AveLat.GetRegByLoc loc l); try discriminate;  eauto.
Qed.

Lemma out_transformed_inst_by_out:
    forall inst l e,
    transform_inst inst l = Inst.print e
    -> inst = Inst.print e.
Proof.
    intros.
    unfolds transform_inst. 
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l) eqn:Eq; try discriminate; eauto.
    destruct or eqn:EqOr;
    destruct (AveLat.GetRegByLoc loc l); try discriminate;  eauto.
Qed.

Lemma at_store_transformed_inst_by_at_store:
    forall inst l loc ord e,
    transform_inst inst l = Inst.store loc e ord 
    -> ord <> Ordering.plain
    -> inst = Inst.store loc e ord.
Proof.
    intros.
    unfolds transform_inst. 
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l) eqn:Eq; try discriminate; eauto.
    destruct or eqn:EqOr;
    destruct (AveLat.GetRegByLoc loc l); try discriminate;  eauto.
    destruct (AveLat.GetRegByLoc loc0 l); try discriminate;  eauto.
    destruct (AveLat.GetRegByLoc loc0 l); try discriminate;  eauto.
Qed.

Lemma at_cas_transformed_inst_by_at_cas:
    forall inst l r loc ord er ew ow,
    transform_inst inst l = Inst.cas r loc er ew ord ow
    -> ord <> Ordering.plain
    -> inst = Inst.cas r loc er ew ord ow.
Proof.
    intros.
    unfolds transform_inst. 
    destruct inst; try discriminate; eauto.
    destruct (AveLat.GetRegByExpr rhs l) eqn:Eq; try discriminate; eauto.
    destruct or eqn:EqOr;
    destruct (AveLat.GetRegByLoc loc l); try discriminate;  eauto.
    destruct (AveLat.GetRegByLoc loc0 l); try discriminate;  eauto.
    destruct (AveLat.GetRegByLoc loc0 l); try discriminate;  eauto.
Qed.

Theorem at_load_transformed_by_at_load: 
    forall b b' ai loc r ord, 
        transform_blk b ai = Inst.load r loc ord ## b'
        -> 
        ord <> Ordering.plain
        -> (
        exists b_tail,
            b = Inst.load r loc ord ## b_tail /\ transform_blk b_tail (AveAI.getTail ai) = b'
        ).
Proof.
    intros.
    unfold transform_blk in H.
    destruct b; destruct ai; try discriminate; eauto.
    - exists b'. splits; trivial.
      unfold transform_blk. unfold AveAI.getTail.
      destruct b'; try discriminate; eauto.
    - fold transform_blk in H. 
      exists b.
      splits.
      * inversion H.
        rewrite H2. 
        eapply at_load_transformed_inst_by_at_load in H2; eauto.
        rewrite H2.
        trivial.
      *      
        inversion H.
        unfolds AveAI.getTail. trivial.
Qed.

Theorem fence_rel_transformed_by_fence_rel: 
    forall b b' ai, 
        transform_blk b ai = Inst.fence_rel ## b'
        -> (
        exists b_tail,
            b = Inst.fence_rel ## b_tail /\ transform_blk b_tail (AveAI.getTail ai) = b'
        ).
Proof.
    intros.
    unfold transform_blk in H.
    destruct b; destruct ai; try discriminate; eauto.
    - exists b'. splits; trivial.
      unfold transform_blk. unfold AveAI.getTail.
      destruct b'; try discriminate; eauto.
    - fold transform_blk in H. 
      exists b.
      splits.
      * inversion H.
        rewrite H1. 
        eapply fence_rel_transformed_inst_by_fence_rel in H1; eauto.
        rewrite H1.
        trivial.
      *      
        inversion H.
        unfolds AveAI.getTail. trivial.
Qed.

Theorem fence_acq_transformed_by_fence_acq: 
    forall b b' ai, 
        transform_blk b ai = Inst.fence_acq ## b'
        -> (
        exists b_tail,
            b = Inst.fence_acq ## b_tail /\ transform_blk b_tail (AveAI.getTail ai) = b'
        ).
Proof.
    intros.
    unfold transform_blk in H.
    destruct b; destruct ai; try discriminate; eauto.
    - exists b'. splits; trivial.
      unfold transform_blk. unfold AveAI.getTail.
      destruct b'; try discriminate; eauto.
    - fold transform_blk in H. 
      exists b.
      splits.
      * inversion H.
        rewrite H1. 
        eapply fence_acq_transformed_inst_by_fence_acq in H1; eauto.
        rewrite H1.
        trivial.
      *      
        inversion H.
        unfolds AveAI.getTail. trivial.
Qed.

Theorem fence_sc_transformed_by_fence_sc: 
    forall b b' ai, 
        transform_blk b ai = Inst.fence_sc ## b'
        -> (
        exists b_tail,
            b = Inst.fence_sc ## b_tail /\ transform_blk b_tail (AveAI.getTail ai) = b'
        ).
Proof.
    intros.
    unfold transform_blk in H.
    destruct b; destruct ai; try discriminate; eauto.
    - exists b'. splits; trivial.
      unfold transform_blk. unfold AveAI.getTail.
      destruct b'; try discriminate; eauto.
    - fold transform_blk in H. 
      exists b.
      splits.
      * inversion H.
        rewrite H1. 
        eapply fence_sc_transformed_inst_by_fence_sc in H1; eauto.
        rewrite H1.
        trivial.
      *      
        inversion H.
        unfolds AveAI.getTail. trivial.
Qed.

Theorem transform_blk_bot_is_id:
    forall b, 
        transform_blk b AveAI.bots = b.
Proof.
    intros.
    unfold transform_blk; unfold AveAI.bots.
    destruct b; trivial.
Qed. 

Theorem transform_blk_top_is_id:
    forall b, 
        transform_blk b (AveAI.Atom AveLat.top) = b.
Proof.
    intros.
    unfold transform_blk.
    destruct b; trivial.
Qed. 

Theorem transform_inst_bot_is_id:
    forall i, 
        transform_inst i AveLat.bot = i.
Proof.
    intros.
    unfold transform_inst; unfold AveAI.bots.
    destruct i; trivial.
    destruct or; trivial. 
Qed. 

Theorem transform_inst_top_is_id:
    forall i, 
        transform_inst i (AveLat.top) = i.
Proof.
    intros.
    unfold transform_inst.
    destruct i; trivial.
    destruct or; trivial.
Qed. 

Lemma br_from_atom_is_eval:
    forall eval i,
    AveAI.br_from_i (AveAI.Atom eval) i =  (AveAI.Atom eval).
Proof.
    intros.
    destruct i.
    unfold AveAI.br_from_i; unfold AveAI.br_from_i_opt; trivial.
    unfold AveAI.br_from_i; unfold AveAI.br_from_i_opt. unfold AveAI.getLast. trivial.
Qed.

(** enpower inductive reasoning *)

Theorem transform_blk_induction:
    forall cdhp_src succ enode analysis blk blk_src b_src' ai b_tgt inst i l,
    AveDS.fixpoint_blk cdhp_src succ enode AveLat.top
             (fun (n : positive) (ai : AveAI.t) =>
              match cdhp_src ! n with
              | Some b => Ave_B.transf_blk ai b
              | None => AveAI.Atom ai
              end) = Some analysis \/ analysis = PMap.init (AveDS.AI.Atom AveLat.top)
    ->
    cdhp_src ! l = Some blk 
    ->
    blk [i:] = Some blk_src
    ->
    blk_src = inst ## b_src'
    ->
    AveAI.br_from_i analysis !! l i = ai
    ->
        transform_blk (inst ## b_src') ai = b_tgt 
        -> 
    exists inst' b_tgt',
        ((b_tgt = inst' ## b_tgt')
        /\ 
            ((transform_inst inst (AveAI.getFirst ai) = inst' /\ transform_blk (b_src') (AveAI.getTail ai) = b_tgt') 
            )
        ).
        Proof.
            intros.
            pose proof H4 as TRSFORM.
            destruct H.
            2: {
                exists inst b_src'.
                rewrite H in H3.
                rewrite PMap.gi in H3.
                rewrite AveAI.br_from_i_eval in H3.
                rewrite <- H3 in H4.
                rewrite transform_blk_top_is_id in H4.
                splits; eauto.
                unfold AveAI.getFirst. rewrite <- H3. eapply transform_inst_top_is_id.
                unfold AveAI.getTail. rewrite <- H3. 
                eapply transform_blk_top_is_id.
            }
            eapply Ave_B.wf_transf_blk_ablk in H; eauto.
            destruct H.
            2: {
                assert (ai = AveAI.bots). {
                    rewrite H in H3.
                    unfolds AveAI.bots.
                    rewrite br_from_atom_is_eval in H3. rewrite H3. trivial.
                }
                do 2 eexists; splits; eauto.
                rewrite H5. unfolds AveAI.bots.
                unfold AveAI.getFirst.
                unfold AveAI.getTail.
                rewrite transform_blk_bot_is_id. 
                rewrite transform_inst_bot_is_id.
                rewrite H5 in H4.
                rewrite transform_blk_bot_is_id in H4.
                rewrite H4.
                trivial. 
            }
            destruct H as (ai_entry & TRSF_BLK).
            eapply Ave_B.wf_transf_blk_ablk_len in TRSF_BLK.
            destruct TRSF_BLK.
            {
                assert (ai = AveAI.bots). {
                    rewrite H in H3.
                    unfolds AveAI.bots.
                    rewrite br_from_atom_is_eval in H3. rewrite H3. trivial.
                }
                do 2 eexists; splits; eauto.
                rewrite H5. unfolds AveAI.bots.
                unfold AveAI.getFirst.
                unfold AveAI.getTail.
                rewrite transform_blk_bot_is_id. 
                rewrite transform_inst_bot_is_id.
                rewrite H5 in H4.
                rewrite transform_blk_bot_is_id in H4.
                rewrite H4.
                trivial. 
            }
            { 
                destruct H.
                destruct ai eqn:EqAi.
                {
                    assert (i<BBlock.len blk). {
                        eapply BBlock.len_lt; eauto.
                    }
                    assert (AveAI.len (analysis !! l) > i + 1). {
                        lia.
                    }
                    eapply AveAI.br_from_i_not_atom in H7; eauto.
                    rewrite H3 in H7. contradiction.
                }
                unfold transform_blk in H4.
                exists (transform_inst inst l0) (transform_blk b_src' (AveAI.getTail ai)). splits; eauto.
                folds transform_blk. 
                rewrite EqAi. unfold AveAI.getTail.
                rewrite H4. trivial.
                rewrite EqAi. trivial.
            }
        Qed.

Theorem transform_blk_induction':
forall cdhp_src succ enode analysis blk blk_src ai b_tgt' i inst' l,
    AveDS.fixpoint_blk cdhp_src succ enode AveLat.top
             (fun (n : positive) (ai : AveAI.t) =>
              match cdhp_src ! n with
              | Some b => Ave_B.transf_blk ai b
              | None => AveAI.Atom ai
              end) = Some analysis \/ analysis = PMap.init (AveDS.AI.Atom AveLat.top)
    ->
    cdhp_src ! l = Some blk 
    ->
    blk [i:] = Some blk_src
    ->
    AveAI.br_from_i analysis !! l i = ai
    ->
        transform_blk blk_src ai = (inst' ## b_tgt') 
        -> 
    exists inst b_src',
        (blk_src = inst ## b_src' 
        /\ (transform_inst inst (AveAI.getFirst ai) = inst' /\ transform_blk (b_src') (AveAI.getTail ai) = b_tgt') 
        ).
Proof.
    intros.
            destruct H.
            2: {
                exists inst' b_tgt'.
                rewrite H in H2.
                rewrite PMap.gi in H2.
                rewrite AveAI.br_from_i_eval in H2.
                rewrite <- H2 in H3.
                rewrite transform_blk_top_is_id in H3.
                splits; eauto.
                unfold AveAI.getFirst. rewrite <- H2. eapply transform_inst_top_is_id.
                unfold AveAI.getTail. rewrite <- H2. 
                eapply transform_blk_top_is_id.
            }
            eapply Ave_B.wf_transf_blk_ablk in H; eauto.
            destruct H.
            2: {
                assert (ai = AveAI.bots). {
                    rewrite H in H2.
                    unfolds AveAI.bots.
                    rewrite br_from_atom_is_eval in H2. rewrite H2. trivial.
                }
                exists inst' b_tgt'.
                rewrite H4 in H3. rewrite transform_blk_bot_is_id in H3.
                splits; eauto.
                rewrite H4.
                unfolds AveAI.bots.
                unfold AveAI.getFirst.
                rewrite transform_inst_bot_is_id. trivial. 
                unfold AveAI.getTail. rewrite H4. unfolds AveAI.bots.
                rewrite transform_blk_bot_is_id. trivial.
            }
            destruct H as (ai_entry & TRSF_BLK).
            eapply Ave_B.wf_transf_blk_ablk_len in TRSF_BLK.
            destruct TRSF_BLK.
            {
                assert (ai = AveAI.bots). {
                    rewrite H in H2.
                    unfolds AveAI.bots.
                    rewrite br_from_atom_is_eval in H2. rewrite H2. trivial.
                }
                exists inst' b_tgt'.
                rewrite H4 in H3. rewrite transform_blk_bot_is_id in H3.
                splits; eauto.
                rewrite H4.
                unfolds AveAI.bots.
                unfold AveAI.getFirst.
                rewrite transform_inst_bot_is_id. trivial. 
                unfold AveAI.getTail. rewrite H4. unfolds AveAI.bots.
                rewrite transform_blk_bot_is_id. trivial.
            }
            { 
                destruct H.
                destruct ai eqn:EqAi.
                {
                    assert (i<BBlock.len blk). {
                        eapply BBlock.len_lt; eauto.
                    }
                    assert (AveAI.len (analysis !! l) > i + 1). {
                        lia.
                    }
                    eapply AveAI.br_from_i_not_atom in H6; eauto.
                    rewrite H2 in H6. contradiction.
                }
                unfold transform_blk in H3.
                destruct blk_src eqn:EqBlkSrc; try discriminate; eauto.
                inv H3.
                do 2 eexists; splits; eauto.
            }
Qed.
    
Theorem get_last_ablk:
forall cdhp_src succ enode analysis blk blk_src ai i l,
    AveDS.fixpoint_blk cdhp_src succ enode AveLat.top
             (fun (n : positive) (ai : AveAI.t) =>
              match cdhp_src ! n with
              | Some b => Ave_B.transf_blk ai b
              | None => AveAI.Atom ai
              end) = Some analysis
    ->
    cdhp_src ! l = Some blk 
    ->
    blk [i:] = Some blk_src
    ->
    (forall inst blk_src', blk_src <> inst ## blk_src')
    ->
    AveAI.br_from_i analysis !! l i = ai
    -> 
    (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)) = AveAI.getLast (AveAI.br_from_i analysis !! l i)).
Proof.
    intros.
    eapply Ave_B.wf_transf_blk_ablk in H; eauto.
    destruct H.
    {
      destruct H as (ai_entry & TRSF_BLK).
      eapply Ave_B.wf_transf_blk_ablk_len in TRSF_BLK.
      destruct TRSF_BLK.
      {
        rewrite H.
        rewrite AveAI.get_first_from_ablk_bots.
        rewrite AveAI.get_last_from_ablk_bots.
        trivial.
      }
      {
        destruct H.
        assert (i+1=BBlock.len blk). {          
          eapply BBlock.len_eq; eauto.
        }
        rewrite <- H5 in H4.
        rewrite AveAI.get_i_plus_1_eq_get_last; eauto; try lia.
        rewrite AveAI.get_last_from_i_eq_from_zero; try lia; trivial.
      }
    }
    {
      rewrite H.
      rewrite AveAI.get_first_from_ablk_bots.
      rewrite AveAI.get_last_from_ablk_bots.
      trivial.
    }
Qed.
