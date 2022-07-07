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

(** * Available Expression Analysis **)

(** Definition of Available Expression Pair *)
(** Interpretation of [AveTuple]: 
- [AExpr r e]: common subexpression
- [AVar r loc]: common memory read
*)
Module AveTuple.
    Inductive Tuple := 
    | AExpr (reg: Reg.t) (expr: Inst.expr) (** Common subexpression *)
    | AVar (reg: Reg.t) (loc: Loc.t)  (** Common memory access *)
    .
    Definition t := Tuple.
    Definition eq (x y: t): Prop := x = y.
    Definition eq_refl: forall x, eq x x := @eq_refl t.
    Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
    Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
    Definition eq_dec: forall x y : t, {x = y} + {x <> y}.
        decide equality; try (eapply Loc.eq_dec). 
        eapply Inst.expr_eq_dec.
    Defined.

    Definition isExpr (tu: t): bool := 
        match tu with 
        | AExpr _ _ => true
        | AVar _ _ => false
        end.

    Definition isSameLoc (loc: Loc.t) (tu: t): bool :=
        match tu with
        | AVar reg loc' => Loc.eqb loc loc'
        | _ => false
        end.

    Definition isNotSameLoc (loc: Loc.t) (tu: t): bool :=
        match tu with
        | AVar reg loc' => negb (Loc.eqb loc loc') 
        | _ => true
        end.
    
    Definition freeOfReg (reg': Loc.t) (tu: t): bool :=
      match tu with
      | AVar reg _ => negb (Reg.eqb reg reg')
      | AExpr reg expr  => andb (negb (Reg.eqb reg reg')) (negb (RegSet.mem reg' (Inst.regs_of_expr expr)))
      end.

    Definition isSameExpr (expr: Inst.expr) (tu: t): bool :=
        match tu with 
        | AExpr reg expr' => Inst.beq_expr expr expr'
        | _ => false
        end.

    Definition get_reg (tu: t): Reg.t := 
        match tu with 
        | AExpr r _ => r
        | AVar r _ => r 
        end.


    Lemma compat_bool_isExpr:
        compat_bool (fun x y : AveTuple.t => x = y) (isExpr). 
    Proof.
        intros.
        pose proof @proper_eq AveTuple.t.
        unfolds compat_bool. simpls.
        unfolds Proper. simpls.
        unfold "==>".
        intros.
        rewrite H0.  
        trivial.      
    Qed.

    Lemma compat_bool_freeOfReg:
        forall r,
        compat_bool (fun x y : AveTuple.t => x = y) (AveTuple.freeOfReg r). 
    Proof.
        intros.
        pose proof @proper_eq AveTuple.t.
        unfolds compat_bool. simpls.
        unfolds Proper. simpls.
        unfold "==>".
        intros.
        rewrite H0.  
        trivial.      
    Qed.

    Lemma compat_bool_isSameExpr:
    forall r,
    compat_bool (fun x y : AveTuple.t => x = y) (AveTuple.isSameExpr r). 
    Proof.
        intros.
        pose proof @proper_eq AveTuple.t.
        unfolds compat_bool. simpls.
        unfolds Proper. simpls.
        unfold "==>".
        intros.
        rewrite H0.  
        trivial.      
    Qed.

    Lemma compat_bool_isSameLoc:
    forall r,
    compat_bool (fun x y : AveTuple.t => x = y) (AveTuple.isSameLoc r). 
    Proof.
        intros.
        pose proof @proper_eq AveTuple.t.
        unfolds compat_bool. simpls.
        unfolds Proper. simpls.
        unfold "==>".
        intros.
        rewrite H0.  
        trivial.      
    Qed.

    Lemma compat_bool_isNotSameLoc:
    forall r,
    compat_bool (fun x y : AveTuple.t => x = y) (AveTuple.isNotSameLoc r). 
    Proof.
        intros.
        pose proof @proper_eq AveTuple.t.
        unfolds compat_bool. simpls.
        unfolds Proper. simpls.
        unfold "==>".
        intros.
        rewrite H0.  
        trivial.      
    Qed.
End AveTuple.

(** Available expression analysis' abstract interpretation is basically a set of [AveTuple] *)
Module W := FSetWeakList.Make (AveTuple).

(** ** Definition of Available Expreesion Analysis' (Semi-)Lattice *)
(** Interpretation of [AveLat]:
- [Bot]: additional uninformative fact for forward dataflow analysis solver 
- [Undef]: act as `universal set`, which definitely matches no state
- [CSet tuples]: set of available expressions   
- [CSet W.empty] is the top fact of this lattice concluding nothing
*)
Module AveLat <: SEMILATTICE_WITH_TOP.
    Inductive AveSet := 
    | Bot
    | Undef  
    | CSet (tuples: W.t)
    .
    Definition t := AveSet.

    Definition beq (x y:t): bool := 
        match x with 
        | CSet tuples_x => 
            match y with 
            | CSet tuples_y => W.equal tuples_x tuples_y
            | _ => false 
            end
        | Undef => 
            match y with 
            | Undef => true 
            | _ => false
            end
        | Bot => 
            match y with  
            | Bot => true
            | _ => false
            end
        end.

    Definition eq (x y: t) := 
        beq x y = true.
    
    Definition eq_refl: forall x, eq x x. 
    Proof.
        intros. unfolds eq. unfolds beq. destruct x; eauto. 
        eapply W.equal_1. eapply W.eq_refl.  
    Qed.
    
    Definition eq_sym: forall x y, eq x y -> eq y x.
    Proof.
        intros. unfolds eq. unfolds beq. destruct x, y; eauto.  
        eapply W.equal_1. eapply W.equal_2 in H. 
        eapply W.eq_sym in H. eauto.
    Qed.

    Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
    Proof. 
        intros. unfolds eq. unfolds beq. destruct x, y, z; eauto.
        eapply W.equal_1. eapply W.equal_2 in H0. eapply W.equal_2 in H.
        eapply W.eq_trans; eauto.  
    Qed.

    Lemma beq_correct: forall x y, beq x y = true -> eq x y.
    Proof. 
        intros.
        unfolds eq. unfolds beq. 
        destruct x, y; try discriminate; eauto.
    Qed.

    (** [W.Subset]: Lattice's partial relation *)
    Definition ge (x y: t) : Prop := 
        match x with
        | CSet tu_x => 
            match y with 
            | CSet tu_y =>
                W.Subset tu_x tu_y
            | _ => True
            end
        | Undef =>
            match y with   
            | CSet tu_y => False
            | _ => True
            end
        | Bot => 
            match y with 
            | Bot => True
            | _ => False
            end
        end.

    Lemma ge_refl: forall x y, eq x y -> ge x y.
    Proof. 
        intros. 
        unfold ge. unfolds eq. destruct x, y; eauto.
        inv H.  unfolds W.Subset. eapply W.equal_2 in H1. unfolds W.Equal. eapply H1.
    Qed.

    Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
    Proof. unfold ge. destruct x, y, z; eauto. 
    - intros. contradiction.
    - intros. contradiction.
    - apply W.MF.Subset_trans.
    Qed.

    Definition bot := Bot.

    Lemma ge_bot: forall x, ge x bot.
    Proof. destruct x; compute; tauto. Qed.

    Definition top := CSet W.empty.

    Lemma ge_top: forall x, ge top x.
    Proof. unfold ge, top. 
        intros. destruct x. tauto. tauto.
        unfolds W.Subset. 
        intros. inv H.
    Qed.

    (** Lattice's meet operator *)
    Definition lub (x y: t) := 
        match x with 
        | CSet tu_x => 
            match y with 
            | CSet tu_y =>
                CSet (W.inter tu_x tu_y) 
            | _ => CSet tu_x
            end
        | Undef => 
            match y with 
            | CSet tu_y => CSet tu_y
            | _ => Undef
            end
        | Bot => 
            match y with 
            | Bot => Bot
            | _ => y
            end
        end.

    Lemma ge_lub_left: forall x y, ge (lub x y) x.
    Proof. destruct x; destruct y; unfolds lub; try (eapply ge_refl; eapply eq_refl).  
    - unfolds ge. reflexivity.
    - unfolds ge. reflexivity.
    - unfolds ge. reflexivity.
    - unfolds ge. unfolds W.Subset.
      eapply W.inter_1; eauto.
    Qed.

    Lemma ge_lub_right: forall x y, ge (lub x y) y.
    Proof. destruct x; destruct y; unfolds lub; try (eapply ge_refl; eapply eq_refl).  
    - unfolds ge. reflexivity.
    - unfolds ge. reflexivity.
    - unfolds ge. reflexivity.
    - unfolds ge. unfolds W.Subset.
      eapply W.inter_2; eauto.
    Qed.

    (** Choose the register with available expression [e] in lattice [ai] *)
    Definition GetRegByExpr (e: Inst.expr) (ai: AveLat.t): option Reg.t := 
        match ai with 
        | Bot => None
        | Undef => None 
        | CSet tuples => 
            match W.choose (W.filter (AveTuple.isSameExpr e) tuples) with  
            | Some tuple => Some (AveTuple.get_reg tuple)  
            | None => None 
            end
        end.
    (** Choose the register with available memory access [loc] in lattice [ai] *)
    Definition GetRegByLoc (loc: Loc.t) (ai: AveLat.t): option Reg.t := 
        match ai with
        | Bot => None 
        | Undef => None 
        | CSet tuples => 
            match W.choose (W.filter (AveTuple.isSameLoc loc) tuples) with  
            | Some tuple => Some (AveTuple.get_reg tuple)  
            | None => None 
            end
        end.

    (** select the expression subset for [ai] *)
    Definition GetExprs (ai: t): t := 
        match ai with
        | Bot => Bot
        | Undef => Undef 
        | CSet tuples => CSet (W.filter (AveTuple.isExpr) tuples)  
        end.

    Lemma get_exprs_implies_ge:
    forall ai,
        ge (GetExprs ai) ai.
    Proof.
        intros.
        unfold ge. unfold GetExprs.
        destruct ai eqn:EqAi; try discriminate; trivial.
        unfold W.Subset.
        intros.
        eapply W.filter_1 in H; eauto.
        eapply AveTuple.compat_bool_isExpr.
    Qed.
    
    (** optimize an expression [e] with known available expressions [ai] *)
    Fixpoint opt_expr_with_ave (e: Inst.expr) (ai: t): Inst.expr := 
        match GetRegByExpr e ai with 
        | Some reg => Inst.expr_reg reg
        | _ =>
            match e with
            | Inst.expr_op2 Op2.add op1 op2 => 
                Inst.expr_op2 Op2.add (opt_expr_with_ave op1 ai) (opt_expr_with_ave op2 ai)
            | Inst.expr_op2 Op2.sub op1 op2 => 
                Inst.expr_op2 Op2.sub (opt_expr_with_ave op1 ai) (opt_expr_with_ave op2 ai)
            | Inst.expr_op2 Op2.mul op1 op2 =>         
                Inst.expr_op2 Op2.mul (opt_expr_with_ave op1 ai) (opt_expr_with_ave op2 ai)
            | _ => e
            end
        end.

    (** filter out information about register [reg] *)
    Definition kill_reg (ai: t) (reg: Reg.t): t := 
      match ai with 
      | Bot => Bot
      | Undef => Undef 
      | CSet tuples => 
            CSet (W.filter (AveTuple.freeOfReg reg) tuples)
      end.

    (** filter out information about location [loc] *)
    Definition kill_var (ai: t) (loc: Loc.t): t := 
        match ai with 
        | Bot => Bot
        | Undef => Undef 
        | CSet tuples => 
            let ai' := (GetExprs ai) in
            match ai' with   
            | CSet tuples_exprs => 
                CSet (W.union (tuples_exprs) (W.filter (AveTuple.isNotSameLoc loc) tuples))
            | _ =>  
                CSet (W.filter (AveTuple.isNotSameLoc loc) tuples)
            end
        end.
    
    (** Auxiliary Lemmas *)

    Lemma getByLoc_none_implies_kill_none:
    forall loc tuples r,
        None = AveLat.GetRegByLoc loc (AveLat.CSet tuples)
        -> 
        None = AveLat.GetRegByLoc loc (AveLat.kill_reg (AveLat.CSet tuples) r).
    Proof.
        intros. unfolds GetRegByLoc.
        remember ( W.choose (W.filter (AveTuple.isSameLoc loc) tuples)) as Get.
        destruct Get eqn:EqGet; try discriminate.
        eapply Logic.eq_sym in HeqGet.
        eapply W.choose_2 in HeqGet. unfolds W.Empty.
        clear H. 
        remember (kill_reg (CSet tuples) r) as Kill.
        destruct Kill eqn:EqKill; try discriminate.
        remember (W.choose (W.filter (AveTuple.isSameLoc loc) tuples0)) as ChooseKill.
        destruct ChooseKill eqn:EqChooseKill; try discriminate; trivial.
        eapply Logic.eq_sym in HeqChooseKill.
        eapply W.choose_1 in HeqChooseKill.
        pose proof (HeqGet e).

        exfalso.
        apply H.

        unfolds kill_reg.
        inversion HeqKill.
        rewrite H1 in HeqChooseKill.
        assert (W.In e tuples). {
            do 2 eapply W.filter_1 in HeqChooseKill; trivial.
            eapply AveTuple.compat_bool_freeOfReg.
            eapply AveTuple.compat_bool_isSameLoc.
            eapply AveTuple.compat_bool_isSameLoc.
        }
        eapply W.filter_3; eauto.
        eapply AveTuple.compat_bool_isSameLoc.
        eapply W.filter_2 in HeqChooseKill; trivial.
        eapply AveTuple.compat_bool_isSameLoc.
    Qed.

    Lemma getByLoc_implies_valid_tuple:
    forall r' loc tuples tu,
        Some r' = AveLat.GetRegByLoc loc (AveLat.CSet tuples)
        -> 
        tu = (AveTuple.AVar r' loc)
        -> 
        W.In tu tuples.
    Proof.
      intros. 
      unfold GetRegByLoc in H.
      remember ( W.choose (W.filter (AveTuple.isSameLoc loc) tuples)) as opttu.
      destruct opttu eqn:EqOpt; try discriminate; eauto.
      inversion H. unfold AveTuple.get_reg in H2.
      apply Logic.eq_sym in Heqopttu.
      eapply W.choose_1 in Heqopttu.
      pose proof Heqopttu.
      eapply W.filter_2 in Heqopttu.
      eapply W.filter_1 in H1.
      unfold AveTuple.isSameLoc in Heqopttu.
      destruct e eqn:EqE; try discriminate.
      rewrite <- H2 in H1.
      eapply Peqb_true_eq in Heqopttu.
      rewrite <- Heqopttu in H1.
      rewrite <- H0 in H1.
      trivial.
      eapply AveTuple.compat_bool_isSameLoc.
      eapply AveTuple.compat_bool_isSameLoc.
    Qed.
      
    Lemma mem_of_kill_reg_implies_neq:
    forall ai' tuples' tuples r tu,
        ai' = CSet tuples' -> 
        ai' = kill_reg (CSet tuples) r ->
        W.In tu tuples' -> 
        AveTuple.get_reg tu <> r.
    Proof.
        intros.
        unfold AveTuple.get_reg. 
        destruct tu eqn:EqTu.
        - unfolds AveLat.kill_reg. 
        rewrite H in H0.
        inversion H0.
        rewrite H3 in H1.
        eapply W.filter_2 in H1; trivial.
        * 
        unfold AveTuple.freeOfReg in H1.
            intro.
          rewrite H2 in H1.
          eapply sflib__andb_split in H1.
          destruct H1.
          (* Set Printing All. *)
          rewrite Reg.eqb_refl in H1.
          unfold negb in H1. discriminate.
        *   
        eapply (AveTuple.compat_bool_freeOfReg r).
        - 
         unfolds AveLat.kill_reg. 
        rewrite H in H0.
        inversion H0.
        rewrite H3 in H1.
        eapply W.filter_2 in H1; trivial.
        * 
        unfold AveTuple.freeOfReg in H1.
            intro.
          rewrite H2 in H1.
          rewrite Reg.eqb_refl in H1.
          unfold negb in H1. discriminate.
        *   
        eapply (AveTuple.compat_bool_freeOfReg r).
    Qed.

    Lemma mem_of_kill_reg_implies_nonfree_var:
    forall ai' tuples' tuples r r' expr,
        ai' = CSet tuples' -> 
        ai' = kill_reg (CSet tuples) r ->
        W.In (AveTuple.AExpr r' expr) tuples' -> 
        ~RegSet.mem r (Inst.regs_of_expr expr).
    Proof.
        intros.
        unfolds AveLat.kill_reg. 
        rewrite H in H0.
        inversion H0.
        rewrite H3 in H1.
        eapply W.filter_2 in H1; trivial.
        * 
        unfold AveTuple.freeOfReg in H1.
            intro.
          eapply sflib__andb_split in H1.
          destruct H1.
          unfolds negb.
          des_ifH H4; try discriminate; eauto.
        *   
        eapply (AveTuple.compat_bool_freeOfReg r).
    Qed.

    Lemma mem_of_getExprs_implies_non_loc_in_ai:
    forall tu reg loc r tuples tuples',
        tu = AveTuple.AVar reg loc -> 
        W.In tu tuples ->
        AveLat.CSet tuples = AveLat.kill_reg (AveLat.GetExprs (AveLat.CSet tuples')) r
        -> False.
    Proof.
        intros.
        remember (AveLat.GetExprs (AveLat.CSet tuples)) as tu_expr.
        destruct tu_expr eqn:EqTuExpr; try subst; try discriminate.
        unfolds AveLat.GetExprs.
        inv Heqtu_expr.
        remember (W.filter AveTuple.isExpr tuples') as exprs.
        assert (W.In (AveTuple.AVar reg loc) exprs). {
        unfolds kill_reg.
          inversion H1.
          rewrite H2 in H0.
          eapply W.filter_1 in H0; trivial.
          eapply (AveTuple.compat_bool_freeOfReg r).
        }
        rewrite Heqexprs in H.
        eapply W.filter_2 in H.
        unfolds AveTuple.isExpr. discriminate.
        eapply (AveTuple.compat_bool_isExpr).
    Qed.

    Lemma mem_of_getExprs_implies_non_loc_in_ai':
    forall tu reg loc tuples tuples',
        tu = AveTuple.AVar reg loc -> 
        W.In tu tuples ->
        AveLat.CSet tuples = (AveLat.GetExprs (AveLat.CSet tuples'))
        -> False.
    Proof.
        intros.
        remember (AveLat.GetExprs (AveLat.CSet tuples)) as tu_expr.
        destruct tu_expr eqn:EqTuExpr; try subst; try discriminate.
        unfolds AveLat.GetExprs.
        inv Heqtu_expr.
        remember (W.filter AveTuple.isExpr tuples') as exprs.
        inv H1.
        eapply W.filter_2 in H0.
        unfolds AveTuple.isExpr. discriminate.
        eapply (AveTuple.compat_bool_isExpr).
    Qed.
    
End AveLat.

(** Transfer function for instruction *)
Module Ave_I.
  Definition transf (inst: Inst.t) (ai: AveLat.t): AveLat.t := 
        match inst with 
        | Inst.skip => ai
        | Inst.assign reg e => 
            let ai' := AveLat.kill_reg ai reg in 
            let e' := AveLat.opt_expr_with_ave e ai' in (** we record the optimized expression *)
                match AveLat.GetRegByExpr e' ai' with  
                | Some reg' => 
                    match ai' with 
                    | AveLat.Bot => AveLat.Bot
                    | AveLat.Undef => 
                        if (negb (RegSet.mem reg (Inst.regs_of_expr e'))) then 
                        AveLat.CSet (W.add (AveTuple.AExpr reg' (Inst.expr_reg reg)) W.empty) 
                        else                         
                        AveLat.Undef  (** if lhs is free var of rhs, we add nothing because it `kills` itself *)
                    | AveLat.CSet tuples => 
                        if (negb (RegSet.mem reg (Inst.regs_of_expr e'))) then  
                        AveLat.CSet (W.add (AveTuple.AExpr reg' (Inst.expr_reg reg)) tuples) 
                        else 
                        AveLat.CSet tuples
                    end
                | None =>
                    match ai' with 
                    | AveLat.Bot => AveLat.Bot
                    | AveLat.Undef => 
                        if (negb (RegSet.mem reg (Inst.regs_of_expr e'))) then  
                        AveLat.CSet (W.add (AveTuple.AExpr reg e') W.empty) 
                        else AveLat.Undef
                    | AveLat.CSet tuples => 
                        if (negb (RegSet.mem reg (Inst.regs_of_expr e'))) then  
                        AveLat.CSet (W.add (AveTuple.AExpr reg e') tuples) 
                        else AveLat.CSet tuples
                    end            
                end
        | Inst.store loc e ow => 
            match ow with 
            | Ordering.seqcst => 
                match ai with  
                | AveLat.Bot => AveLat.Bot
                | _ => AveLat.top
                end
            | _ => AveLat.kill_var ai loc 
            end
        | Inst.load reg loc or => 
            match or with
            | Ordering.plain => 
                let ai' := AveLat.kill_reg ai reg in 
                match AveLat.GetRegByLoc loc ai' with  
                | Some reg' => 
                    match ai' with 
                    | AveLat.Bot => AveLat.Bot
                    | AveLat.Undef => 
                        AveLat.CSet (W.add (AveTuple.AExpr reg' (Inst.expr_reg reg)) W.empty) 
                    | AveLat.CSet tuples => 
                        AveLat.CSet (W.add (AveTuple.AExpr reg' (Inst.expr_reg reg)) tuples) 
                    end
                | None =>
                    match ai' with 
                    | AveLat.Bot => AveLat.Bot
                    | AveLat.Undef => AveLat.CSet (W.add (AveTuple.AVar reg loc) W.empty) (** only one [(r, x)] is kept for each [x] *)
                    | AveLat.CSet tuples => AveLat.CSet (W.add (AveTuple.AVar reg loc) tuples) 
                    end            
                end
            | Ordering.relaxed => AveLat.kill_reg ai reg
            | Ordering.strong_relaxed => AveLat.kill_reg ai reg
            | Ordering.acqrel => AveLat.kill_reg (AveLat.GetExprs ai) reg
            | _ => 
                match ai with  
                | AveLat.Bot => AveLat.Bot
                | _ => AveLat.top
                end
            end
        | Inst.cas r loc er ew or ow => 
            match ow with 
            | Ordering.seqcst => 
                match ai with  
                | AveLat.Bot => AveLat.Bot
                | _ => AveLat.top
                end
            | _ => 
                match or with 
                | Ordering.relaxed => AveLat.kill_reg (AveLat.kill_var ai loc) r
                | Ordering.strong_relaxed => AveLat.kill_reg (AveLat.kill_var ai loc) r
                | Ordering.acqrel => AveLat.kill_reg (AveLat.GetExprs ai) r  
                | _ => 
                    match ai with  
                    | AveLat.Bot => AveLat.Bot
                    | _ => AveLat.top
                    end
                end
            end
        | Inst.fence_rel => ai
        | Inst.fence_acq => AveLat.GetExprs ai
        | Inst.fence_sc => AveLat.GetExprs ai
        | Inst.print e => AveLat.GetExprs ai
    end.

    (** for analysis solver *)
    Theorem transf_inst_bot_is_bot:
        forall inst, 
        transf inst AveLat.bot = AveLat.bot.
    Proof.
        intros. unfolds transf; simpls.
        destruct inst; eauto. 
        destruct or; eauto.
        destruct ow; eauto.
        destruct ow; destruct or; eauto.
    Qed.
End Ave_I.

Module AveDS := Dataflow_Solver(AveLat)(NodeSetForward).

Module AveAI := AveDS.AI. 

(** ** Transfer Function for the Basic Block *)
Module Ave_B.
    Fixpoint transf_blk' (ai: AveAI.t) (bb: BBlock.t) {struct bb}: AveAI.b := 
        match bb with     
        | BBlock.blk inst bb' => 
            let ai' := Ave_I.transf inst ai in
            AveAI.Cons ai' (transf_blk' ai' bb')
        | BBlock.jmp f => AveAI.Atom ai
        | BBlock.call f fret => AveAI.Atom (AveLat.GetExprs ai)
        | BBlock.ret => AveAI.Atom ai
        | BBlock.be e f1 f2 => AveAI.Atom ai
        end.

    Definition transf_step (ai: AveAI.t) (bb: BBlock.t): (AveAI.t) := 
        match bb with     
        | BBlock.blk inst bb' => Ave_I.transf inst ai
        | BBlock.jmp f => ai
        | BBlock.call f fret =>  (AveLat.GetExprs ai)
        | BBlock.ret => ai
        | BBlock.be e f1 f2 => ai
        end.

    Definition transf_blk (ai: AveAI.t) (bb: BBlock.t): AveAI.b := 
        if AveLat.beq ai AveAI.bot then AveAI.bots else 
        AveAI.Cons ai (transf_blk' ai bb).
    
    Definition transf (ai: AveAI.t) (bb: BBlock.t): AveAI.t := 
      AveAI.getLast (transf_blk ai bb).

    (** Some boring lemma bridging facts between basic block and inst *)
    
    Lemma wf_transf_blk'_len:
      forall i ai blk ablk,
      transf_blk' ai blk = ablk 
      -> 
      BBlock.len blk = i 
      -> 
      AveAI.len ablk = i.
    Proof.
      induction i.
      - 
        intros.
        pose proof (BBlock.len_lt_zero blk). 
        lia.
      -
        intros. 
        unfold BBlock.len in H0.
        destruct blk eqn:EqBlk; rewrite <- EqBlk in H.
        {
          assert (BBlock.len blk = 1). {unfold BBlock.len; rewrite EqBlk; trivial.  }
          rewrite <- H0.
          unfold transf_blk' in H.
          rewrite EqBlk in H.
          rewrite <- H.
          unfolds AveAI.len.
          trivial.
        }
        {
          assert (BBlock.len blk = 1). {unfold BBlock.len; rewrite EqBlk; trivial.  }
          rewrite <- H0.
          unfold transf_blk' in H.
          rewrite EqBlk in H.
          rewrite <- H.
          unfolds AveAI.len.
          trivial.
        }
        {
          assert (BBlock.len blk = 1). {unfold BBlock.len; rewrite EqBlk; trivial.  }
          rewrite <- H0.
          unfold transf_blk' in H.
          rewrite EqBlk in H.
          rewrite <- H.
          unfolds AveAI.len.
          trivial.
        }
        {
          assert (BBlock.len blk = 1). {unfold BBlock.len; rewrite EqBlk; trivial.  }
          rewrite <- H0.
          unfold transf_blk' in H.
          rewrite EqBlk in H.
          rewrite <- H.
          unfolds AveAI.len.
          trivial.
        }
        {
          pose proof H.
          unfold transf_blk' in H.
          rewrite EqBlk in H.
          rewrite <- H.
          (* unfolds AveAI.len. *)
          simpls. eapply f_equal.
          folds transf_blk'.
          folds AveAI.len.
          folds BBlock.len.
          remember (transf_blk' (Ave_I.transf c ai) t) as tsf'.
          eapply eq_sym in Heqtsf'.
          eapply IHi in Heqtsf'; eauto.
          lia.
        }
    Qed.

    Lemma wf_transf_blk_ablk_len:
      forall ai blk ablk, 
        transf_blk ai blk = ablk
        -> 
        (ablk = AveAI.bots 
        \/ 
        ablk = AveAI.Cons ai (transf_blk' ai blk) /\ AveAI.len ablk = BBlock.len blk + 1
        ).
    Proof.
        intros.
        pose proof H.
        unfold transf_blk in H.
        des_ifs; try tauto.
        right.
        splits; trivial.
        remember (transf_blk' ai blk) as ablk'.
        remember (AveAI.Cons ai (transf_blk' ai blk)) as ablk.
        eapply eq_sym in Heqablk'.
        eapply wf_transf_blk'_len in Heqablk'; eauto.
        unfolds AveAI.len. rewrite Heqablk'. lia.
    Qed.

    Theorem transf_step_bot_is_bot:
        forall bb,
        transf_step AveAI.bot bb = AveAI.bot.
    Proof.
        intros.
        unfolds transf_step.
        destruct bb; eauto.
        eapply Ave_I.transf_inst_bot_is_bot.
    Qed.
    
    Theorem wf_transf_blk: (** to be simplify *)
        forall l b,
            AveAI.getFirst (transf_blk l b) = l.
    Proof.
        intros.
        remember (transf_blk l b) as ablk.
        destruct l eqn:H. 
        - unfolds AveAI.getFirst. unfolds transf_blk. 
            unfolds AveAI.bot. unfolds AveDS.L.bot; simpls.
            unfolds AveAI.bots. 
            rewrite Heqablk. auto.
        - unfolds AveAI.getFirst. unfolds transf_blk. 
            unfolds AveAI.bot. unfolds AveDS.L.bot; simpls.
            unfolds AveAI.bots. 
            rewrite Heqablk. auto.
        - unfolds AveAI.getFirst. unfolds transf_blk. 
            unfolds AveAI.bot. unfolds AveDS.L.bot; simpls.
            rewrite Heqablk. trivial.            
    Qed.  

    Theorem wf_transf_blk2:
        forall b,
            AveAI.getLast (transf_blk AveAI.bot b) = AveAI.bot.
    Proof.
        intros.
        unfolds transf_blk; unfolds transf_blk'. 
        unfolds AveAI.getLast; simpls.
        trivial.
    Qed.

    Theorem wf_transf_blk_ablk:
        forall cdhp succ enode blk l  analysis,
        AveDS.fixpoint_blk cdhp succ enode AveLat.top
            (fun (n : positive) (ai : AveAI.t) =>
            match (cdhp!n) with
            | Some b => transf_blk ai b
            | None => AveAI.Atom ai
            end) = Some analysis
        -> 
        cdhp ! l = Some blk
        ->     
        ((exists ai,
            transf_blk ai blk = analysis !! l
        )\/ analysis !! l = AveAI.bots
        ).
    Proof.
        intros.
        remember (fun (n : positive) (ai : AveAI.t) =>
            match cdhp ! n with
            | Some b => transf_blk ai b
            | None => AveAI.Atom ai
            end) as transf_blk_id.
        unfolds AveDS.fixpoint_blk.
        remember (fun (n : positive) (ai : AveDS.AI.t) =>
            AveDS.AI.getLast (transf_blk_id n ai)) as transf.
        remember (AveDS.fixpoint cdhp succ transf enode AveLat.top) as result.
        destruct result eqn:EqResult; try discriminate; eauto.
        inversion H.
        unfold "!!"; simpls.
        remember ((PTree.map transf_blk_id (snd t)) ! l) as ablk_opt.
        destruct ablk_opt  as [ablk|] eqn:EqAblkOpt.   
        - rewrite PTree.gmap in Heqablk_opt; unfolds Coqlib.option_map. 
          destruct ((snd t)!l); try discriminate; eauto.
          inversion Heqablk_opt.
          left.
          eexists.
          rewrite Heqtransf_blk_id.
          rewrite H0. 
          trivial.
        - right. trivial. 
    Qed.

    Theorem wf_transf_blk'_partial:
    forall  i ai blk ablk blk_part,
      transf_blk' ai blk = ablk
      ->
      blk[i:] = Some blk_part 
      -> 
      transf_blk' 
        (AveAI.getFirst (AveAI.br_from_i (AveAI.Cons ai ablk) i))
        blk_part 
      =
        AveAI.br_from_i ablk i. 
    Proof.
        induction i.
        - intros.
        unfolds BBlock.bb_from_i. inv H0.
        unfolds AveAI.br_from_i; unfolds AveAI.br_from_i_opt; unfolds AveAI.getFirst. trivial.
        -
          intros. 
          unfold BBlock.bb_from_i in H0.
          (* pose proof H. *)
          destruct blk eqn:EqBlk; try discriminate; eauto.
          fold BBlock.bb_from_i in H0.
          rewrite AveAI.from_cons_plus.
          (* eapply IHi in H0; eauto. *)
          unfold transf_blk' in H.
          fold transf_blk' in H. 
          remember (transf_blk' (Ave_I.transf c ai) t) as ablk'.
          eapply eq_sym in Heqablk'.
          eapply IHi in Heqablk'; eauto.
          rewrite H in Heqablk'.
          rewrite Heqablk'.
          rewrite <- H.
          rewrite AveAI.from_cons_plus.
          trivial.
    Qed.

    Theorem wf_transf_blk'_inner_step:
    forall  i ai blk ablk blk_part,
      transf_blk' ai blk = ablk
      ->
      blk[i:] = Some blk_part 
      -> 
      transf_step 
        (AveAI.getFirst (AveAI.br_from_i (AveAI.Cons ai ablk) i))
        blk_part 
      =
      AveAI.getFirst (AveAI.br_from_i (AveAI.Cons ai ablk) (i + 1)).
    Proof.
      destruct i.
      - intros. unfolds BBlock.bb_from_i.  inversion H0. rewrite <- H2.
        simpls. unfold transf_step.
        unfolds transf_blk'.
        destruct blk; unfolds AveAI.br_from_i; unfolds AveAI.getFirst; try rewrite <- H; simpls; trivial.
      - intros.
        pose proof H0.
        eapply wf_transf_blk'_partial in H0; eauto.
        rename ai into ai_entry.
        remember (AveAI.br_from_i ablk (S i)) as ablk_part.
        remember (AveAI.getFirst (AveAI.br_from_i (AveAI.Cons ai_entry ablk) (S i))) as ai.
        remember (AveAI.getFirst (AveAI.br_from_i (AveAI.Cons ai_entry ablk) (S i + 1))) as ai'.
        pose proof H0.
        unfold transf_blk' in H0.
        destruct blk_part eqn:EqBlkPart; eauto.
        * (** TODO: fix this, dup proof *)
        rewrite AveAI.from_cons_plus in Heqai.
        simpl in Heqai'.
        rewrite AveAI.from_cons_plus in Heqai'.
        replace (i+1) with (S i) in Heqai'; try lia.
        rewrite <- Heqablk_part in Heqai'.
        rewrite <- H0 in Heqai'. unfold AveAI.getFirst in Heqai'.
        unfold transf_step; rewrite Heqai'; trivial.
        * 
        rewrite AveAI.from_cons_plus in Heqai.
        simpl in Heqai'.
        rewrite AveAI.from_cons_plus in Heqai'.
        replace (i+1) with (S i) in Heqai'; try lia.
        rewrite <- Heqablk_part in Heqai'.
        rewrite <- H0 in Heqai'. unfold AveAI.getFirst in Heqai'.
        unfold transf_step; rewrite Heqai'; trivial.
        *
        rewrite AveAI.from_cons_plus in Heqai.
        simpl in Heqai'.
        rewrite AveAI.from_cons_plus in Heqai'.
        replace (i+1) with (S i) in Heqai'; try lia.
        rewrite <- Heqablk_part in Heqai'.
        rewrite <- H0 in Heqai'. unfold AveAI.getFirst in Heqai'.
        unfold transf_step; rewrite Heqai'; trivial. 
        *
        rewrite AveAI.from_cons_plus in Heqai.
        simpl in Heqai'.
        rewrite AveAI.from_cons_plus in Heqai'.
        replace (i+1) with (S i) in Heqai'; try lia.
        rewrite <- Heqablk_part in Heqai'.
        rewrite <- H0 in Heqai'. unfold AveAI.getFirst in Heqai'.
        unfold transf_step; rewrite Heqai'; trivial. 
        *
        rewrite AveAI.from_cons_plus in Heqai.
        simpl in Heqai'.
        rewrite AveAI.from_cons_plus in Heqai'.
        replace (i+1) with (S i) in Heqai'; try lia.
        rewrite <- Heqablk_part in Heqai'.
        rewrite <- H0 in Heqai'. unfold AveAI.getFirst in Heqai'.
        unfold transf_step; rewrite Heqai'; trivial.
    Qed.

    Theorem wf_transf_blk_ablk_partial:
    forall i blk blk_part ablk ai_entry ai ai',
        transf_blk ai_entry blk = ablk
        -> 
        blk[i:] = Some blk_part
        -> 
        ai = AveAI.getFirst (AveAI.br_from_i ablk i)
        ->
        ai' = AveAI.getFirst (AveAI.br_from_i ablk (i + 1))
        ->
        transf_step ai blk_part = ai'.
    Proof.
      intros.
      unfolds transf_blk.
      des_ifs.
      - do 2 rewrite AveAI.get_first_from_ablk_bots.
        eapply transf_step_bot_is_bot.
      - remember (transf_blk' ai_entry blk) as ablk.
        eapply eq_sym in Heqablk.
        eapply wf_transf_blk'_inner_step in Heqablk; eauto.
    Qed.

    Theorem wf_transf_blk_step:
        forall cdhp succ enode blk l blk_part i analysis,
        AveDS.fixpoint_blk cdhp succ enode AveLat.top
            (fun (n : positive) (ai : AveAI.t) =>
            match (cdhp!n) with
            | Some b => Ave_B.transf_blk ai b
            | None => AveAI.Atom ai
            end) = Some analysis
        -> 
        cdhp ! l = Some blk
        -> 
        blk [i:] = Some blk_part
        ->  
        transf_step  
        (AveAI.getFirst (AveAI.br_from_i analysis !! l i))
        blk_part = 
        (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1)))
        .
    Proof.
        intros.
        pose proof H.
        eapply wf_transf_blk_ablk in H2; eauto.

        remember (fun (n : positive) (ai : AveAI.t) =>
                    match cdhp ! n with
                    | Some b => transf_blk ai b
                    | None => AveAI.Atom ai
                    end) as transf_blk_real.
        unfolds AveDS.fixpoint_blk.
        remember (fun (n : positive) (ai : AveDS.AI.t) =>
                    AveDS.AI.getLast (transf_blk_real n ai)) as transf_inst.
        remember (AveDS.fixpoint cdhp succ transf_inst enode AveLat.top) as fixpoint_real.
        destruct fixpoint_real; try discriminate; eauto.
        remember (AveAI.getFirst (AveAI.br_from_i analysis !! l i)) as ai.
        remember (AveAI.getFirst (AveAI.br_from_i analysis !! l (i + 1))) as ai'.
        inversion H.
        rename t into fixpoint_result.

        remember (analysis!!l) as ablk.
        remember (fixpoint_result!!l) as ablk_entry.
        destruct H2 as [TSF | BOTS].
        2: {
          rewrite BOTS in Heqai.
          rewrite BOTS in Heqai'.
          rewrite AveAI.get_first_from_ablk_bots in Heqai.
          rewrite AveAI.get_first_from_ablk_bots in Heqai'.
          rewrite Heqai.
          rewrite Heqai'.
          eapply transf_step_bot_is_bot.
        }
        destruct TSF as (ai_entry & TSF).
        pose proof H1.
        eapply wf_transf_blk_ablk_partial; eauto.
    Qed.

    Theorem wf_transf_blk_getlast:
    forall analysis l i cdhp succ enode blk blk_part,
        AveDS.fixpoint_blk cdhp succ enode AveLat.top
            (fun (n : positive) (ai : AveAI.t) =>
            match cdhp ! n with
            | Some b => Ave_B.transf_blk ai b
            | None => AveAI.Atom ai
            end) = Some analysis
        ->
        cdhp!l = Some blk
        ->
        blk[i:] = Some blk_part
        -> 
        (AveAI.getLast (AveAI.br_from_i analysis !! l (i))) = 
        (AveAI.getLast (AveAI.br_from_i analysis !! l (i + 1))).
    Proof.
        intros.
        pose proof H.
        eapply wf_transf_blk_ablk in H; eauto.

        destruct H as [(ai & H) | H].
        2: {
          rewrite H.
          do 2 rewrite AveAI.get_last_from_ablk_bots.
          trivial.
        }
        eapply wf_transf_blk_ablk_len in H. 
        destruct H.
        -     
          rewrite H.
          do 2 rewrite AveAI.get_last_from_ablk_bots. trivial.
        -
          destruct H as (TSF & LEN).
          eapply blk_partial_i_lt_len in H1.
          eapply AveAI.get_last_from_i_eq_i_plus_one.
          lia. 
    Qed.

End Ave_B.
