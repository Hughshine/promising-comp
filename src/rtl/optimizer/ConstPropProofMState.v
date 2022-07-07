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
Require Import CorrectOpt.
Require Import ValAnalysis.
Require Import ConstProp.
Require Import CSEProofMState.

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
Require Import DelaySet.
Require Import LocalSim.

(** ** Invariant in ConstProp proof *) 
Definition I_cp (lo: Ordering.LocOrdMap) (inj: Mapping) (S: Rss) :=
  <<ID_INJ: inj = spec_inj (T_MEM S)>> /\
  <<SC_EQ: T_SC S = S_SC S>> /\ <<MEM_EQ: T_MEM S = S_MEM S>>.

(** ** Match state in ConstProp proof *) 
(** Interpretation/semantics of the result of the value analysis at each program point. *)
Definition sem_val_reg (R_src: RegFile.t) (aregs: vreg) :=
  forall r, match (VALSET.get r aregs) with
       | LVal.VAL v => RegFun.find r R_src = v
       | LVal.vtop => True
       | LVal.vbot => False
       end.

Definition sem_val_loc (tview_src: TView.t) (mem_src: Memory.t) (amem: vmem) (lo: Ordering.LocOrdMap) :=
  forall loc,
    match (VALSET.get loc amem) with
    | LVal.VAL v => exists from R, Memory.get loc (View.pln (TView.cur tview_src) loc) mem_src =
                             Some (from, Message.concrete v R) /\
                             lo loc = Ordering.nonatomic
    | LVal.vtop => True
    | LVal.vbot => False
    end.

Definition val_interp (R_src: RegFile.t) (tview_src: TView.t) (mem_src: Memory.t)
           (ae: ValLat.t) (lo: Ordering.LocOrdMap) :=
  sem_val_reg R_src (fst ae) /\ sem_val_loc tview_src mem_src (snd ae) lo.

(** Match state for current stack frame *) 
Inductive match_state_cur_stkframe:
  Ordering.LocOrdMap -> TView.t -> Memory.t ->
  (RegFile.t * BBlock.t * CodeHeap) ->
  (RegFile.t * BBlock.t * CodeHeap) -> Prop :=
| match_state_cur_stkframe_intro
    lo R_tgt BB_tgt C_tgt R_src BB_src C_src tview_src mem_src
    afunc ep ae fid
    (* function analysis *)
    (FUNC_ANALYSIS: ValDS.analyze_func (C_src, fid) succ ep transf_blk = Some afunc)
    (* transformation code heap *)
    (FUNC_TRANS: transform_cdhp C_src afunc = C_tgt)
    (* current source and target blocks transformation *)
    (TRANS_PBLK: transform_blk (transf_blk ae BB_src) BB_src = BB_tgt)
    (* current ai interpretation *)
    (AI_INTERP: val_interp R_src tview_src mem_src ae lo)
    (* RegFile eq *)
    (REGS_EQ: R_tgt = R_src)
    (* link *)
    (LINK: forall s BB_src',
        In s (succ BB_src) -> C_src ! s = Some BB_src' ->
        ValDS.L.ge (ValDS.AI.getFirst (afunc !! s)) (ValDS.AI.getLast (transf_blk ae BB_src))):
    match_state_cur_stkframe lo tview_src mem_src (R_tgt, BB_tgt, C_tgt) (R_src, BB_src, C_src).

(** Match state for stack frames. *) 
Inductive match_state_stkframes:
  Ordering.LocOrdMap ->
  Continuation.t -> Continuation.t -> Prop :=
| match_state_stkframes_done
    lo:
    match_state_stkframes lo Continuation.done Continuation.done
| match_state_stkframes_cont
    lo
    R_tgt BB_tgt C_tgt cont_tgt 
    R_src BB_src C_src cont_src
    (CUR_MATCH:  
       forall tview_src mem_src, 
         match_state_cur_stkframe lo tview_src mem_src
                                  (R_tgt, BB_tgt, C_tgt) (R_src, BB_src, C_src)
    )
    (CONT_MATCH: match_state_stkframes lo cont_tgt cont_src):
    match_state_stkframes lo
                          (Continuation.stack R_tgt BB_tgt C_tgt cont_tgt)
                          (Continuation.stack R_src BB_src C_src cont_src).

(** Match state for the thread-local state *)
Inductive match_state_tlocal:
  Mapping -> Ordering.LocOrdMap -> Memory.t ->
  (State.t * TView.t * Memory.t) -> (State.t * TView.t * Memory.t) -> Prop :=
| match_state_tlocal_intro
    inj lo mem_src
    R_tgt BB_tgt C_tgt cont_tgt Prog_tgt tview_tgt prm_tgt
    R_src BB_src C_src cont_src Prog_src tview_src prm_src
    (PROG_TRANS: transform_prog Prog_src = Some Prog_tgt)
    (CUR_STK_FRAME: match_state_cur_stkframe lo tview_src mem_src
                                             (R_tgt, BB_tgt, C_tgt)
                                             (R_src, BB_src, C_src))
    (STK_FRAMES: match_state_stkframes lo cont_tgt cont_src)
    (TVIEW_EQ: tview_tgt = tview_src)
    (PRM_EQ: prm_tgt = prm_src)
    (PRM_INDOM: forall loc to from val R,
        Memory.get loc to prm_tgt = Some (from, Message.concrete val R) ->
        exists to', inj loc to = Some to'):
    match_state_tlocal inj lo mem_src
                       (State.mk R_tgt BB_tgt C_tgt cont_tgt Prog_tgt, tview_tgt, prm_tgt)
                       (State.mk R_src BB_src C_src cont_src Prog_src, tview_src, prm_src).

(** Match state for the thread state *)
Inductive match_state_cp:
  Mapping -> Ordering.LocOrdMap -> bool ->
  Thread.t rtl_lang -> Thread.t rtl_lang -> Prop :=
| match_state_cp_intro
    inj inj' lo b
    state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
    state_src tview_src prm_src sc_src mem_src
    (INV: I_cp lo inj' (Build_Rss sc_tgt mem_tgt sc_src mem_src))
    (MATCH_THRD_LOCAL: 
       match_state_tlocal inj lo mem_src (state_tgt, tview_tgt, prm_tgt) (state_src, tview_src, prm_src))
    (ATM_BIT: (b = false /\ (forall loc t t', inj loc t = Some t' -> inj' loc t = Some t')) \/
              (b = true /\ inj = inj'))
    (* wf local, closed sc, closed memory *)
    (LOCAL_WF_TGT: Local.wf (Local.mk tview_tgt prm_tgt) mem_tgt)
    (CLOSED_SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
    (MEM_CLOSED_TGT: Memory.closed mem_tgt):
    match_state_cp inj lo b
                   (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                   (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src).

Lemma sem_val_reg_ge
      aregs aregs' R
      (SEM_VAL_REG: sem_val_reg R aregs)
      (GE: VALSET.ge aregs' aregs):
  sem_val_reg R aregs'.
Proof.
  unfold sem_val_reg in *. ii.
  specialize (SEM_VAL_REG r).
  destruct (VALSET.get r aregs) eqn:Heqe1; ss.
  unfold VALSET.ge in *.
  specialize (GE r).
  unfold LVal.ge in *.
  destruct (VALSET.get r aregs') eqn:Heqe2; ss.
  rewrite Heqe1 in GE. ss.
  rewrite Heqe1 in GE. ss.
  destruct (VALSET.get r aregs') eqn:Heqe2; ss.
  unfold VALSET.ge in *.
  specialize (GE r).
  unfold LVal.ge in *.
  rewrite Heqe2, Heqe1 in GE; ss.
  des_ifH GE; ss. subst; eauto.
  unfold VALSET.ge in *.
  specialize (GE r).
  unfold LVal.ge in *.
  rewrite Heqe2, Heqe1 in GE; ss.
Qed.

Lemma sem_val_loc_ge
      tview mem amem amem' lo
      (SEM_VAL_LOC: sem_val_loc tview mem amem lo)
      (GE: VALSET.ge amem' amem):
  sem_val_loc tview mem amem' lo.
Proof.
  unfold sem_val_loc in *. ii.
  specialize (SEM_VAL_LOC loc).
  destruct (VALSET.get loc amem) eqn:Heqe1; ss.
  unfold VALSET.ge in GE. specialize (GE loc).
  unfold LVal.ge in GE.
  rewrite Heqe1 in GE.
  destruct (VALSET.get loc amem') eqn:Heqe2; ss.
  unfold VALSET.ge in GE. specialize (GE loc).
  unfold LVal.ge in GE.
  rewrite Heqe1 in GE.
  destruct (VALSET.get loc amem') eqn:Heqe2; ss.
  des_ifH GE; ss. subst. eauto.
Qed.

Lemma ge_val_interp_prsv
      ae ae' R tview mem lo
      (GE: ValDS.AI.ge ae' ae)
      (VAL_INTERP: val_interp R tview mem ae lo):
  val_interp R tview mem ae' lo.
Proof.
  destruct ae, ae'; ss. inv GE; ss.
  unfold val_interp in *; ss. des.
  split. eapply sem_val_reg_ge; eauto.
  eapply sem_val_loc_ge; eauto.
Qed.

Lemma vreg_ge_top
      aregs R
      (GE: VALSET.ge aregs VALSET.top):
  sem_val_reg R aregs.
Proof.
  unfold VALSET.ge in *.
  unfold sem_val_reg; ii.
  specialize (GE r).
  destruct (VALSET.get r aregs) eqn:AREGS; ss.
  rewrite PTree.gempty in GE. ss.
  rewrite PTree.gempty in GE. ss.
Qed.

Lemma vloc_ge_top
      tview mem amem lo
      (GE: VALSET.ge amem VALSET.top):
  sem_val_loc tview mem amem lo.
Proof.
  unfold VALSET.ge in *; ss.
  unfold sem_val_loc; ii.
  specialize (GE loc).
  rewrite PTree.gempty in GE.
  unfold LVal.ge in *; ss.
  destruct (VALSET.get loc amem) eqn:Heqe; ss.
Qed.

Lemma val_ge_top
      ae R tview mem lo
      (GE_TOP: ValDS.L.ge ae ValLat.top):
  val_interp R tview mem ae lo.
Proof.
  destruct ae; ss.
  unfold ValDS.L.ge in *; ss. des.
  unfold val_interp. ss.
  split.
  eapply vreg_ge_top; eauto.
  eapply vloc_ge_top; eauto.
Qed.
  

  
  

  


    
