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
Require Import DetLoop.
Require Import LICM.
Require Import Lib_Ordering.

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
Require Import MsgMapping.
Require Import LocalSim.

Require Import ConsistentStableEnv.

Set Implicit Arguments.

(** * Match state for loop invariant code motion proof *)

(** ** Invariant for shared state *) 
Definition I_linv (lo: Ordering.LocOrdMap) (inj: Mapping) (rss: Rss) : Prop :=
  match rss with
  | Build_Rss sc_tgt mem_tgt sc_src mem_src =>
    <<MEM_LE: mem_id_le mem_src mem_tgt>> /\
    <<SC_LE: TimeMap.le sc_src sc_tgt>> /\
    <<ID_INJ: inj = spec_inj mem_tgt>>  
  end.

(** ** Well-defined pre-header *)
(** A pre-header block is well-defined, if:
    - all registers in the pre-header have not used in the source code;
    - all locations in the pre-header are non-atomic location. *) 
Fixpoint wdph (BB: BBlock.t) (l_entry: positive) (cdhp_s: CodeHeap) (lo: Ordering.LocOrdMap) :=
  match BB with
  | (Inst.assign r e) ## BB' =>
    (~ (RegSet.In r (regs_of_cdhp cdhp_s))) /\ wdph BB' l_entry cdhp_s lo
  | (Inst.load r loc Ordering.plain) ## BB' =>
    (~ (RegSet.In r (regs_of_cdhp cdhp_s))) /\ lo loc = Ordering.nonatomic /\ wdph BB' l_entry cdhp_s lo
  | BBlock.jmp l =>
    if Pos.eq_dec l l_entry then True else False
  | _ => False
  end.

Inductive ptB_ph_rel: BBlock.t -> BBlock.t -> (PTree.t positive) -> Prop :=
| ptB_ph_rel_inst
    c BB_t BB_s preheader
    (PT_CONT: ptB_ph_rel BB_t BB_s preheader):
    ptB_ph_rel (c ## BB_t) (c ## BB_s) preheader
| ptB_ph_rel_jmp
    l_s l_t preheader
    (PT: PTree.get l_s preheader = Some l_t):
    ptB_ph_rel (BBlock.jmp l_t) (BBlock.jmp l_s) preheader
| ptB_ph_rel_be1
    l_s l_t l preheader e
    (PT: PTree.get l_s preheader = Some l_t):
    ptB_ph_rel (BBlock.be e l_t l) (BBlock.be e l_s l) preheader
| ptB_ph_rel_be2
    l l_s l_t preheader e
    (PT: PTree.get l_s preheader = Some l_t):
    ptB_ph_rel (BBlock.be e l l_t) (BBlock.be e l l_s) preheader
| ptB_ph_rel_be3
    l_s l_t l_s' l_t' preheader e
    (PT1: PTree.get l_s preheader = Some l_t)
    (PT2: PTree.get l_s' preheader = Some l_t'):
    ptB_ph_rel (BBlock.be e l_t l_t') (BBlock.be e l_s l_s') preheader.

(** ** Match state for the thread-local state *)
Inductive match_local
          (loop_P: PTree.t (list (positive * positive * list LOOP_INV))) (lo: Ordering.LocOrdMap):
  (RegFile.t * BBlock.t * CodeHeap * Code) ->
  (RegFile.t * BBlock.t * CodeHeap * Code) -> Prop :=
| EXEC_NOT_PH
    (cdhp_s cdhp_t: CodeHeap)
    loopinvs preheader R_s R_t BB_s BB_t prog_s prog_t max_p max_p' f ep
    (TRANSC: TransC' cdhp_s (PTree.empty positive) loopinvs loopinvs max_p = (cdhp_t, max_p', preheader))
    (MAX_P_WF: forall l BB, cdhp_s ! l = Some BB -> (l < max_p)%positive)
    (LOOP_INVS: loop_P ! f = Some loopinvs)
    (CDHP_S: prog_s ! f = Some (cdhp_s, ep))
    (ORIGN_REGS: forall r, RegSet.In r (regs_of_cdhp cdhp_s) -> RegFun.find r R_t = RegFun.find r R_s)
    (SUBSET_REG: forall r, RegSet.In r (BBlock.regs_of_blk BB_s) -> RegSet.In r (regs_of_cdhp cdhp_s))
    (BLK_REL: BB_t = BB_s \/ ptB_ph_rel BB_t BB_s preheader):
    match_local loop_P lo
                 (R_t, BB_t, cdhp_t, prog_t) (R_s, BB_s, cdhp_s, prog_s)
| EXEC_PH
    (cdhp_s cdhp_t: CodeHeap)
    loopinvs preheader R_s R_t BB_s BB_t prog_s prog_t max_p max_p' f l_entry ep
    (TRANSC: TransC' cdhp_s (PTree.empty positive) loopinvs loopinvs max_p = (cdhp_t, max_p', preheader))
    (MAX_P_WF: forall l BB, cdhp_s ! l = Some BB -> (l < max_p)%positive)
    (LOOP_INVS: loop_P ! f = Some loopinvs)
    (CDHP_S: prog_s ! f = Some (cdhp_s, ep))
    (ORIGN_REGS: forall r, RegSet.In r (regs_of_cdhp cdhp_s) -> RegFun.find r R_t = RegFun.find r R_s)
    (WDPH: wdph BB_t l_entry cdhp_s lo)
    (BLK_REL: cdhp_s ! l_entry = Some BB_s):
    match_local loop_P lo
                (R_t, BB_t, cdhp_t, prog_t) (R_s, BB_s, cdhp_s, prog_s). 

Inductive match_cont
          (loop_P: PTree.t (list (positive * positive * list LOOP_INV))) (lo: Ordering.LocOrdMap):
  (Continuation.t * Code) -> (Continuation.t * Code) -> Prop :=
| cont_done
    prog_t prog_s:
    match_cont loop_P lo (Continuation.done, prog_t) (Continuation.done, prog_s)
| cont_stack
    R_t BB_t cdhp_t cont_t prog_t R_s BB_s cdhp_s cont_s prog_s
    (MATCH_CUR: match_local loop_P lo (R_t, BB_t, cdhp_t, prog_t) (R_s, BB_s, cdhp_s, prog_s))
    (MATCH_CONT: match_cont loop_P lo (cont_t, prog_t) (cont_s, prog_s)):
    match_cont loop_P lo
               (Continuation.stack R_t BB_t cdhp_t cont_t, prog_t)
               (Continuation.stack R_s BB_s cdhp_s cont_s, prog_s). 

Inductive match_tlocal (lo: Ordering.LocOrdMap): State.t -> State.t -> Prop :=
| match_tlocal_intro
    R_t BB_t cdhp_t cont_t prog_t R_s BB_s cdhp_s cont_s prog_s loop_P
    (OPT: LInv lo prog_s = Some prog_t)
    (DET_LOOP_INV: det_loop_invs prog_s lo = loop_P)
    (MATCH_CUR: match_local loop_P lo
                            (R_t, BB_t, cdhp_t, prog_t) (R_s, BB_s, cdhp_s, prog_s))
    (MATCH_CONT: match_cont loop_P lo (cont_t, prog_t) (cont_s, prog_s)):
    match_tlocal lo
                 (State.mk R_t BB_t cdhp_t cont_t prog_t)
                 (State.mk R_s BB_s cdhp_s cont_s prog_s). 

(** Match state for the thread state *)
Inductive match_state_linv:
  Mapping -> Ordering.LocOrdMap -> bool ->
  Thread.t rtl_lang -> Thread.t rtl_lang -> Prop :=
| match_state_linv_intro
    inj inj' lo b
    state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
    state_src tview_src prm_src sc_src mem_src
    (INV: I_linv lo inj' (Build_Rss sc_tgt mem_tgt sc_src mem_src))
    (MATCH_THRD_LOCAL: match_tlocal lo state_tgt state_src)
    (TVIEW_LE: TView.le tview_src tview_tgt)
    (PRM_EQ: prm_src = prm_tgt)
    (PRM_INDOM: forall loc to from val R,
        Memory.get loc to prm_tgt = Some (from, Message.concrete val R) ->
        exists to', inj loc to = Some to')
    (ATM_BIT: (b = false /\ (forall loc t t', inj loc t = Some t' -> inj' loc t = Some t')) \/
              (b = true /\ inj = inj'))
    (* wf local, closed sc, closed memory *)
    (LOCAL_WF_TGT: Local.wf (Local.mk tview_tgt prm_tgt) mem_tgt)
    (CLOSED_SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
    (MEM_CLOSED_TGT: Memory.closed mem_tgt)
    (LOCAL_WF_SRC: Local.wf (Local.mk tview_src prm_src) mem_src)
    (CLOSED_SC_SRC: Memory.closed_timemap sc_src mem_src)
    (MEM_CLOSED_SRC: Memory.closed mem_src):
    match_state_linv inj lo b
                     (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                     (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src).

Fixpoint wdph_aux (BB_t: BBlock.t) (f_entry: positive)
         (loop_invs: list (positive * positive * list LOOP_INV)) : Prop :=
  match BB_t with
  | Inst.assign r e ## BB_t' =>
    (exists l1 l2 loopinvs, In (l1, l2, loopinvs) loop_invs /\ In (LINV_EXPR r e) loopinvs) /\
    wdph_aux BB_t' f_entry loop_invs
  | Inst.load r loc Ordering.plain ## BB_t' =>
    (exists l1 l2 loopinvs, In (l1, l2, loopinvs) loop_invs /\ In (LINV_LOC r loc) loopinvs) /\
    wdph_aux BB_t' f_entry loop_invs
  | BBlock.jmp f => if Pos.eq_dec f f_entry then True else False
  | _ => False
  end.

Lemma wdph_aux_cons'
      linv loopinvs l_entry l1 l2 loop_invs BB loopinvs0
      (WDPH: wdph_aux BB l_entry loop_invs)
      (IN: In (l1, l2, loopinvs0 ++ linv :: loopinvs) loop_invs):
  wdph_aux (alloc_inst linv ## BB) l_entry loop_invs.
Proof.
  destruct linv; ss; splits; eauto.
  exists l1 l2 (loopinvs0 ++ LINV_EXPR r e :: loopinvs).
  split; eauto. eapply in_app. right. ss. eauto.
  exists l1 l2 (loopinvs0 ++ LINV_LOC r loc :: loopinvs).
  split; eauto. eapply in_app. right. ss. eauto.
Qed.

Lemma wdph_aux_cons:
  forall loopinvs l_entry loop_invs BB loopinvs0 l1 l2
    (WDPH: wdph_aux BB l_entry loop_invs)
    (IN: In (l1, l2, loopinvs0 ++ loopinvs) loop_invs),
    wdph_aux (consInv loopinvs BB) l_entry loop_invs.
Proof.
  induction loopinvs; ii; ss; eauto.
  eapply IHloopinvs; eauto.
  2: {  instantiate (1 := loopinvs0 ++ (a :: nil)). rewrite <- app_assoc. ss. eauto. }
  eapply wdph_aux_cons' in IN; eauto.
Qed.

Lemma wdph_aux_diff:
  forall BB l loop_invs l1 l2
    (WDPH_AUX: wdph_aux BB l loop_invs)
    (DISJ: l2 <> l),
    wdph_aux (ptB_ph l1 l2 BB) l loop_invs.
Proof.
  induction BB; ii; ss; eauto.
  - des_ifH WDPH_AUX; tryfalse; ss; eauto. subst.
    unfold pt_modify. des_if; eauto.
    des_ifH n; ss; eauto.
  - destruct c; ss; eauto.
    + des. split; eauto.
    + destruct or; ss.
      des. split; eauto.
Qed.

Lemma wdph_aux_alloc:
  forall loopinvs l1 l2 loop_invs loopinvs0
    (IN: In (l1, l2, loopinvs0 ++ loopinvs) loop_invs),
    wdph_aux (alloc_ph loopinvs l1) l1 loop_invs.
Proof.
  induction loopinvs; ii; ss; eauto.
  - des_if; eauto.
  - destruct a; ss; eauto.
    + split.
      exists l1 l2 (loopinvs0 ++ LINV_EXPR r e :: loopinvs). split; eauto.
      eapply in_or_app. right; ss. eauto.
      eapply IHloopinvs; eauto.
      instantiate (2 := l2).
      instantiate (1 := (loopinvs0 ++ (LINV_EXPR r e) :: nil)).
      rewrite <- app_assoc. eauto.
    + split.
      exists l1 l2 (loopinvs0 ++ LINV_LOC r loc :: loopinvs). split; eauto.
      eapply in_or_app. right; ss. eauto.
      eapply IHloopinvs; eauto.
      instantiate (2 := l2).
      instantiate (1 := (loopinvs0 ++ (LINV_LOC r loc) :: nil)).
      rewrite <- app_assoc. eauto.
Qed.

Lemma ptB_ph_rel_cons:
  forall BB preheader l_ph l_entry
    (PREHEADER: preheader ! l_entry = Some l_ph),
    (ptB_ph_rel (ptB_ph l_ph l_entry BB) BB preheader) \/
    BB = (ptB_ph l_ph l_entry BB).
Proof.
  induction BB; ii; ss; eauto; try solve [econs; eauto].
  - unfold pt_modify. des_if; subst; eauto.
    left. econs; eauto.
  - unfold pt_modify.
    des_if; subst; eauto.
    des_if; subst; eauto.
    left. econs; eauto.
    left. econs; eauto.
    des_if; subst; eauto.
    left. econs; eauto.
  - exploit IHBB; eauto. i.
    des1.
    left. econs; eauto.
    right. rewrite <- H. eauto.
Qed.

Lemma ptB_ph_rel_cons2:
  forall BB_t l_ph l_entry BB_s preheader
    (ENTRY_NOT_PH: (l_entry < l_ph)%positive)
    (PTB_PH_REL: ptB_ph_rel BB_t (ptB_ph l_ph l_entry BB_s) preheader)
    (PREHEADER: preheader ! l_entry = Some l_ph)
    (PREHEADER2: preheader ! l_ph = None),
    BB_t = BB_s \/ ptB_ph_rel BB_t BB_s preheader.
Proof.
  induction BB_t; ii; eauto.
  - destruct BB_s; ss; eauto;
      try solve [inv PTB_PH_REL; ss].
    unfold pt_modify in *. des_ifH PTB_PH_REL; ss; subst; eauto.
    inv PTB_PH_REL.
    unfold Language.fid, IdentMap.key in *. tryfalse.
  - destruct BB_s; ss; eauto; try solve [inv PTB_PH_REL; ss].
  - destruct BB_s; ss; eauto; try solve [inv PTB_PH_REL; ss].
    unfold pt_modify in *.
    des_ifH PTB_PH_REL; subst; ss; eauto.
    {
      des_ifH PTB_PH_REL; subst; ss; eauto.
      inv PTB_PH_REL;
        try solve [unfold Language.fid, IdentMap.key in *; ss; tryfalse].
      inv PTB_PH_REL;
        try solve [unfold Language.fid, IdentMap.key in *; ss; tryfalse].
      right. econs; eauto.
    }
    {
      des_ifH PTB_PH_REL; subst; ss; eauto.
      inv PTB_PH_REL;
        try solve [unfold Language.fid, IdentMap.key in *; ss; tryfalse].
      right. econs; eauto.
    }
  - inv PTB_PH_REL.
  - destruct BB_s; ss; eauto;
      try solve [inv PTB_PH_REL; ss].
    inv PTB_PH_REL.
    eapply IHBB_t in PT_CONT; eauto.
    des; subst; eauto.
    right. econs; eauto.
Qed.

Lemma well_defined_preheader_I':
  forall loop_invs0 cdhp_s cdhp_t BB_s preheader l_s l0
    max_p max_p' preheader0 loop_invs
    (TRANS: TransC' cdhp_s preheader0 loop_invs0 loop_invs max_p = (cdhp_t, max_p', preheader))
    (BLK: cdhp_s ! l_s = Some BB_s)
    (PRE_HEADER0: preheader0 ! l0 = Some l_s)
    (WF_MAX_P: forall l BB, cdhp_s ! l = Some BB -> (l < max_p)%positive)
    (WF_PH: forall l l', preheader0 ! l = Some l' -> exists BB, cdhp_s ! l' = Some BB)
    (IN: forall linv, In linv loop_invs0 -> In linv loop_invs)
    (WDPH: wdph_aux BB_s l0 loop_invs),
  exists BB_t, preheader ! l0 = Some l_s /\ cdhp_t ! l_s = Some BB_t /\
          wdph_aux BB_t l0 loop_invs.
Proof.
  induction loop_invs0; ii; ss; eauto.
  - inv TRANS. exists BB_s. splits; eauto.
  - destruct a. destruct p.
    destruct (preheader0 ! p) eqn:Heqe; ss.
    {
      (* the preheader of p has already been allocated *)
      exploit WF_PH; [eapply Heqe | eauto..]. i. des1.
      rewrite H in TRANS.  
      destruct (Pos.eq_dec p l0); subst; eauto.
      {
        rewrite Heqe in PRE_HEADER0. inv PRE_HEADER0.
        rewrite BLK in H. inv H.
        eapply IHloop_invs0 with (BB_s := consInv l BB) in TRANS; eauto.
        {
          rewrite PTree.gss; eauto.
        }
        {
          ii.
          destruct (Pos.eq_dec l_s l1); subst; eauto.
          rewrite PTree.gso in H; eauto.
        }
        {
          ii. eapply WF_PH in H. des1.
          destruct (Pos.eq_dec l_s l'); subst; eauto.
          rewrite PTree.gss; eauto.
          rewrite PTree.gso; eauto.
        }
        {
          exploit IN; eauto. ii. 
          eapply wdph_aux_cons; eauto.
          instantiate (2 := p0). instantiate (1 := nil). ss. eauto.
        }
      }
      {
        destruct (Pos.eq_dec p1 l_s); subst; eauto.
        {
          rewrite BLK in H. inv H.
          eapply IHloop_invs0 with (BB_s := consInv l BB) in TRANS; eauto.
          {
            rewrite PTree.gss; eauto.
          }
          {
            ii.
            destruct (Pos.eq_dec l_s l1); subst; eauto.
            rewrite PTree.gso in H; eauto.
          }
          {
            ii. eapply WF_PH in H. des1.
            destruct (Pos.eq_dec l_s l'); subst; eauto.
            rewrite PTree.gss; eauto.
            rewrite PTree.gso; eauto.
          }
          { 
            exploit IN; eauto. ii. 
            eapply wdph_aux_cons; eauto.
            instantiate (2 := p0). instantiate (1 := nil). ss. eauto.
          }
        }
        {
          eapply IHloop_invs0 in TRANS; eauto.
          {
            rewrite PTree.gso; eauto.
          }
          {
            ii.
            destruct (Pos.eq_dec p1 l1); subst.
            rewrite PTree.gss in H0. inv H0. eauto.
            rewrite PTree.gso in H0; eauto.
          }
          {
            ii.
            eapply WF_PH in H0. des1.
            destruct (Pos.eq_dec p1 l'); subst; eauto.
            rewrite PTree.gss; eauto.
            rewrite PTree.gso; eauto.
          }
        }
      }
    }
    {
      (* the preheader of p has not been allocated *)
      eapply IHloop_invs0 with
        (BB_s := if is_exit l_s loop_invs then BB_s else ptB_ph max_p p BB_s) in TRANS; eauto.
      {
        destruct (Pos.eq_dec max_p l_s); subst; eauto.
        eapply WF_MAX_P in BLK; eauto.
        eapply Pos.lt_irrefl in BLK. ss.
        rewrite PTree.gso; eauto.
        unfold ptC_ph. rewrite PTree.gmap. unfold option_map. rewrite BLK. eauto.
      }
      {
        destruct (Pos.eq_dec p l0); subst; eauto; tryfalse.
        rewrite PTree.gso; eauto.
      }
      {
        ii. destruct (Pos.eq_dec max_p l1); subst.
        eapply Pos.lt_succ_diag_r; eauto.
        rewrite PTree.gso in H; eauto.
        eapply ptC_ph_dom_eq in H. do 2 des1.
        eapply WF_MAX_P in H.
        assert ((max_p < Pos.succ max_p)%positive).
        {
          eapply Pos.lt_succ_diag_r; eauto.
        }
        eapply Pos.lt_trans; eauto.
      }
      {
        ii. 
        destruct (Pos.eq_dec p l1); subst.
        {
          rewrite PTree.gss in H. inv H.
          rewrite PTree.gss; eauto.
        }
        {
          rewrite PTree.gso in H; eauto.
          destruct (Pos.eq_dec max_p l'); subst; eauto.
          eapply WF_PH in H. des1. eapply WF_MAX_P in H.
          eapply POrderedType.Positive_as_OT.lt_irrefl in H. ss.
          rewrite PTree.gso; eauto.
          eapply WF_PH in H. des1.
          eapply ptC_ph_dom_eq2 in H; eauto. do 2 des1.
          rewrite H. eauto.
        }
      }
      {
        destruct (Pos.eq_dec p l0); subst. tryfalse.
        des_if; eauto.
        eapply wdph_aux_diff; eauto.
      }
    }
Qed.

Lemma well_defined_preheader_I'':
  forall loop_invs0 cdhp_s cdhp_t BB_t preheader l_s l_t
    max_p max_p' preheader0 loop_invs
    (PRE_HEADER: preheader ! l_s = Some l_t)
    (BLK: PTree.get l_t cdhp_t = Some BB_t)
    (TRANS: TransC' cdhp_s preheader0 loop_invs0 loop_invs max_p = (cdhp_t, max_p', preheader))
    (WF_MAX_P: forall l BB, cdhp_s ! l = Some BB -> (l < max_p)%positive)
    (WF_PH: forall l l', preheader0 ! l = Some l' -> exists BB, cdhp_s ! l' = Some BB)
    (IN: forall linv, In linv loop_invs0 -> In linv loop_invs)
    (WF_PH0: preheader0 ! l_s = None),
  (exists loopinvs l_s', In (l_s, l_s', loopinvs) loop_invs) /\ wdph_aux BB_t l_s loop_invs /\ (max_p <= l_t)%positive.
Proof.
  induction loop_invs0; ii; ss; eauto.
  - inv TRANS. tryfalse.
  - destruct a. destruct p.
    destruct (preheader0 ! p) eqn:Heqe1; ss.
    {
      (* the preheader of p has already been allocated *)
      exploit WF_PH; eauto. i. des1. rewrite H in TRANS; ss. clear H.
      eapply IHloop_invs0 in TRANS; eauto.

      ii. exploit WF_PH; eauto. i. des1. exploit WF_MAX_P; eauto. i.
      destruct (Pos.eq_dec p1 l0); subst; eauto.
      rewrite PTree.gso in H; eauto.

      ii.
      destruct (Pos.eq_dec p1 l'); subst; eauto.
      rewrite PTree.gss. eauto.
      rewrite PTree.gso; eauto.
    }
    {
      (* the preheader of p has not been allocated *)
      destruct (Pos.eq_dec p l_s); subst.
      {
        exploit well_defined_preheader_I'; eauto.
        {
          instantiate (2 := max_p). rewrite PTree.gss. eauto.
        }
        {
          instantiate (1 := l_s). rewrite PTree.gss; eauto.
        }
        {
          ii.
          destruct (Pos.eq_dec max_p l0); subst; eauto.
          {
            eapply Pos.lt_succ_diag_r; eauto.
          }
          {
            rewrite PTree.gso in H; eauto.
            eapply ptC_ph_dom_eq in H. do 2 des1.
            eapply WF_MAX_P in H.
            assert (SUCC_LT: (max_p < Pos.succ max_p)%positive).
            {
              eapply Pos.lt_succ_diag_r; eauto.
            }
            eapply Pos.lt_trans; eauto.
          }
        }
        {
          ii.
          destruct (Pos.eq_dec l_s l0); subst.
          {
            rewrite PTree.gss in H. inv H.
            rewrite PTree.gss; eauto.
          }
          {
            rewrite PTree.gso in H; eauto.
            destruct (Pos.eq_dec max_p l'); subst; eauto.
            rewrite PTree.gss; eauto.
            rewrite PTree.gso; eauto.
            eapply WF_PH in H. des1.
            eapply ptC_ph_dom_eq2 in H; eauto. do 2 des1.
            rewrite H; eauto.
          }
        }
        {
          exploit IN; eauto. ii.
          eapply wdph_aux_alloc; eauto.
          instantiate (2 := p0). instantiate (1 := nil). ss.
        }
        {
          ii. des. rewrite PRE_HEADER in H. inv H.
          rewrite BLK in H0. inv H0. splits; eauto.
          eapply Pos.le_refl; eauto.
        }
      }
      {
        eapply IHloop_invs0 in TRANS; eauto.
        {
          des. splits; eauto.
          assert (SUCC_LT: (max_p < Pos.succ max_p)%positive).
          {
            eapply Pos.lt_succ_diag_r; eauto.
          }
          eapply Pos.lt_le_incl; eauto.
          eapply Pos.lt_le_trans; eauto.
        }
        {
          ii.
          destruct (Pos.eq_dec max_p l0); subst; eauto.
          {
            eapply Pos.lt_succ_diag_r; eauto.
          }
          {
            rewrite PTree.gso in H; eauto. 
            eapply ptC_ph_dom_eq in H; eauto. do 2 des1.
            exploit WF_MAX_P; eauto. ii.
            assert (SUCC_LT: (max_p < Pos.succ max_p)%positive).
            {
              eapply Pos.lt_succ_diag_r; eauto.
            }
            eapply Pos.lt_trans; eauto.
          }
        }
        {
          ii.
          destruct (Pos.eq_dec p l0); subst; eauto.
          {
            rewrite PTree.gss in H. inv H. rewrite PTree.gss. eauto.
          }
          {
            rewrite PTree.gso in H; eauto.
            exploit WF_PH; eauto. i. des1.
            exploit WF_MAX_P; eauto. i.
            destruct (Pos.eq_dec max_p l'); subst; tryfalse. eapply Pos.lt_irrefl in H1; ss.
            rewrite PTree.gso; eauto.
            eapply ptC_ph_dom_eq2 in H0; eauto. do 2 des1.
            rewrite H0. eauto.
          }
        }
        {
          rewrite PTree.gso; eauto.
        }
      }
    }
Qed.
    
Lemma well_defined_preheader_I
      loop_invs cdhp_s cdhp_t BB_t preheader l_s l_t
      max_p max_p'
      (PRE_HEADER: preheader ! l_s = Some l_t)
      (BLK: PTree.get l_t cdhp_t = Some BB_t)
      (TRANS: TransC' cdhp_s (PTree.empty positive) loop_invs loop_invs max_p = (cdhp_t, max_p', preheader))
      (WF_MAX_P: forall l BB, cdhp_s ! l = Some BB -> (l < max_p)%positive):
  (exists loopinvs l_s', In (l_s, l_s', loopinvs) loop_invs) /\ wdph_aux BB_t l_s loop_invs /\ (max_p <= l_t)%positive.
Proof.
  eapply well_defined_preheader_I''; eauto.
  ii. rewrite PTree.gempty in H. ss.
  rewrite PTree.gempty; eauto.
Qed.

Lemma wdph_aux_to_wdph:
  forall BB l cdhp lo ep
    (WDPH_AUX: wdph_aux BB l (loop_invC lo (cdhp, ep))),
    wdph BB l cdhp lo.
Proof.
  induction BB; ii; eauto.
  ss. destruct c; ss. des.
  eapply wf_loop_invC2 in WDPH_AUX; eauto.
  destruct or; ss.
  des.
  lets WDPH_AUX': WDPH_AUX.
  eapply wf_loop_invC2 in WDPH_AUX; eauto.
  eapply wf_loop_invC3 in WDPH_AUX'; eauto.
Qed.

Lemma well_defined_preheader
      loop_invs cdhp_s cdhp_t BB_t preheader l_s l_t max_p max_p' ep lo
      (PRE_HEADER: preheader ! l_s = Some l_t)
      (BLK: cdhp_t ! l_t = Some BB_t)
      (LOOP_INVS: loop_invs = loop_invC lo (cdhp_s, ep))
      (TRANS: TransC' cdhp_s (PTree.empty positive) loop_invs loop_invs max_p = (cdhp_t, max_p', preheader))
      (WF_MAX_P: forall l BB, cdhp_s ! l = Some BB -> (l < max_p)%positive):
  exists BB_s, cdhp_s ! l_s = Some BB_s /\ cdhp_s ! l_t = None /\ wdph BB_t l_s cdhp_s lo.
Proof.
  exploit well_defined_preheader_I; eauto. i. des. subst.
  exploit wf_loop_invC1; eauto. i. des.
  exists BB0. splits; eauto.
  destruct (cdhp_s ! l_t) eqn:Heqe; eauto.
  eapply WF_MAX_P in Heqe.
  exploit Pos.lt_le_trans; eauto. i. eapply Pos.lt_irrefl in H2. ss.
  eapply wdph_aux_to_wdph; eauto.
Qed.

Lemma well_defined_preheader2''':
  forall loop_invs0 loop_invs cdhp_s cdhp_t preheader0 preheader max_p max_p' l
    (TRANS: TransC' cdhp_s preheader0 loop_invs0 loop_invs max_p = (cdhp_t, max_p', preheader))
    (WF_PH: forall l l', preheader0 ! l = Some l' -> exists BB, cdhp_s ! l' = Some BB)
    (IN: forall l_entry l_exit linvs, In (l_entry, l_exit, linvs) loop_invs0 ->
                                 (In (l_entry, l_exit, linvs) loop_invs /\ (l_entry < max_p)%positive))
    (WF_MAX_P: forall l BB, cdhp_s ! l = Some BB -> (l < max_p)%positive)
    (PREHEADER: preheader0 ! l = None),
    (preheader ! l = None) \/ (exists l_exit linvs, In (l, l_exit, linvs) loop_invs0).
Proof.
  induction loop_invs0; ii; ss; eauto.
  - inv TRANS. eauto.
  - destruct a. destruct p.
    destruct (preheader0 ! p) eqn:PREHEADER0; ss.
    {
      (* the preheader of p has already been allocated *)
      exploit WF_PH; eauto. i. des1. rewrite H in TRANS; ss; clear H.
      eapply IHloop_invs0 in TRANS; eauto.
      {
        des; eauto. 
      }
      {
        ii. destruct (Pos.eq_dec p1 l'); subst; eauto.
        rewrite PTree.gss; eauto.
        rewrite PTree.gso; eauto.
      }
      {
        ii. destruct (Pos.eq_dec p1 l1); subst; eauto.
        eapply WF_PH in PREHEADER0; eauto. des1.
        eapply WF_MAX_P in PREHEADER0; eauto.
        rewrite PTree.gso in H; ss; eauto.
      }
    }
    {
      (* the preheader of p has not been allocated *)
      destruct (Pos.eq_dec p l); subst; eauto.
      
      eapply IHloop_invs0 with (l := l) in TRANS; eauto.
      {
        des1; eauto.
        des. eauto.
      }
      {
        ii. destruct (Pos.eq_dec p l1); subst.
        rewrite PTree.gss in H. inv H. rewrite PTree.gss; eauto.
        rewrite PTree.gso in H; eauto.
        destruct (Pos.eq_dec max_p l'); subst; eauto.
        rewrite PTree.gss; eauto.
        rewrite PTree.gso; eauto.
        eapply WF_PH in H. des1.
        eapply ptC_ph_dom_eq2 in H; eauto. do 2 des1.
        rewrite H; eauto.
      }
      {
        ii; eauto. exploit IN; eauto. i. des1.
        split; eauto.
        assert (SUCC_LT: (max_p < Pos.succ max_p)%positive).
        {
          eapply Pos.lt_succ_diag_r; eauto.
        }
        eapply Pos.lt_trans; eauto.
      }
      {
        ii. destruct (Pos.eq_dec max_p l1); subst; eauto.
        eapply Pos.lt_succ_diag_r; eauto.
        rewrite PTree.gso in H; eauto.
        eapply ptC_ph_dom_eq in H; eauto. do 2 des1.
        eapply WF_MAX_P in H.
        assert (SUCC_LT: (max_p < Pos.succ max_p)%positive).
        {
          eapply Pos.lt_succ_diag_r; eauto.
        }
        eapply Pos.lt_trans; eauto.
      }
      {
        rewrite PTree.gso; eauto.
      }
    }
Qed.

Lemma well_defined_preheader2'':
  forall loop_invs0 loop_invs cdhp_s cdhp_t preheader0 preheader max_p max_p' l l'
    (TRANS: TransC' cdhp_s preheader0 loop_invs0 loop_invs max_p = (cdhp_t, max_p', preheader))
    (PRE_HEADER: preheader0 ! l = Some l'),
    preheader ! l = Some l'.
Proof.
  induction loop_invs0; ss; eauto; ii.
  inv TRANS; eauto.
  destruct a. destruct p.
  destruct (preheader0 ! p) eqn:Heqe; eauto.
  {
    destruct (cdhp_s ! p1) eqn:Heqe1; ss; eauto.
  }
  {
    eapply IHloop_invs0 in TRANS; eauto.
    destruct (Pos.eq_dec p l); subst; tryfalse.
    rewrite PTree.gso; eauto.
  }
Qed.

Lemma well_defined_preheader2':
  forall loop_invs0 loop_invs cdhp_s cdhp_t BB_t l preheader0 preheader max_p max_p'
    (BLK: cdhp_t ! l = Some BB_t)
    (TRANS: TransC' cdhp_s preheader0 loop_invs0 loop_invs max_p = (cdhp_t, max_p', preheader))
    (WF_PH: forall l l', preheader0 ! l = Some l' -> (exists BB, cdhp_s ! l' = Some BB))
    (WF_PH1: forall l l', preheader0 ! l = Some l' -> (exists BB, cdhp_s ! l = Some BB))
    (IN: forall l_entry l_exit linvs, In (l_entry, l_exit, linvs) loop_invs0 ->
                                 (In (l_entry, l_exit, linvs) loop_invs /\ (exists BB, cdhp_s ! l_entry = Some BB)))
    (WF_MAX_P: forall l BB, cdhp_s ! l = Some BB -> (l < max_p)%positive),
    (exists l0, preheader ! l0 = Some l) \/ 
    (exists BB_s, cdhp_s ! l = Some BB_s /\ (BB_t = BB_s \/ ptB_ph_rel BB_t BB_s preheader)).
Proof.
  induction loop_invs0; ii; ss.
  - inv TRANS. right. exists BB_t. split; eauto.
  - destruct a. destruct p. 
    destruct (preheader0 ! p) eqn:PRE_HEADER_p.
    {
      (* the preheader of p has already been allocated *)
      exploit WF_PH; eauto. i. des. rewrite H in TRANS.
      exploit IHloop_invs0; [ | eapply TRANS | eauto..]; eauto.
      {
        ii.
        destruct (Pos.eq_dec p1 l'); subst; eauto.
        rewrite PTree.gss; eauto.
        rewrite PTree.gso; eauto.
      }
      {
        ii.
        destruct (Pos.eq_dec p1 l1); subst; eauto.
        rewrite PTree.gss; eauto.
        rewrite PTree.gso; eauto.
      }
      {
        ii. exploit IN; eauto. i. des.
        split; eauto.
        destruct (Pos.eq_dec p1 l_entry); subst; eauto.
        rewrite PTree.gss; eauto.
        rewrite PTree.gso; eauto.
      }
      {
        ii. destruct (Pos.eq_dec p1 l1); subst; eauto.
        rewrite PTree.gso in H0; eauto.
      }

      i. do 2 des1. eauto.
      des1.
      destruct (Pos.eq_dec p1 l); subst; eauto.
      {
        eapply well_defined_preheader2'' with (l := p) in TRANS; eauto.
      }
      {
        rewrite PTree.gso in H0; eauto.
      }
    }
    {
      (* the preheader of p has not been allocated *)
      lets PRE_HEADER': TRANS.
      lets TEMP: TRANS.
      eapply well_defined_preheader2'' with (l := p) (l' := max_p) in PRE_HEADER'; eauto.
      2: { rewrite PTree.gss; eauto. }
      assert (P_LT_MAX_P: (p < max_p)%positive).
      {
        exploit IN; eauto. i. des.
        exploit WF_MAX_P; eauto.
      }
      
      destruct (Pos.eq_dec max_p l); subst; eauto.
      eapply IHloop_invs0 in TRANS; eauto.
      {
        des1. des1. eauto.
        do 2 des1.
        rewrite PTree.gso in TRANS; eauto. unfold ptC_ph in TRANS.
        rewrite PTree.gmap in TRANS.
        unfold option_map in TRANS.
        destruct (cdhp_s ! l) eqn:Heqe; eauto.
        des_ifH TRANS.
        inv TRANS; eauto.
        inv TRANS. des1; subst; eauto.
        {
          right. exists t. split; eauto.
          eapply ptB_ph_rel_cons with (BB := t) in PRE_HEADER'.
          des; subst; eauto.
        }
        {
          destruct (preheader0 ! max_p) eqn:PRE_HEADER0; ss.
          eapply WF_PH1 in PRE_HEADER0. des1.
          eapply WF_MAX_P in PRE_HEADER0. eapply Pos.lt_irrefl in PRE_HEADER0. ss.
          exploit ptB_ph_rel_cons2; eauto.
          eapply well_defined_preheader2''' with (l := max_p) in TEMP; eauto.
          {
            des1; eauto.
            do 2 des1. exploit IN; eauto. i. do 2 des1.
            eapply WF_MAX_P in H0.
            eapply Pos.lt_irrefl in H0. tryfalse.
          }
          {
            ii. destruct (Pos.eq_dec p l1); subst.
            rewrite PTree.gss in H. inv H.
            rewrite PTree.gss; eauto.
            rewrite PTree.gso in H; eauto.
            destruct (Pos.eq_dec max_p l'); subst; eauto.
            rewrite PTree.gss; eauto.
            rewrite PTree.gso; eauto.
            eapply WF_PH in H. des1. eapply ptC_ph_dom_eq2 in H; eauto.
            do 2 des1. rewrite H; eauto.
          }
          {
            ii. exploit IN; eauto. i. do 2 des1.
            split; eauto.
            eapply WF_MAX_P in H1.
            assert (SUCC_LT: (max_p < Pos.succ max_p)%positive).
            eapply Pos.lt_succ_diag_r; eauto.
            eapply Pos.lt_trans; eauto.
          }
          {
            ii. destruct (Pos.eq_dec max_p l1); subst.
            eapply Pos.lt_succ_diag_r; eauto.
            rewrite PTree.gso in H; eauto.
            eapply ptC_ph_dom_eq in H; eauto. do 2 des1.
            eapply WF_MAX_P in H.
            assert (SUCC_LT: (max_p < Pos.succ max_p)%positive).
            eapply Pos.lt_succ_diag_r; eauto.
            eapply Pos.lt_trans; eauto.
          }
          {
            destruct (Pos.eq_dec p max_p); subst.
            eapply POrderedType.Positive_as_OT.lt_irrefl in P_LT_MAX_P; eauto. tryfalse.
            rewrite PTree.gso; eauto.
          }
        }
      }
      {
        ii.
        destruct (Pos.eq_dec max_p l'); subst; eauto.
        rewrite PTree.gss; eauto.
        destruct (Pos.eq_dec p l1); subst; eauto.
        rewrite PTree.gss in H. inv H. rewrite PTree.gss; eauto.
        rewrite PTree.gso in H; eauto.
        rewrite PTree.gso; eauto.
        eapply WF_PH in H; eauto. des1.
        eapply ptC_ph_dom_eq2 in H; eauto. do 2 des1.
        rewrite H; eauto.
      }
      {
        ii. destruct (Pos.eq_dec p l1); subst.
        {
          exploit IN; eauto. i. do 2 des1.
          destruct (Pos.eq_dec max_p l1); subst; eauto.
          rewrite PTree.gss; eauto.
          rewrite PTree.gso; eauto.
          eapply ptC_ph_dom_eq2 in H1; eauto. do 2 des1.
          rewrite H1. eauto.
        }
        {
          rewrite PTree.gso in H; eauto.
          destruct (Pos.eq_dec max_p l1); subst; eauto.
          rewrite PTree.gss; eauto.
          rewrite PTree.gso; eauto.
          eapply WF_PH1 in H. des1.
          eapply ptC_ph_dom_eq2 in H; eauto. do 2 des1.
          rewrite H. eauto.
        }
      }

      ii. exploit IN; eauto. i. do 2 des1.
      split; eauto.
      destruct (Pos.eq_dec max_p l_entry); subst; eauto.
      rewrite PTree.gss; eauto.
      rewrite PTree.gso; eauto.
      eapply ptC_ph_dom_eq2 in H1; eauto. do 2 des1.
      rewrite H1. eauto.
      i. destruct (Pos.eq_dec max_p l1); subst.
      eapply Pos.lt_succ_diag_r; eauto.
      rewrite PTree.gso in H; eauto.
      eapply ptC_ph_dom_eq in H; eauto. do 2 des1.
      eapply WF_MAX_P in H.
      assert (SUCC_LT: (max_p < Pos.succ max_p)%positive).
      {
        eapply Pos.lt_succ_diag_r; eauto.
      }
      eapply Pos.lt_trans; eauto.
    }
Qed.

Lemma well_defined_preheader3:
  forall loop_invs0 loop_invs cdhp_s cdhp_t l preheader0 preheader max_p max_p' BB_s
    (TRANS: TransC' cdhp_s preheader0 loop_invs0 loop_invs max_p = (cdhp_t, max_p', preheader))
    (GET_SRC: cdhp_s ! l = Some BB_s),
  exists BB_t, cdhp_t ! l = Some BB_t.
Proof.
  induction loop_invs0; ii; ss; eauto.
  inv TRANS. eauto.
  destruct a. destruct p; ss.
  destruct (preheader0 ! p) eqn:PREHEADER_P; ss; eauto.
  {
    destruct (cdhp_s ! p1) eqn:CDHP_S; ss; eauto.
    destruct (Pos.eq_dec p1 l); subst; eauto.
    eapply IHloop_invs0 in TRANS; eauto.
    rewrite PTree.gss; eauto.
    eapply IHloop_invs0 in TRANS; eauto.
    rewrite PTree.gso; eauto.
  }
  {
    destruct (Pos.eq_dec max_p l); subst.
    eapply IHloop_invs0 in TRANS; eauto. rewrite PTree.gss; eauto.
    eapply ptC_ph_dom_eq2 in GET_SRC. do 2 des1.
    eapply IHloop_invs0 in TRANS; eauto. rewrite PTree.gso; eauto.
  }
Qed.
  
Lemma well_defined_preheader4:
  forall loop_invs0 loop_invs cdhp_s cdhp_t l_s l_t preheader0 preheader max_p max_p'
    (TRANS: TransC' cdhp_s preheader0 loop_invs0 loop_invs max_p = (cdhp_t, max_p', preheader))
    (PRE_HEADER: preheader ! l_s = Some l_t),
    preheader0 ! l_s = Some l_t \/ (exists BB_t, cdhp_t ! l_t = Some BB_t).
Proof.
  induction loop_invs0; ii; ss; eauto.
  inv TRANS. eauto.
  destruct a. destruct p.
  destruct (preheader0 ! p) eqn:PREHEADER_P; ss; eauto.
  {
    destruct (cdhp_s ! p1) eqn:CDHP_S; ss; eauto.
  }
  {
    lets TRANS': TRANS.
    eapply IHloop_invs0 in TRANS; eauto. des; eauto.
    destruct (Pos.eq_dec p l_s); subst; eauto.
    rewrite PTree.gss in TRANS. inv TRANS.
    eapply well_defined_preheader3 in TRANS'; eauto.
    rewrite PTree.gss; eauto.
    rewrite PTree.gso in TRANS; eauto.
  }
Qed.
  
Lemma transC'_prop
      cdhp_s cdhp_t l BB_s BB_t loop_invs max_p max_p' preheader ep lo
      (TRANSC': TransC' cdhp_s (PTree.empty positive) loop_invs loop_invs max_p = (cdhp_t, max_p', preheader))
      (BLK_TGT: cdhp_t ! l = Some BB_t)
      (BLK_SRC: cdhp_s ! l = Some BB_s)
      (LOOP_INVS: (cdhp_s ! ep = None /\ loop_invs = nil) \/
                  (exists BB', cdhp_s ! ep = Some BB' /\ loop_invC lo (cdhp_s, ep) = loop_invs))
      (WF_MAX_P: forall l BB, cdhp_s ! l = Some BB -> (l < max_p)%positive):
  BB_t = BB_s \/ ptB_ph_rel BB_t BB_s preheader.
Proof.
  des1.

  des1. subst; ss. inv TRANSC'; eauto. rewrite BLK_TGT in BLK_SRC. inv BLK_SRC; eauto.

  do 2 des1. subst. clear LOOP_INVS.
  lets TRANSC2': TRANSC'.
  eapply well_defined_preheader2' in TRANSC'; eauto.
  {
    des1.
    {
      des1. exploit WF_MAX_P; eauto. i.
      eapply TransC'_new_allocated_prop in TRANSC2'; eauto.
      des1. rewrite PTree.gempty in TRANSC2'. ss.
      eapply Pos.lt_nle in H. eapply H in TRANSC2'. tryfalse.
    }
    {
      do 2 des1. rewrite BLK_SRC in TRANSC'. inv TRANSC'. eauto.
    }
  }
  {
    ii. rewrite PTree.gempty in H. ss.
  }
  {
    ii. rewrite PTree.gempty in H; ss.
  }
  {
    ii; eauto. subst.
    exploit wf_loop_invC1; eauto.
    ii; des; eauto.
  }
Qed.
  
Lemma transC_prop
      cdhp_s l_s cdhp_t l_t lo BB_t loop_invs
      (TRANSC: TransC (cdhp_s, l_s) loop_invs = (cdhp_t, l_t))
      (LOOP_INVS: (cdhp_s ! l_s = None /\ loop_invs = nil) \/
                  (exists BB', cdhp_s ! l_s = Some BB' /\ loop_invC lo (cdhp_s, l_s) = loop_invs))
      (GET_BB_T: cdhp_t ! l_t = Some BB_t):
  exists BB_s preheader max_p max_p',
    <<GET_BB_S: cdhp_s ! l_s = Some BB_s>> /\ 
    <<TRANSC': TransC' cdhp_s (PTree.empty positive) (loop_invC lo (cdhp_s, l_s))
                       (loop_invC lo (cdhp_s, l_s)) max_p = (cdhp_t, max_p', preheader)>> /\
    <<MAX_P: forall l BB, cdhp_s ! l = Some BB -> (l < max_p)%positive>> /\      
    <<BLK_REL: ((BB_t = BB_s \/ ptB_ph_rel BB_t BB_s preheader) /\ preheader ! l_s = None) \/
               (wdph BB_t l_s cdhp_s lo /\ preheader ! l_s = Some l_t)>>.
Proof.
  des.
  subst. simpl in TRANSC.
  assert ((PTree.empty positive) ! l_s = None).
  {
    rewrite PTree.gempty. eauto.
  }
  rewrite H in TRANSC. inv TRANSC. tryfalse.
  
  subst. unfold TransC in *.
  destruct (TransC' cdhp_s (PTree.empty positive) (loop_invC lo (cdhp_s, l_s)) (loop_invC lo (cdhp_s, l_s))
                    (Pos.succ (max_labelled_node (PTree.elements cdhp_s) 1))) eqn:TRANSC'.
  destruct p as (cdhp_t', max_p). renames t to preheader.
  assert (ALLOC_NEW: forall l BB,
             cdhp_s ! l = Some BB ->
             (l < Pos.succ (max_labelled_node (PTree.elements cdhp_s) 1))%positive).
  { 
    ii. exploit PTree.elements_remove; eauto. i. des. clear H1.
    assert (IN: In (l, BB) (PTree.elements cdhp_s)).
    {
      rewrite H0. eapply in_or_app. ss; eauto.
    }
    eapply max_lablled_node_prop in IN.
    instantiate (1 := 1%positive) in IN.
    assert (SUCC_LT: ((max_labelled_node (PTree.elements cdhp_s) 1) <
                      Pos.succ (max_labelled_node (PTree.elements cdhp_s) 1))%positive).
    {
      eapply Pos.lt_succ_diag_r; eauto.
    }
    eapply Pos.le_lt_trans; eauto.
  }
  destruct (preheader ! l_s) eqn:PREHEADER.
  - inv TRANSC.
    exploit well_defined_preheader; eauto.
    i. do 3 des1.
    do 4 eexists.
    splits; eauto.
  - inv TRANSC.
    lets TRANSC2': TRANSC'.
    eapply well_defined_preheader2' in TRANSC'; eauto.
    {
      des1.
      {
        des1. exploit ALLOC_NEW; eauto. i.
        eapply TransC'_new_allocated_prop in TRANSC2'; eauto.
        des1. rewrite PTree.gempty in TRANSC2'. ss.
        eapply Pos.lt_nle in H. eapply H in TRANSC2'. tryfalse.
      }
      {
        do 2 des1.
        do 4 eexists. splits; eauto.
      }
    }
    {
      ii. rewrite PTree.gempty in H. ss.
    }
    {
      ii. rewrite PTree.gempty in H. ss.
    }
    {
      ii; eauto.
      exploit wf_loop_invC1; eauto.
      ii; des; eauto.
    }
Qed.

Lemma BBlock_cons
      BB_t BB_s c preheader
      (BLK_CONS: BB_t = c ## BB_s \/ ptB_ph_rel BB_t (c ## BB_s) preheader):
  exists BB_t', BB_t = c ## BB_t' /\
           (BB_t' = BB_s \/ ptB_ph_rel BB_t' BB_s preheader).
Proof.
  des1. subst. exists BB_s. eauto.
  inv BLK_CONS. exists BB_t0. eauto.
Qed.

Lemma BBlock_cons'
      BB_t BB_s c preheader
      (BLK_CONS: c ## BB_t = BB_s \/ ptB_ph_rel (c ## BB_t) BB_s preheader):
  exists BB_s', BB_s = c ## BB_s' /\
           (BB_s' = BB_t \/ ptB_ph_rel BB_t BB_s' preheader).
Proof.
  des1. subst. exists BB_t. split; eauto.
  inv BLK_CONS. eauto.
Qed. 

Lemma wdph_implies_progress
      BB l_entry cdhp_s cdhp_t lo BB' R_t cont_t prog_t
      (WDPH: wdph BB l_entry cdhp_s lo)
      (GET: cdhp_t ! l_entry = Some BB'):
  exists e st2,
    State.step e {| State.regs := R_t; State.blk := BB;
                    State.cdhp := cdhp_t; State.cont := cont_t; State.code := prog_t |} st2.
Proof.
  destruct BB; ss.
  - des_ifH WDPH; subst; ss.
    do 2 eexists. eapply State.step_jmp; eauto.
  - destruct c; ss. des.
    do 2 eexists. eapply State.step_assign; eauto.
    destruct or; ss.
    do 2 eexists. eapply State.step_load; eauto.
    Unshelve. exact Int.zero.
Qed.
