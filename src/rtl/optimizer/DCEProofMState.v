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
Require Import LiveAnalysis.
Require Import CorrectOpt.
Require Import DCE.

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

(** * Invariant in dead code elimination  *)
Definition I_dce (lo: Ordering.LocOrdMap) (inj: Mapping) (S: Rss) :=
  match S with
  | Build_Rss sc_tgt mem_tgt sc_src mem_src =>
    (* injection timemaps for SC fence *)
    (<<INJ_SC: TMapInj inj sc_tgt sc_src>> /\
    (* memory injection *)
    <<INJ_MEM: MsgInj inj mem_tgt mem_src>> /\
    (* timestamps reservation *)
    <<TS_RSV: forall loc val from' to' R' to,
        Memory.get loc to' mem_src = Some (from', Message.concrete val R') ->
        inj loc to = Some to' ->
        Time.lt Time.bot to ->
        lo loc = Ordering.nonatomic ->
        exists to_r, Time.lt to_r from' /\
                (forall ts, Interval.mem (to_r, from') ts -> ~Cover.covered loc ts mem_src)>> /\
    (* no atomic location has no reservation *)
    <<NO_RSVs: forall loc to from,
            Memory.get loc to mem_src = Some (from, Message.reserve) -> lo loc = Ordering.atomic>> /\           
    (* identity atomic *)                                                                                            
    <<ID_ATOMIC: forall loc to to', lo loc = Ordering.atomic -> inj loc to = Some to' -> to = to'>> /\
    (* closed src memory *)
    <<CLOSED_SRC_MEM: Memory.closed mem_src>>
    )
  end. 

(** * Match state *)
(* timestamp match *)
Definition TM (inj: Mapping) (loc: Loc.t) (tm_tgt: TimeMap.t)
           (tm_src: TimeMap.t) (mem_src: Memory.t) :=
  (forall to to', inj loc to = Some to' -> Time.lt (tm_tgt loc) to -> Time.lt (tm_src loc) to') /\
  (exists to', inj loc (tm_tgt loc) = Some to' /\ Time.le to' (tm_src loc) /\
          (forall ts, Interval.mem (to', tm_src loc) ts -> concrete_covered loc ts mem_src)).

(* view match *) 
Inductive InvView_dce: Mapping -> Ordering.LocOrdMap -> TView.t -> TView.t -> Memory.t -> Prop :=
| InvView_dce_intro
    inj lo tview_tgt tview_src mem_src
    (* For current view *)
    (ATM_LOC_CUR_PLN: 
       forall loc, lo loc = Ordering.atomic ->
              inj loc ((View.pln (TView.cur tview_tgt)) loc) = Some ((View.pln (TView.cur tview_src)) loc))
    (ATM_LOC_CUR_RLX: 
       forall loc, lo loc = Ordering.atomic ->
              inj loc ((View.rlx (TView.cur tview_tgt)) loc) = Some ((View.rlx (TView.cur tview_src)) loc))
    (NA_LOC_CUR_RLX: 
       forall loc, lo loc = Ordering.nonatomic ->
              TM inj loc (View.rlx (TView.cur tview_tgt)) (View.rlx (TView.cur tview_src)) mem_src)
    (* For acquire view *)
    (ATM_LOC_ACQ_PLN: 
       forall loc, lo loc = Ordering.atomic ->
              inj loc ((View.pln (TView.acq tview_tgt)) loc) = Some ((View.pln (TView.acq tview_src)) loc))
    (ATM_LOC_ACQ_RLX: 
       forall loc, lo loc = Ordering.atomic ->
              inj loc ((View.rlx (TView.acq tview_tgt)) loc) = Some ((View.rlx (TView.acq tview_src)) loc))
    (NA_LOC_CUR_RLX: 
       forall loc, lo loc = Ordering.nonatomic ->
              TM inj loc (View.rlx (TView.acq tview_tgt)) (View.rlx (TView.acq tview_src)) mem_src)
    (* For release view *)
    (ATM_LOC_REL: 
       forall loc, lo loc = Ordering.atomic ->
              ViewInj inj ((TView.rel tview_tgt) loc) ((TView.rel tview_src) loc)):
    InvView_dce inj lo tview_tgt tview_src mem_src.

Definition cur_acq (lo: Ordering.LocOrdMap) (inj: Mapping)
           (cur_tgt acq_tgt: View.t) (cur_src acq_src: View.t) :=
  forall loc 
    (NA_LOC: lo loc = Ordering.nonatomic),
    <<LT: Time.lt ((View.rlx cur_tgt) loc) ((View.rlx acq_tgt) loc) /\
          inj loc ((View.rlx acq_tgt) loc) = Some ((View.rlx acq_src) loc)>> \/
    <<EQ: ((View.rlx cur_tgt) loc) = ((View.rlx acq_tgt) loc) /\
          ((View.rlx cur_src) loc) = ((View.rlx acq_src) loc)>>.

Definition cur_acq_pln (lo: Ordering.LocOrdMap) (inj: Mapping)
           (cur_tgt acq_tgt: View.t) (cur_src acq_src: View.t) :=
  forall loc 
    (NA_LOC: lo loc = Ordering.nonatomic),
    <<LT: Time.lt ((View.rlx cur_tgt) loc) ((View.pln acq_tgt) loc) /\
          inj loc ((View.pln acq_tgt) loc) = Some ((View.pln acq_src) loc)>> \/
    <<EQ: Time.le ((View.pln acq_tgt) loc) ((View.rlx cur_tgt) loc) /\
          Time.le ((View.pln acq_src) loc) ((View.rlx cur_src) loc)>>.
    
(* semantics for abstract interpretation *)
Definition sem_live_reg (R_tgt R_src: RegFile.t) (nr: nreg): Prop :=
  forall r, NREG.get r nr = true -> RegFun.find r R_tgt = RegFun.find r R_src.

Definition sem_live_loc (inj: Mapping) (tview_tgt tview_src: TView.t) (nm: nmem): Prop :=
  forall loc, negb (is_dead_loc loc nm) ->
         (
           (inj loc ((View.pln (TView.cur tview_tgt)) loc) = Some ((View.pln (TView.cur tview_src)) loc)) /\
           (inj loc ((View.pln (TView.acq tview_tgt)) loc) = Some ((View.pln (TView.acq tview_src)) loc)) /\
           (inj loc ((View.rlx (TView.cur tview_tgt)) loc) = Some ((View.rlx (TView.cur tview_src)) loc)) /\
           (inj loc ((View.rlx (TView.acq tview_tgt)) loc) = Some ((View.rlx (TView.acq tview_src)) loc))
         ). 

Definition ai_interp (inj: Mapping)
           (R_tgt: RegFile.t) (tview_tgt: TView.t)
           (R_src: RegFile.t) (tview_src: TView.t)
           (ai: LvDS.L.t): Prop :=
  match ai with
  | (nr, nm) => sem_live_reg R_tgt R_src nr /\ sem_live_loc inj tview_tgt tview_src nm
  end.

(* promise relation *)
Definition promises_relation (inj: Mapping) (lo: Ordering.LocOrdMap) (prm_tgt prm_src: Memory.t) :=
  @rel_promises nat inj dset_init prm_tgt prm_src /\
  (forall loc from to,
      lo loc = Ordering.atomic -> 
      (Memory.get loc to prm_tgt = Some (from, Message.reserve) <->
       Memory.get loc to prm_src = Some (from, Message.reserve))).

(* match state for current stack frame *)
Inductive match_state_cur_stkframe:
  Mapping -> Ordering.LocOrdMap ->
  (RegFile.t * BBlock.t * CodeHeap * TView.t) ->
  (RegFile.t * BBlock.t * CodeHeap * TView.t) -> Prop :=
| match_state_cur_stkframe_intro
    inj lo R_tgt BB_tgt C_tgt tview_tgt R_src BB_src C_src tview_src
    afunc ai_tail ai ai_pblk fid
    (* function analysis *)
    (FUNC_ANALYSIS: LvDS.analyze_func_backward (C_src, fid) succ transf_blk = Some afunc)
    (* transformation code heap *)
    (FUNC_TRANS: transform_cdhp C_src afunc = C_tgt)
    (* analysis for the current source block *)
    (AI_FOR_CBLK: transf_blk ai_tail BB_src = LvDS.AI.Cons ai ai_pblk)
    (* current source and target blocks transformation *)
    (TRANS_PBLK: transform_blk' ai_pblk BB_src = BB_tgt)
    (* current ai interpretation *)
    (AI_INTERP: ai_interp inj R_tgt tview_tgt R_src tview_src ai)
    (* link *)
    (LINK: forall s BB_src',
        In s (succ BB_src) -> C_src ! s = Some BB_src' ->
        LvDS.L.ge ai_tail (LvDS.AI.getFirst (transf_blk (LvDS.AI.getLast (afunc !! s)) BB_src'))):
    match_state_cur_stkframe inj lo
                             (R_tgt, BB_tgt, C_tgt, tview_tgt)
                             (R_src, BB_src, C_src, tview_src).

(* match state for stack frames *) 
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
       forall tview_tgt tview_src inj', 
         sem_live_loc inj' tview_tgt tview_src (NMem LocSet.empty) ->
         match_state_cur_stkframe inj' lo
                                  (R_tgt, BB_tgt, C_tgt, tview_tgt)
                                  (R_src, BB_src, C_src, tview_src)
    )
    (CONT_MATCH: match_state_stkframes lo cont_tgt cont_src):
    match_state_stkframes lo
                          (Continuation.stack R_tgt BB_tgt C_tgt cont_tgt)
                          (Continuation.stack R_src BB_src C_src cont_src).

Lemma match_state_call_stack
      inj lo fid ai_tail ai_pblk nr afunc
      R_tgt BB_tgt C_tgt tview_tgt
      R_src BB_src C_src tview_src
      (FUNC_ANALYSIS: LvDS.analyze_func_backward (C_src, fid) succ transf_blk = Some afunc)
      (FUNC_TRANS: transform_cdhp C_src afunc = C_tgt)
      (AI_FOR_CBLK: transf_blk ai_tail BB_src = LvDS.AI.Cons (nr, NMem LocSet.empty) ai_pblk)
      (TRANS_PBLK: transform_blk' ai_pblk BB_src = BB_tgt)
      (LV_REG: sem_live_reg R_tgt R_src nr)
      (LV_LOC: sem_live_loc inj tview_tgt tview_src (NMem LocSet.empty))
      (LINK: forall s BB_src',
          In s (succ BB_src) -> C_src ! s = Some BB_src' ->
          LvDS.L.ge ai_tail (LvDS.AI.getFirst (transf_blk (LvDS.AI.getLast (afunc !! s)) BB_src'))):
  match_state_cur_stkframe inj lo
                           (R_tgt, BB_tgt, C_tgt, tview_tgt)
                           (R_src, BB_src, C_src, tview_src).
Proof.
  econs; eauto.
  unfold ai_interp.
  split; eauto.
Qed.

(* match state for the thread-local state *)
Inductive match_state_tlocal:
  Mapping -> Ordering.LocOrdMap ->
  (State.t * TView.t * Memory.t) -> (State.t * TView.t * Memory.t) -> Prop :=
| match_state_tlocal_intro
    inj lo
    R_tgt BB_tgt C_tgt cont_tgt Prog_tgt tview_tgt prm_tgt
    R_src BB_src C_src cont_src Prog_src tview_src prm_src
    (PROG_TRANS: transform_prog Prog_src = Some Prog_tgt)
    (CUR_STK_FRAME: match_state_cur_stkframe inj lo
                                             (R_tgt, BB_tgt, C_tgt, tview_tgt)
                                             (R_src, BB_src, C_src, tview_src))
    (STK_FRAMES: match_state_stkframes lo cont_tgt cont_src):
    match_state_tlocal inj lo
                       (State.mk R_tgt BB_tgt C_tgt cont_tgt Prog_tgt, tview_tgt, prm_tgt)
                       (State.mk R_src BB_src C_src cont_src Prog_src, tview_src, prm_src).

(* match state for thread state *)
Inductive match_state_dce:
  Mapping -> Ordering.LocOrdMap -> bool ->
  Thread.t rtl_lang -> Thread.t rtl_lang -> Prop :=
| match_state_dce_intro
    inj inj' lo b
    state_tgt tview_tgt prm_tgt sc_tgt mem_tgt
    state_src tview_src prm_src sc_src mem_src
    (INV: I_dce lo inj' (Build_Rss sc_tgt mem_tgt sc_src mem_src))
    (ATOM_MEM_EQ: Mem_at_eq lo mem_tgt mem_src)
    (MATCH_THRD_LOCAL: 
       match_state_tlocal inj' lo (state_tgt, tview_tgt, prm_tgt) (state_src, tview_src, prm_src))
    (VIEW_MATCH: InvView_dce inj' lo tview_tgt tview_src mem_src)
    (CUR_ACQ: cur_acq lo inj' (TView.cur tview_tgt) (TView.acq tview_tgt)
                      (TView.cur tview_src) (TView.acq tview_src))
    (CUR_ACQ_PLN: cur_acq_pln lo inj' (TView.cur tview_tgt) (TView.acq tview_tgt)
                              (TView.cur tview_src) (TView.acq tview_src))
    (* promise injection *)
    (PROM_INJ: promises_relation inj lo prm_tgt prm_src)
    (ATM_BIT: (b = false /\ (forall loc t t', inj loc t = Some t' -> inj' loc t = Some t')) \/
              (b = true /\ inj = inj'))
    (* wf local, closed sc, closed memory *)
    (LOCAL_WF_TGT: Local.wf (Local.mk tview_tgt prm_tgt) mem_tgt)
    (CLOSED_SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
    (MEM_CLOSED_TGT: Memory.closed mem_tgt)
    (LOCAL_WF_SRC: Local.wf (Local.mk tview_src prm_src) mem_src)
    (CLOSED_SC_SRC: Memory.closed_timemap sc_src mem_src):
    (*(MEM_CLOSED_SRC: Memory.closed mem_src):*)
  match_state_dce inj lo b
                  (Thread.mk rtl_lang state_tgt (Local.mk tview_tgt prm_tgt) sc_tgt mem_tgt)
                  (Thread.mk rtl_lang state_src (Local.mk tview_src prm_src) sc_src mem_src).

Lemma promise_consistent_prsv
      inj lo
      tview_tgt prm_tgt tview_src prm_src mem_src
      (VIEW_MATCH: InvView_dce inj lo tview_tgt tview_src mem_src)
      (PROM_REL: promises_relation inj lo prm_tgt prm_src)
      (PROM_CONS: Local.promise_consistent (Local.mk tview_tgt prm_tgt))
      (MON_INJ: monotonic_inj inj):
  Local.promise_consistent (Local.mk tview_src prm_src).
Proof.
  unfold Local.promise_consistent in *; ii; ss.
  unfold promises_relation in PROM_REL. des. clear PROM_REL0.
  inv PROM_REL.
  exploit COMPLETE; eauto. ii; des.
  rewrite dset_gempty in x0. ss.
  exploit PROM_CONS; eauto. ii.
  clear - VIEW_MATCH x x0 x1 MON_INJ.
  inv VIEW_MATCH.
  destruct (lo loc) eqn:Heqe.
  exploit ATM_LOC_CUR_RLX; eauto.
  exploit NA_LOC_CUR_RLX; eauto.
  introv TM_H. inv TM_H; ss. eauto.
Qed.
