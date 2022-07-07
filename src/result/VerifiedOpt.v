Require Import sflib.  

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.
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
Require Import ww_RF.
Require Import Behavior.
Require Import LocalSim.

Require Import CorrectOpt.
Require Import ConstProp.
Require Import ConstPropProof.
Require Import CSE.
Require Import CSEProof.
Require Import DCE.
Require Import DCEProof.
Require Import LICM.
Require Import LICMProof.

(** * Correct ConstProp, CSE, DCE and LICM  *)
Theorem Correct_optimizers:
  Correct(constprop_optimizer) /\ Correct(cse_optimizer) /\
  Correct(dce_optimizer) /\ Correct (licm).
Proof.
  splits.
  eapply correct_constprop.
  eapply correct_cse.
  eapply correct_dce.
  eapply correct_licm.
Qed.

