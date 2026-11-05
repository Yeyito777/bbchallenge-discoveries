Require Import Lia.
Require Import ZArith.

From BBminus2x4 Require Import TM.
From BBminus2x4 Require Import BBminus2x4_Statement.
From BBminus2x4 Require Import BB2x4_Encodings.
From BBminus2x4 Require Import Deciders_Common.
From BBminus2x4 Require Import Decider_Halt.

Set Warnings "-abstract-large-number".

(** Runs a machine up to 1,845,977 steps from the start tape and reports halting. *)
Definition halt_decider_max := halt_decider 1845977.
Lemma halt_decider_max_spec: HaltDecider_WF (N.to_nat BBinit_minus_one) halt_decider_max.
Proof.
  eapply halt_decider_WF.
  unfold BBinit_minus_one.
  replace (S (N.to_nat 1845976)) with (N.to_nat 1845977) by lia.
  replace 1845977 with (N.to_nat 1845977).
  1: apply Nat.le_refl.
  symmetry.
  apply nat_eqb_N_spec.
  vm_compute.
  reflexivity.
Qed.
