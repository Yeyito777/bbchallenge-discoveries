(** Entry point: proves the statements of `BBminus2x4_Statement.v`. *)
Require Import ZArith.
Require Import Lia.

From BBminus2x4 Require Import Prelims.
From BBminus2x4 Require Import BBminus2x4_Statement.
From BBminus2x4 Require Import TNF_Common.
From BBminus2x4 Require Import TNF_Enumeration.
From BBminus2x4 Require Import BB2x4_Encodings.
From BBminus2x4 Require Import TM.
From BBminus2x4 Require Import List_Tape.
From BBminus2x4 Require Import BB2x4_Make_TM.
From BBminus2x4 Require Import Tactics.
From BBminus2x4 Require Import Deciders.Verifier_Halt.

(** `2LA2LB0RB---_1RA3RB0RA1LB`: halts from `110[1]011` after 1,845,977 steps. *)
Definition BBinit2x4_StartTape_champion := (makeTM AL2 BL2 BR0 HR1 AR1 BR3 AR0 BL1).

(** `1RB2LA1RA1RA_1LB1LA3RB---`: the BB(2,4) champion, halts from the blank tape after 3,932,964 steps. *)
Definition BB2x4_champion := (makeTM BR1 AL2 AR1 AR1 BL1 AL1 BR3 HR1).

Lemma HaltsAt_PlusOne tm n st:
  HaltsAt Σ tm n st -> HaltsAtPlusOne Σ tm (S n) st.
Proof.
  intro H. ctor. apply H.
Qed.

Lemma BBinit2x4_StartTape_lower_bound:
  HaltsAtPlusOne Σ BBinit2x4_StartTape_champion (N.to_nat BBinit2x4_StartTape) StartES.
Proof.
  replace (N.to_nat BBinit2x4_StartTape) with (S (N.to_nat BBinit_minus_one)) by (unfold BBinit_minus_one,BBinit2x4_StartTape; lia).
  apply HaltsAt_PlusOne.
  rewrite <-ListES_toES_Start.
  apply halt_time_verifier_spec.
  vm_compute.
  reflexivity.
Qed.

Lemma BB2x4_champion_halts:
  HaltsAtPlusOne Σ BB2x4_champion (N.to_nat BB2x4) (InitES Σ Σ0).
Proof.
  replace (N.to_nat BB2x4) with (S (N.to_nat 3932963)) by (unfold BB2x4; lia).
  apply HaltsAt_PlusOne.
  rewrite <-ListES_toES_O.
  apply halt_time_verifier_spec.
  vm_compute.
  reflexivity.
Qed.

Lemma BBinit2x4_StartTape_upper_bound tm n0:
  HaltsAtPlusOne Σ tm n0 StartES -> n0 <= N.to_nat BBinit2x4_StartTape.
Proof.
  intro H.
  invst H.
  epose proof (allTM_HTUB _ _ _ H0) as H1.
  Unshelve. 2: cbn; trivial.
  unfold BB,BBinit_minus_one in H1.
  unfold BBinit2x4_StartTape.
  lia.
Qed.

Theorem BBinit2x4_StartTape_value:
  BBinit2x4_StartTape_statement.
Proof.
  split.
  - apply BBinit2x4_StartTape_upper_bound.
  - exists BBinit2x4_StartTape_champion.
    apply BBinit2x4_StartTape_lower_bound.
Qed.

Theorem BBminus2x4_lt_BB2x4:
  BBminus2x4_lt_BB2x4_statement.
Proof.
  exists StartTape.
  split. 2: split.
  - apply BBinit2x4_StartTape_upper_bound.
  - exists BB2x4_champion.
    apply BB2x4_champion_halts.
  - unfold BBinit2x4_StartTape,BB2x4. lia.
Qed.

Print Assumptions BBinit2x4_StartTape_value.
Print Assumptions BBminus2x4_lt_BB2x4.
