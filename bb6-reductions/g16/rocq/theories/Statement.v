(** The 16-machine group: statement.

    For each of the 16 machines, from the blank tape:

    - [g16_NN]: the machine halts iff some stack of the orbit has a top event with P + 2 = 2^k.
    - [g16_map_NN]: until such a stack, the machine passes through the tape of every stack of the orbit, in order.

    The map is in [Spec]: [orbit n] iterates [step] from [s0 = [9;10]], [topP s] is the P of the top event of a
    step from [s], if it has one, and [hit s] says P + 2 is a power of 2. Nothing in [Spec] mentions a machine.
    The tape of stack [s] is [Cc a c s] in [Tape]: head in state [a] on a blank to the right of
    1^c 0 1^4 0 1^6 0 1^s1 0 1^s2 ..., with c = 1 or 2 by family.
    Four machines (03, 04, 05, 14) are stated mirrored in [g16_map_NN], since their tapes run the other way; [g16_NN] is always
    about the literal machine. *)
From Coq Require Import List String.
Local Open Scope string_scope.
From BusyCoq Require Import Individual62.
From G16 Require Import Spec Tape.
From G16 Require M01 M02 M03 M04 M05 M06 M07 M08 M09 M10 M11 M12 M13 M14 M15 M16.

(** 1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF *)
Theorem g16_01 : halts (TM_from_str "1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF") c0 <-> exists n, hit (orbit n).
Proof. exact M01.main_M01. Qed.
Theorem g16_map_01 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF") ]->+ Cc C 1 (orbit n).
Proof. exact (M01.map_M01 n). Qed.

(** 1RB1RC_1LA0LE_1RD1RC_1LB0RA_---0LF_1RD1LF *)
Theorem g16_02 : halts (TM_from_str "1RB1RC_1LA0LE_1RD1RC_1LB0RA_---0LF_1RD1LF") c0 <-> exists n, hit (orbit n).
Proof. exact M02.main_M02. Qed.
Theorem g16_map_02 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB1RC_1LA0LE_1RD1RC_1LB0RA_---0LF_1RD1LF") ]->+ Cc C 1 (orbit n).
Proof. exact (M02.map_M02 n). Qed.

(** 1RB0LC_1LC0RE_0LA1LD_1LA1LD_---0RF_1LA1RF *)
Theorem g16_03 : halts (TM_from_str "1RB0LC_1LC0RE_0LA1LD_1LA1LD_---0RF_1LA1RF") c0 <-> exists n, hit (orbit n).
Proof. exact M03.main_M03. Qed.
Theorem g16_map_03 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (mirror (TM_from_str "1RB0LC_1LC0RE_0LA1LD_1LA1LD_---0RF_1LA1RF")) ]->+ Cc D 1 (orbit n).
Proof. exact (M03.map_M03 n). Qed.

(** 1RB0LF_1LC0RD_1LA1LC_---0RE_1LA1RE_0LA1LC *)
Theorem g16_04 : halts (TM_from_str "1RB0LF_1LC0RD_1LA1LC_---0RE_1LA1RE_0LA1LC") c0 <-> exists n, hit (orbit n).
Proof. exact M04.main_M04. Qed.
Theorem g16_map_04 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (mirror (TM_from_str "1RB0LF_1LC0RD_1LA1LC_---0RE_1LA1RE_0LA1LC")) ]->+ Cc C 1 (orbit n).
Proof. exact (M04.map_M04 n). Qed.

(** 1RB0LF_1LC0RD_1LA1LC_---0RE_1LA1RE_1LB1LC *)
Theorem g16_05 : halts (TM_from_str "1RB0LF_1LC0RD_1LA1LC_---0RE_1LA1RE_1LB1LC") c0 <-> exists n, hit (orbit n).
Proof. exact M05.main_M05. Qed.
Theorem g16_map_05 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (mirror (TM_from_str "1RB0LF_1LC0RD_1LA1LC_---0RE_1LA1RE_1LB1LC")) ]->+ Cc C 1 (orbit n).
Proof. exact (M05.map_M05 n). Qed.

(** 1RB1RC_1RC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF *)
Theorem g16_06 : halts (TM_from_str "1RB1RC_1RC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF") c0 <-> exists n, hit (orbit n).
Proof. exact M06.main_M06. Qed.
Theorem g16_map_06 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB1RC_1RC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF") ]->+ Cc C 1 (orbit n).
Proof. exact (M06.map_M06 n). Qed.

(** 1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF *)
Theorem g16_07 : halts (TM_from_str "1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF") c0 <-> exists n, hit (orbit n).
Proof. exact M07.main_M07. Qed.
Theorem g16_map_07 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF") ]->+ Cc A 1 (orbit n).
Proof. exact (M07.map_M07 n). Qed.

(** 1RB---_0RC1RB_1LC1RD_1RA0LE_1RB0LF_0RD1LF *)
Theorem g16_08 : halts (TM_from_str "1RB---_0RC1RB_1LC1RD_1RA0LE_1RB0LF_0RD1LF") c0 <-> exists n, hit (orbit n).
Proof. exact M08.main_M08. Qed.
Theorem g16_map_08 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB---_0RC1RB_1LC1RD_1RA0LE_1RB0LF_0RD1LF") ]->+ Cc B 2 (orbit n).
Proof. exact (M08.map_M08 n). Qed.

(** 1RB0LE_1RC---_1RD1RC_1LA0RA_0RB0LF_1RD1LF *)
Theorem g16_09 : halts (TM_from_str "1RB0LE_1RC---_1RD1RC_1LA0RA_0RB0LF_1RD1LF") c0 <-> exists n, hit (orbit n).
Proof. exact M09.main_M09. Qed.
Theorem g16_map_09 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB0LE_1RC---_1RD1RC_1LA0RA_0RB0LF_1RD1LF") ]->+ Cc C 1 (orbit n).
Proof. exact (M09.map_M09 n). Qed.

(** 1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1LB--- *)
Theorem g16_10 : halts (TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1LB---") c0 <-> exists n, hit (orbit n).
Proof. exact M10.main_M10. Qed.
Theorem g16_map_10 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1LB---") ]->+ Cc B 2 (orbit n).
Proof. exact (M10.map_M10 n). Qed.

(** 1RB1LA_1LC0RC_1RE0LD_0RE0LA_1RF---_1RB1RF *)
Theorem g16_11 : halts (TM_from_str "1RB1LA_1LC0RC_1RE0LD_0RE0LA_1RF---_1RB1RF") c0 <-> exists n, hit (orbit n).
Proof. exact M11.main_M11. Qed.
Theorem g16_map_11 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB1LA_1LC0RC_1RE0LD_0RE0LA_1RF---_1RB1RF") ]->+ Cc F 1 (orbit n).
Proof. exact (M11.map_M11 n). Qed.

(** 1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1RB--- *)
Theorem g16_12 : halts (TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1RB---") c0 <-> exists n, hit (orbit n).
Proof. exact M12.main_M12. Qed.
Theorem g16_map_12 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1RB---") ]->+ Cc B 2 (orbit n).
Proof. exact (M12.map_M12 n). Qed.

(** 1RB0LE_0RC1RB_1LC1RD_0RF0LA_0RD1LE_1LA--- *)
Theorem g16_13 : halts (TM_from_str "1RB0LE_0RC1RB_1LC1RD_0RF0LA_0RD1LE_1LA---") c0 <-> exists n, hit (orbit n).
Proof. exact M13.main_M13. Qed.
Theorem g16_map_13 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB0LE_0RC1RB_1LC1RD_0RF0LA_0RD1LE_1LA---") ]->+ Cc B 2 (orbit n).
Proof. exact (M13.map_M13 n). Qed.

(** 1RB---_0LC1LB_1RC1LD_1LA0RE_1LB0RF_0LD1RF *)
Theorem g16_14 : halts (TM_from_str "1RB---_0LC1LB_1RC1LD_1LA0RE_1LB0RF_0LD1RF") c0 <-> exists n, hit (orbit n).
Proof. exact M14.main_M14. Qed.
Theorem g16_map_14 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (mirror (TM_from_str "1RB---_0LC1LB_1RC1LD_1LA0RE_1LB0RF_0LD1RF")) ]->+ Cc B 2 (orbit n).
Proof. exact (M14.map_M14 n). Qed.

(** 1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF *)
Theorem g16_15 : halts (TM_from_str "1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF") c0 <-> exists n, hit (orbit n).
Proof. exact M15.main_M15. Qed.
Theorem g16_map_15 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF") ]->+ Cc D 2 (orbit n).
Proof. exact (M15.map_M15 n). Qed.

(** 1RB0LB_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF *)
Theorem g16_16 : halts (TM_from_str "1RB0LB_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF") c0 <-> exists n, hit (orbit n).
Proof. exact M16.main_M16. Qed.
Theorem g16_map_16 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "1RB0LB_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF") ]->+ Cc D 2 (orbit n).
Proof. exact (M16.map_M16 n). Qed.
