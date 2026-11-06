(** The statement: the holdout 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA halts from the blank tape, in exactly N steps,
    given a certificate that passes [cert_ok]. [cert_ok] is a pure function, proved sound in the files this one imports. *)
From Coq Require Import ZArith Lia List.
From BusyCoq Require Import Individual62.
From BB6 Require Import Rules Map Num Big Vec Cert Halts Totals.
Local Open Scope Z_scope.

(** Rules.v: [tm := TM_from_str "1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA"].
    TM.v (busycoq): [halts_in tm c0 n]: from the blank tape, n steps reach a configuration whose (state, symbol) has no transition. *)

(** Halt form: A(a, a+3) with a = 28 * 2^85 - 6. *)
Definition a_halt : Z := 1083197534374707740536733690.
(** Rule applications from A(6,1) to the halt form. *)
Definition n_apps : Z := 674564771793355691986675473.
(** Steps from the blank tape to the halting configuration, not counting the undefined transition. *)
Definition n_steps : nat := Z.to_nat 6448902863343978619509980365051027907909194602118636181048891434378153619188133.
(** The cost total, which determines [n_steps], as five limbs mod 2^315. *)
Definition R_total : Z := 38693417180063871717059872803770979643885910167836334283316455175709787324184634.

Lemma R_limbs_ok : cong PM (vval R_limbs) R_total.
Proof. exists 0. vm_compute. reflexivity. Qed.

Theorem bb6_holdout_halts l f : cert_ok l f = true -> halts tm c0.
Proof. apply cert_halts. Qed.

Theorem bb6_holdout_steps l f :
  cert_ok l f = true ->
  val (fa f) = a_halt ->
  sum_apps l + val (fapps f) = n_apps ->
  veqb (vplus (sum_acc l) (facc f)) R_limbs = true ->
  halts_in tm c0 n_steps.
Proof.
  intros H Ha Hn Hr. apply veqb_eq in Hr.
  eapply cert_steps with (Rc := R_total); [exact H| | | |].
  - rewrite Hr. apply R_limbs_ok.
  - vm_compute. reflexivity.
  - rewrite Ha. unfold n_steps. rewrite Z2Nat.id by (vm_compute; discriminate). vm_compute. reflexivity.
  - cbv zeta. rewrite Hn. vm_compute. reflexivity.
Qed.
