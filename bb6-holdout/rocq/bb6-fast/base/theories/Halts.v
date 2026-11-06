(** From a passing certificate to the halt of the machine, with the exact step count. *)
From Coq Require Import ZArith Lia List.
From BusyCoq Require Import Individual62.
From BB6 Require Import Rules Map Num Big Vec Cert.
Local Open Scope Z_scope.

(** What a passing certificate proves. *)
Theorem cert_halts l f : cert_ok l f = true -> halts tm c0.
Proof.
  intros H. destruct (cert_reach l f H) as (R & HR & _).
  destruct (halts_of_Reach _ _ _ HR) as (st & Hst & _). exists st. exact Hst.
Qed.

Definition steps6 (a R : Z) : Z := 6 * 35 + 2 * (a * a - 36) + R + 6 * (a * a + 7 * a + 41).

(** With the exact count: [Rc] is the cost total, read off the certificate's modular sum. *)
Theorem cert_steps l f Rc N : cert_ok l f = true ->
  cong PM (vval (vplus (sum_acc l) (facc f))) Rc -> Z.abs Rc * 2 < PM ->
  Z.of_nat N * 6 = steps6 (val (fa f)) Rc ->
  let n := sum_apps l + val (fapps f) in
  n * (9 * ((7 + 20 * n + 40) * (7 + 20 * n + 40))) * 2 < PM ->
  halts_in tm c0 N.
Proof.
  intros H Cc Bc EN n Bn. destruct (cert_reach l f H) as (R & HR & CR).
  destruct (halts_of_Reach _ _ _ HR) as (st & Hst & Est).
  destruct (Reach_bound _ _ _ _ _ _ HR ltac:(unfold inv; split; [reflexivity|lia])) as [N0 Hb].
  specialize (Hb (7 + 20 * n + 40) ltac:(unfold n; lia)).
  assert (ER : R = Rc).
  { apply cong_small; [|lia|exact Bc]. eapply cong_trans; [apply cong_sym; exact CR|exact Cc]. }
  subst Rc. unfold steps6 in EN.
  assert (E : st = N) by lia.
  subst st. exact Hst.
Qed.
