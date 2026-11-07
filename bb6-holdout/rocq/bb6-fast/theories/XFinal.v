(** The exact step count from an orbit with its count and cost, for the constants of Statement.v. *)
From Coq Require Import ZArith Lia.
From Coq Require Uint63.
From BusyCoq Require Import Individual62.
From BB6 Require Import Rules Map Num Big Vec Cert Halts Totals Statement.
Local Open Scope Z_scope.

(** A stretch of the orbit with its application count and its cost modulo 2^315. *)
Definition XR (a b a1 b1 n : Z) (V : V) : Prop := exists r, Reach a b a1 b1 n r /\ cong PM (vval V) r.

Lemma XR_trans a b a1 b1 a2 b2 n1 n2 V1 V2 : XR a b a1 b1 n1 V1 -> XR a1 b1 a2 b2 n2 V2 -> XR a b a2 b2 (n1 + n2) (vplus V1 V2).
Proof.
  intros (r1 & H1 & C1) (r2 & H2 & C2). exists (r1 + r2). split; [exact (Reach_trans _ _ _ _ _ _ _ _ _ _ H1 H2)|].
  eapply cong_trans; [apply vplus_spec|]. apply cong_add; assumption.
Qed.

Theorem steps_of_orbit n V : XR 6 1 a_halt (a_halt + 3) n V -> n = n_apps -> veqb V R_limbs = true -> halts_in tm c0 n_steps.
Proof.
  intros (r & HR & Cv) En Hv. apply veqb_eq in Hv. subst V n.
  destruct (halts_of_Reach _ _ _ HR) as (st & Hst & Est).
  destruct (Reach_bound _ _ _ _ _ _ HR ltac:(unfold inv; split; [reflexivity|lia])) as [_ Hb].
  specialize (Hb (7 + 20 * n_apps + 40) ltac:(lia)).
  assert (ER : r = R_total).
  { apply cong_small.
    - eapply cong_trans; [apply cong_sym; exact Cv|exact R_limbs_ok].
    - assert (B : n_apps * (9 * ((7 + 20 * n_apps + 40) * (7 + 20 * n_apps + 40))) * 2 < PM) by (vm_compute; reflexivity). lia.
    - vm_compute. reflexivity. }
  subst r.
  assert (E : Z.of_nat st = Z.of_nat n_steps).
  { unfold n_steps. rewrite Z2Nat.id by (vm_compute; discriminate). unfold a_halt, R_total in Est. lia. }
  apply Nat2Z.inj in E. rewrite <- E. exact Hst.
Qed.
