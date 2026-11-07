(** The Rocq map against the fast C map [hunt/flat/g16/lm.c]: top events of the orbit. *)
From Coq Require Import List Arith.
From G16 Require Import Spec.
Open Scope nat_scope.

Fixpoint scan (N i : nat) (s : list nat) : list (nat * nat) :=
  match N with
  | 0 => nil
  | S n =>
      match topP s with
      | Some P => (i, P) :: scan n (S i) (step s)
      | None => scan n (S i) (step s)
      end
  end.

(** Index n here is step n + 1 in the table of the report. *)
Example events : scan 3000 0 s0 =
  ((1, 23) :: (2, 21) :: (5, 24) :: (38, 104) :: (334, 1290) :: (590, 647) :: (2638, 7146) :: nil)%list.
Proof. vm_compute. reflexivity. Qed.

(** [no_hit_below N] checks the first N stacks by computation. *)
Fixpoint pow2b (fuel m : nat) : bool :=
  match fuel with
  | 0 => false
  | S f => (Nat.eqb m 1) || (Nat.even m && pow2b f (m / 2))
  end.

Lemma pow2b_sound k : forall fuel, k < fuel -> pow2b fuel (2 ^ k) = true.
Proof.
  induction k as [|k IH]; intros fuel H.
  - destruct fuel; [inversion H|reflexivity].
  - destruct fuel as [|f]; [inversion H|]. cbn [pow2b].
    apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split.
    + rewrite Nat.pow_succ_r'. apply Nat.even_mul.
    + rewrite Nat.pow_succ_r', Nat.mul_comm, Nat.div_mul by discriminate. apply IH. apply Nat.succ_lt_mono. exact H.
Qed.

Definition nohit (s : list nat) : bool :=
  match topP s with
  | Some P => negb (pow2b (P + 3) (P + 2))
  | None => true
  end.

Lemma nohit_sound s : nohit s = true -> ~ hit s.
Proof.
  unfold nohit. intros E [P [HP [k Hk]]]. rewrite HP in E. rewrite Hk in E.
  assert (Hl : k < P + 3).
  { pose proof (Nat.pow_gt_lin_r 2 k ltac:(repeat constructor)). rewrite <- Hk in H.
    apply Nat.lt_trans with (P + 2); [exact H|]. rewrite !Nat.add_succ_r. apply Nat.lt_succ_diag_r. }
  rewrite (pow2b_sound k (P + 3) Hl) in E. discriminate.
Qed.

Fixpoint check (N : nat) (s : list nat) : bool :=
  match N with
  | 0 => true
  | S n => nohit s && check n (step s)
  end.

Lemma check_sound N : forall s, check N s = true -> forall k, k < N -> ~ hit (Nat.iter k step s).
Proof.
  induction N as [|N IH]; intros s E k Hk; [inversion Hk|].
  cbn [check] in E. apply Bool.andb_true_iff in E as [E1 E2].
  destruct k as [|k]; [exact (nohit_sound s E1)|].
  rewrite Nat.iter_succ_r. apply (IH _ E2). apply Nat.succ_lt_mono. exact Hk.
Qed.

(** Stated with [Nat.eqb]: reading back a unary 93,998 overflows the stack. *)
Example top_26766 :
  match topP (orbit 26766) with Some P => Nat.eqb P 93998 | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

(** Every stack through that event. *)
Theorem no_hit_below : forall k, k < 30000 -> ~ hit (orbit k).
Proof. apply check_sound. vm_compute. reflexivity. Qed.
