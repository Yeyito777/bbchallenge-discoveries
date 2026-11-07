(** Machines whose right edge ends in runs 6, 4, 1: from the raw rules to the interface of [Generic]. *)
From Coq Require Import List Arith Lia.
From BusyCoq Require Import Individual62.
From G16 Require Import Spec Tape Generic.
Import ListNotations.
Open Scope list.
Open Scope sym.

Section Fam1.
Variable tm : TM.
Variables f a : Q.

Hypothesis R_round : forall lx p n y rx,
  cfg f lx p (S (S n)) y rx -[ tm ]->+ cfg f lx (S p) n (S y) rx.
Hypothesis R_even : forall q lx p y rx,
  cfg f (0 >> [1]^^q *> lx) (S (S (S p))) 1 y rx -[ tm ]->+ cfg f lx (S q) p 2 (0 >> [1]^^(S y) *> rx).
Hypothesis R_odd : forall lx p y rx,
  cfg f lx p 2 y rx -[ tm ]->+ AP a (y + 3) (0 >> [1]^^(p + 2) *> lx) rx.
Hypothesis R_cross : forall cur lx e rx,
  AP a cur lx (0 >> [1]^^(S (S e)) *> rx) -[ tm ]->+ AP a (S e) (0 >> [1]^^(S cur) *> lx) rx.
Hypothesis R_tail : forall x q lx,
  AP a 1 (0 >> [1]^^4 *> 0 >> [1]^^6 *> 0 >> [1]^^(S (S (S x))) *> 0 >> [1]^^q *> lx) (const 0)
    -[ tm ]->+ cfg f lx (S q) (x + 4) 2 (RS tail0).
Hypothesis R_top : forall p y rx,
  cfg f (const 0) (S p) 1 y rx -[ tm ]->+ LSc f (S p) (0 >> [1]^^(S y) *> rx).
Hypothesis R_ls : forall n rx,
  LSc f (S (S (S (S n)))) rx -[ tm ]->+ cfg f (const 0) 1 (S n) 2 rx.
Hypothesis R_ls1 : forall rx, LSc f 1 rx -[ tm ]->+ AP a 3 (RS (1%nat :: nil)) rx.
Hypothesis R_ls3 : forall rx, LSc f 3 rx -[ tm ]->+ AP a 4 (RS (2%nat :: nil)) rx.
Hypothesis R_ls2 : forall rx, exists c, LSc f 2 rx -[ tm ]->* c /\ halted tm c.
Hypothesis R_start : c0 -[ tm ]->+ Cc a 1 s0.

Definition Stage1 (ll : list nat) (x r : nat) (rr : list nat) : Q * tape :=
  cfg f (RS ll) (x + 1) (r - 1) 2 (RS rr).
Definition LSf1 (P : nat) (rr : list nat) : Q * tape := LSc f P (RS rr).

Lemma zig k : forall lx p r y rx,
  cfg f lx p (r + 2 * k) y rx -[ tm ]->* cfg f lx (p + k) r (y + k) rx.
Proof.
  induction k as [|k IH]; intros lx p r y rx.
  - replace (r + 2 * 0)%nat with r by lia. replace (p + 0)%nat with p by lia. replace (y + 0)%nat with y by lia.
    apply evstep_refl.
  - replace (r + 2 * S k)%nat with (S (S (r + 2 * k))) by lia.
    replace (p + S k)%nat with (S p + k)%nat by lia. replace (y + S k)%nat with (S y + k)%nat by lia.
    eapply evstep_trans; [apply progress_evstep; apply R_round|apply IH].
Qed.

Lemma pass rr : forall cur done, all2 rr ->
  AP a cur (RS done) (RS (rr ++ tail0)) -[ tm ]->+ Cc a 1 (rev rr ++ S cur :: done).
Proof.
  induction rr as [|e rr IH]; intros cur done Ha.
  - eapply progress_trans; [exact (R_cross cur (RS done) 4 (RS (4%nat :: 2%nat :: nil)))|].
    eapply progress_trans; [exact (R_cross 5 _ 2 (RS (2%nat :: nil)))|].
    exact (R_cross 3 _ 0 (RS nil)).
  - inversion Ha as [|x t He Ht]; subst.
    destruct e as [|[|e']]; try lia.
    eapply progress_trans; [exact (R_cross cur (RS done) e' (RS (rr ++ tail0)))|].
    replace (rev (S (S e') :: rr) ++ S cur :: done) with (rev rr ++ S (S e') :: S cur :: done)
      by (simpl; rewrite <- app_assoc; reflexivity).
    exact (IH (S e') (S cur :: done) Ht).
Qed.

Lemma if_tail x q ll : (3 <= x)%nat -> Cc a 1 (x :: q :: ll) -[ tm ]->+ Stage1 ll q (x + 2)%nat tail0.
Proof.
  intros H. destruct x as [|[|[|x]]]; try lia. unfold Stage1.
  replace (q + 1)%nat with (S q) by lia.
  replace (S (S (S x)) + 2 - 1)%nat with (x + 4)%nat by lia.
  exact (R_tail x q (RS ll)).
Qed.

Lemma if_even q ll x r rr : Nat.even r = true -> (2 <= r)%nat -> (3 <= x)%nat ->
  Stage1 (q :: ll) x r rr -[ tm ]->+ Stage1 ll q (x + r / 2 - 2)%nat ((r / 2 + 2)%nat :: rr).
Proof.
  intros E H2 H3. destruct (even_form r E H2) as [m ->].
  assert (Hd : ((2 * m + 2) / 2 = m + 1)%nat) by (apply dv; lia). rewrite Hd. unfold Stage1.
  replace (2 * m + 2 - 1)%nat with (1 + 2 * m)%nat by lia.
  replace (x + (m + 1) - 2 - 1)%nat with (x + m - 2)%nat by lia.
  replace (m + 1 + 2)%nat with (S (2 + m)) by lia.
  replace (q + 1)%nat with (S q) by lia.
  eapply evstep_progress_trans; [apply zig|].
  replace (x + 1 + m)%nat with (S (S (S (x + m - 2)))) by lia.
  exact (R_even q (RS ll) (x + m - 2) (2 + m) (RS rr)).
Qed.

Lemma if_odd ll x r rr : Nat.even r = false -> (3 <= r)%nat -> (1 <= x)%nat -> all2 rr ->
  Stage1 ll x r (rr ++ tail0) -[ tm ]->+ Cc a 1 (rev rr ++ ((r + 9) / 2)%nat :: (x + (r + 3) / 2)%nat :: ll).
Proof.
  intros E H3 H1 Ha. destruct (odd_form r E ltac:(lia)) as [m ->].
  assert (Hd1 : ((2 * m + 3 + 9) / 2 = m + 6)%nat) by (apply dv; lia).
  assert (Hd2 : ((2 * m + 3 + 3) / 2 = m + 3)%nat) by (apply dv; lia).
  rewrite Hd1, Hd2. unfold Stage1.
  replace (2 * m + 3 - 1)%nat with (2 + 2 * m)%nat by lia.
  eapply evstep_progress_trans; [apply zig|].
  eapply progress_trans; [apply R_odd|].
  replace (m + 6)%nat with (S (2 + m + 3)) by lia.
  replace (x + (m + 3))%nat with (x + 1 + m + 2)%nat by lia.
  exact (pass rr (2 + m + 3) ((x + 1 + m + 2) :: ll) Ha).
Qed.

Lemma if_topc x r rr : Nat.even r = true -> (2 <= r)%nat -> (1 <= x)%nat ->
  Stage1 nil x r rr -[ tm ]->+ LSf1 (x + r / 2)%nat ((r / 2 + 2)%nat :: rr).
Proof.
  intros E H2 H1. destruct (even_form r E H2) as [m ->].
  assert (Hd : ((2 * m + 2) / 2 = m + 1)%nat) by (apply dv; lia). rewrite Hd. unfold Stage1, LSf1.
  replace (2 * m + 2 - 1)%nat with (1 + 2 * m)%nat by lia.
  replace (m + 1 + 2)%nat with (S (2 + m)) by lia.
  replace (x + (m + 1))%nat with (S (x + m)) by lia.
  eapply evstep_progress_trans; [apply zig|].
  replace (x + 1 + m)%nat with (S (x + m)) by lia.
  exact (R_top (x + m) (2 + m) (RS rr)).
Qed.

Lemma if_lse P rr : Nat.even P = true -> (4 <= P)%nat ->
  LSf1 P rr -[ tm ]->+ LSf1 (P / 2 - 1)%nat ((P / 2 + 1)%nat :: rr).
Proof.
  intros E H4. destruct (even_form P E ltac:(lia)) as [m0 Hm].
  destruct m0 as [|m]; [lia|]. subst P.
  assert (Hd : ((2 * S m + 2) / 2 = m + 2)%nat) by (apply dv; lia). rewrite Hd. unfold LSf1.
  replace (2 * S m + 2)%nat with (S (S (S (S (2 * m))))) by lia.
  eapply progress_trans; [apply R_ls|].
  replace (S (2 * m)) with (1 + 2 * m)%nat by lia.
  eapply evstep_progress_trans; [apply zig|].
  replace (m + 2 - 1)%nat with (S m) by lia.
  replace (m + 2 + 1)%nat with (S (2 + m)) by lia.
  exact (R_top m (2 + m) (RS rr)).
Qed.

Lemma if_lso P rr : Nat.even P = false -> all2 rr ->
  LSf1 P (rr ++ tail0) -[ tm ]->+ Cc a 1 (rev rr ++ ((P + 1) / 2 + 3)%nat :: ((P + 1) / 2)%nat :: nil).
Proof.
  intros E Ha. destruct (oddP_form P E) as [m ->]. unfold LSf1.
  destruct m as [|[|m]].
  - eapply progress_trans; [apply R_ls1|]. exact (pass rr 3 (1%nat :: nil) Ha).
  - eapply progress_trans; [apply R_ls3|]. exact (pass rr 4 (2%nat :: nil) Ha).
  - assert (Hd : ((2 * S (S m) + 1 + 1) / 2 = m + 3)%nat) by (apply dv; lia). rewrite Hd.
    replace (2 * S (S m) + 1)%nat with (S (S (S (S (2 * m + 1))))) by lia.
    eapply progress_trans; [apply R_ls|].
    replace (S (2 * m + 1)) with (2 + 2 * m)%nat by lia.
    eapply evstep_progress_trans; [apply zig|].
    eapply progress_trans; [apply R_odd|].
    replace (m + 3 + 3)%nat with (S (2 + m + 3)) by lia.
    replace (m + 3)%nat with (1 + m + 2)%nat by lia.
    exact (pass rr (2 + m + 3) ((1 + m + 2)%nat :: nil) Ha).
Qed.

Lemma if_ls2 rr : exists c, LSf1 2 rr -[ tm ]->* c /\ halted tm c.
Proof. apply R_ls2. Qed.

Theorem fam1_main : halts tm c0 <-> exists n, hit (orbit n).
Proof.
  apply (generic_main tm (Cc a 1) Stage1 LSf1 if_tail if_even if_odd if_topc if_lse if_lso if_ls2 R_start).
Qed.
Theorem fam1_map n : (forall k, (k < n)%nat -> ~ hit (orbit k)) -> c0 -[ tm ]->+ Cc a 1 (orbit n).
Proof.
  intros H. exact (proj2 (reach_orbit tm (Cc a 1) Stage1 LSf1 if_tail if_even if_odd if_topc if_lse if_lso R_start n H)).
Qed.

End Fam1.
