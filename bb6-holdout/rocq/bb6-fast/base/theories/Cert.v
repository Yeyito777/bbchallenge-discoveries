(** A certificate: a linked chain of orbit segments with claimed totals, ending at the halt form. *)
From Coq Require Import ZArith Lia Uint63 List Bool.
From BB6 Require Import Map Num Big Vec Check.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

(** A segment of the certificate: from reset state (z0,B0) to (z1,B1), with its claimed totals. *)
Record Seg := mkSeg { z0 : bool; B0 : W; z1 : bool; B1 : W; napps : W; nacc : V }.

Definition seg_ok (s : Seg) : bool :=
  match check_seg (z0 s) (B0 s) (z1 s) (B1 s) with
  | Some (n, acc) => Num.eqb n (napps s) && veqb acc (nacc s)
  | None => false
  end.

(** The part that does not need the machine: the list is linked and starts at A(6,1). *)
Fixpoint linked (z : bool) (B : W) (l : list Seg) : bool :=
  match l with
  | [] => true
  | s :: t => Bool.eqb (z0 s) z && Num.eqb (B0 s) B && linked (z1 s) (B1 s) t
  end.

Fixpoint end_of (z : bool) (B : W) (l : list Seg) : bool * W :=
  match l with
  | [] => (z, B)
  | s :: t => end_of (z1 s) (B1 s) t
  end.

Fixpoint sum_apps (l : list Seg) : Z := match l with [] => 0 | s :: t => val (napps s) + sum_apps t end.
Fixpoint sum_acc (l : list Seg) : V := match l with [] => vzero | s :: t => vplus (nacc s) (sum_acc t) end.

Definition start_B : W := wc 1.

Record Final := mkFinal { fa : W; fapps : W; facc : V }.

Definition final_ok (e : bool * W) (f : Final) : bool :=
  match check_final (fst e) (snd e) with
  | Some (a, n, acc) => Num.eqb a (fa f) && Num.eqb n (fapps f) && veqb acc (facc f)
  | None => false
  end.

(** The whole certificate. Everything in it is a pure computation, and the segments are independent. *)
Definition cert_ok (l : list Seg) (f : Final) : bool :=
  linked false start_B l && forallb seg_ok l && final_ok (end_of false start_B l) f.

Lemma chain_reach l : forall z B, linked z B l = true -> forallb seg_ok l = true ->
  exists R, Reach (za z) (val B) (za (fst (end_of z B l))) (val (snd (end_of z B l))) (sum_apps l) R /\ cong PM (vval (sum_acc l)) R.
Proof.
  induction l as [|s t IH]; intros z B Hl Hf.
  { exists 0. split; [constructor|]. cbn [sum_acc]. rewrite vval_zero. apply cong_refl. }
  cbn [linked] in Hl. apply andb_prop in Hl. destruct Hl as [Hl Ht]. apply andb_prop in Hl. destruct Hl as [Hz HB].
  apply eqb_prop in Hz. apply eqb_spec_W in HB.
  cbn [forallb] in Hf. apply andb_prop in Hf. destruct Hf as [Hs Hf].
  unfold seg_ok in Hs. destruct (check_seg (z0 s) (B0 s) (z1 s) (B1 s)) as [[n acc]|] eqn:C; [|discriminate].
  apply andb_prop in Hs. destruct Hs as [Hn Ha]. apply eqb_spec_W in Hn. apply veqb_eq in Ha. subst acc.
  destruct (check_seg_sound _ _ _ _ _ _ C) as (R1 & H1 & C1).
  destruct (IH _ _ Ht Hf) as (R2 & H2 & C2).
  exists (R1 + R2). cbn [end_of sum_apps sum_acc]. split.
  - rewrite Hn in H1. rewrite Hz, HB in H1. exact (Reach_trans _ _ _ _ _ _ _ _ _ _ H1 H2).
  - eapply cong_trans; [apply vplus_spec|]. apply cong_add; assumption.
Qed.

(** The certificate gives a run from A(6,1) to the halt form. *)
Theorem cert_reach l f : cert_ok l f = true ->
  exists R, Reach 6 1 (val (fa f)) (val (fa f) + 3) (sum_apps l + val (fapps f)) R /\ cong PM (vval (vplus (sum_acc l) (facc f))) R.
Proof.
  unfold cert_ok. intros H. apply andb_prop in H. destruct H as [H Hf]. apply andb_prop in H. destruct H as [Hl Hs].
  destruct (chain_reach l false start_B Hl Hs) as (R1 & H1 & C1).
  unfold final_ok in Hf. destruct (check_final (fst (end_of false start_B l)) (snd (end_of false start_B l))) as [[[a n] acc]|] eqn:C; [|discriminate].
  apply andb_prop in Hf. destruct Hf as [Hf Ha]. apply andb_prop in Hf. destruct Hf as [Hf Hn].
  apply eqb_spec_W in Hf. apply eqb_spec_W in Hn. apply veqb_eq in Ha. subst acc.
  destruct (check_final_sound _ _ _ _ _ C) as (R2 & H2 & C2).
  exists (R1 + R2). split.
  - change (za false) with 6 in H1. change (val start_B) with 1 in H1.
    rewrite Hf, Hn in H2. exact (Reach_trans _ _ _ _ _ _ _ _ _ _ H1 H2).
  - eapply cong_trans; [apply vplus_spec|]. apply cong_add; assumption.
Qed.

(** ** A bound on the cost term, from the number of applications alone *)
Lemma step_bound a b a1 b1 r : inv a b -> aStep a b = Some (a1, b1, r) ->
  a1 + b1 <= a + b + 20 /\ Z.abs r <= 9 * ((a + b + 40) * (a + b + 40)).
Proof.
  intros (Ha2 & Ha6 & Hb1) H. unfold aStep in H.
  destruct (Z.eqb_spec b (a+3)) as [|N1]. { discriminate. }
  destruct (Z.ltb_spec (a+3) b) as [L1|L1].
  { apply some3 in H. destruct H as (<- & <- & <-). split; [lia|]. apply Z.abs_le. nia. }
  destruct (Z.eqb_spec b 1) as [|N2].
  { subst b. destruct (Z.eqb_spec (a mod 4) 2); apply some3 in H; destruct H as (<- & <- & <-); (split; [lia|apply Z.abs_le; nia]). }
  destruct (Z.eqb_spec b 3) as [|N3].
  { subst b. destruct (Z.eqb_spec (a mod 4) 2); apply some3 in H; destruct H as (<- & <- & <-); (split; [lia|apply Z.abs_le; nia]). }
  destruct (Z.eqb_spec (b mod 2) 1) as [O|O].
  { destruct (Z.eqb_spec b (a+1)) as [N4|N4].
    { apply some3 in H; destruct H as (<- & <- & <-); split; [lia|apply Z.abs_le; nia]. }
    destruct (Z.eqb_spec ((a-b+5) mod 4) 2); apply some3 in H; destruct H as (<- & <- & <-); (split; [lia|apply Z.abs_le; nia]). }
  destruct (Z.eqb_spec ((a-b) mod 4) 2); apply some3 in H; destruct H as (<- & <- & <-); (split; [lia|apply Z.abs_le; nia]).
Qed.

Lemma Reach_bound a b a1 b1 n r : Reach a b a1 b1 n r -> inv a b ->
  0 <= n /\ forall M, a + b + 20 * n + 40 <= M -> Z.abs r <= n * (9 * (M * M)).
Proof.
  induction 1 as [a b|a b a1 b1 r a2 b2 n s Hs _ IH]; intros Hi.
  { split; [lia|]. intros M _. cbn. lia. }
  pose proof (aStep_inv _ _ _ _ _ Hi Hs) as Hi1.
  destruct (IH Hi1) as [N0 Hb]. destruct (step_bound _ _ _ _ _ Hi Hs) as [S1 R1].
  destruct Hi as (_ & Ha & Hb1). destruct Hi1 as (_ & Ha1 & Hb2).
  split; [lia|]. intros M HM.
  specialize (Hb M ltac:(lia)).
  assert (Q : (a + b + 40) * (a + b + 40) <= M * M) by nia.
  assert (Z.abs (r + s) <= Z.abs r + Z.abs s) by apply Z.abs_triangle.
  nia.
Qed.

(** Two values congruent mod 2^315 and both small are equal. *)
Lemma cong_small x y : cong PM x y -> Z.abs x * 2 < PM -> Z.abs y * 2 < PM -> x = y.
Proof.
  intros [k ->] H1 H2. assert (P : 0 < PM) by reflexivity.
  destruct (Z.eq_dec k 0) as [->|Nk]; [ring|].
  exfalso. assert (PM <= Z.abs (k * PM)).
  { rewrite Z.abs_mul, (Z.abs_eq PM) by lia. nia. }
  assert (Z.abs (k * PM) <= Z.abs (y + k * PM) + Z.abs y).
  { replace (k * PM) with ((y + k * PM) + (- y)) at 1 by ring. rewrite <- (Z.abs_opp y). apply Z.abs_triangle. }
  lia.
Qed.

