(** From the rule interface to the theorem: the machine halts iff some top event of the orbit has P + 2 = 2^k. *)
From Coq Require Import List Arith Lia.
From BusyCoq Require Import Individual62.
From G16 Require Import Spec.
Import ListNotations.
Open Scope list.
Local Open Scope nat_scope.

Definition tail0 : list nat := [6; 4; 2].

Fixpoint InvT (s : list nat) : Prop :=
  match s with
  | [] => False
  | x :: t => match t with
              | [] => 1 <= x
              | _ :: _ => 3 <= x /\ InvT t
              end
  end.
Definition Inv (s : list nat) : Prop := InvT s /\ 2 <= length s.
Definition all2 (l : list nat) : Prop := Forall (fun e => 2 <= e) l.

(** Arithmetic. *)
Lemma even_form r : Nat.even r = true -> 2 <= r -> exists m, r = 2 * m + 2.
Proof.
  intros H H2. apply Nat.even_spec in H. destruct H as [k Hk]. exists (k - 1). lia.
Qed.
Lemma odd_form r : Nat.even r = false -> 2 <= r -> exists m, r = 2 * m + 3.
Proof.
  intros H H2. assert (Hn : Nat.odd r = true) by (unfold Nat.odd; rewrite H; reflexivity).
  apply Nat.odd_spec in Hn. destruct Hn as [k Hk]. exists (k - 1). lia.
Qed.
Lemma div2a m c : (2 * m + 2 * c) / 2 = m + c.
Proof. symmetry. apply Nat.div_unique with 0; lia. Qed.
Lemma div2b m c : (2 * m + 2 * c + 1) / 2 = m + c.
Proof. symmetry. apply Nat.div_unique with 1; lia. Qed.
Lemma even_2m m c : Nat.even (2 * m + 2 * c) = true.
Proof. apply Nat.even_spec. exists (m + c). lia. Qed.
Lemma even_2m1 m c : Nat.even (2 * m + 2 * c + 1) = false.
Proof.
  destruct (Nat.even (2 * m + 2 * c + 1)) eqn:E; [|reflexivity].
  apply Nat.even_spec in E. destruct E as [k Hk]. lia.
Qed.

Lemma pw_half P : Nat.even P = true -> 4 <= P -> pw (P / 2 - 1) -> pw P.
Proof.
  intros He H4 [k Hk]. destruct (even_form P He ltac:(lia)) as [m ->].
  replace (2 * m + 2) with (2 * m + 2 * 1) in * by lia. rewrite div2a in Hk.
  exists (S k). rewrite Nat.pow_succ_r'. lia.
Qed.
Lemma pw_half' P : Nat.even P = true -> 4 <= P -> pw P -> pw (P / 2 - 1).
Proof.
  intros He H4 [k Hk]. destruct (even_form P He ltac:(lia)) as [m ->].
  destruct k as [|k]; [simpl in Hk; lia|].
  rewrite Nat.pow_succ_r' in Hk.
  exists k. replace (2 * m + 2) with (2 * m + 2 * 1) by lia. rewrite div2a. lia.
Qed.
Lemma pw_not_odd P : Nat.even P = false -> ~ pw P.
Proof.
  intros He [k Hk]. destruct k as [|k]; [simpl in Hk; lia|].
  rewrite Nat.pow_succ_r' in Hk.
  assert (Hev : Nat.even P = true).
  { apply Nat.even_spec. exists (2 ^ k - 1). lia. }
  congruence.
Qed.
Lemma pw_2 : pw 2.
Proof. exists 2. reflexivity. Qed.
Lemma pw_dec P : {pw P} + {~ pw P}.
Proof.
  destruct (Nat.eq_dec (P + 2) (2 ^ Nat.log2 (P + 2))) as [E|N].
  - left. exists (Nat.log2 (P + 2)). exact E.
  - right. intros [k Hk]. apply N. rewrite Hk. rewrite Nat.log2_pow2 by lia. reflexivity.
Qed.


Lemma dv a b : a = 2 * b -> a / 2 = b.
Proof. intros ->. symmetry. apply Nat.div_unique with 0; lia. Qed.
Lemma dv1 a b : a = 2 * b + 1 -> a / 2 = b.
Proof. intros ->. symmetry. apply Nat.div_unique with 1; lia. Qed.

Lemma evenP_form P : Nat.even P = true -> 1 <= P -> exists m, P = 2 * m + 2.
Proof. intros H H1. apply even_form; [exact H|]. destruct P as [|[|P]]; simpl in H; try discriminate; lia. Qed.
Lemma oddP_form P : Nat.even P = false -> exists m, P = 2 * m + 1.
Proof.
  intros H. assert (Hn : Nat.odd P = true) by (unfold Nat.odd; rewrite H; reflexivity).
  apply Nat.odd_spec in Hn. destruct Hn as [k Hk]. exists k. lia.
Qed.

(** Unfolding equations for the map. *)
Lemma carry_e1 a r : Nat.even r = true -> carry r [a] = (r / 2 + 2) :: top (a + r / 2) (a + r / 2).
Proof.
  intros E. transitivity (if Nat.even r then (r / 2 + 2) :: top (a + r / 2) (a + r / 2) else ((r + 9) / 2) :: (a + (r + 3) / 2) :: []);
  [reflexivity|rewrite E; reflexivity].
Qed.
Lemma carry_e2 a q t r : Nat.even r = true -> carry r (a :: q :: t) = (r / 2 + 2) :: carry (a + r / 2 - 2) (q :: t).
Proof.
  intros E. transitivity (if Nat.even r then (r / 2 + 2) :: carry (a + r / 2 - 2) (q :: t) else ((r + 9) / 2) :: (a + (r + 3) / 2) :: q :: t);
  [reflexivity|rewrite E; reflexivity].
Qed.
Lemma carry_o a t r : Nat.even r = false -> carry r (a :: t) = ((r + 9) / 2) :: (a + (r + 3) / 2) :: t.
Proof.
  intros E. destruct t as [|q t].
  - transitivity (if Nat.even r then (r / 2 + 2) :: top (a + r / 2) (a + r / 2) else ((r + 9) / 2) :: (a + (r + 3) / 2) :: []);
    [reflexivity|rewrite E; reflexivity].
  - transitivity (if Nat.even r then (r / 2 + 2) :: carry (a + r / 2 - 2) (q :: t) else ((r + 9) / 2) :: (a + (r + 3) / 2) :: q :: t);
    [reflexivity|rewrite E; reflexivity].
Qed.
Lemma carryP_e1 a r : Nat.even r = true -> carryP r [a] = Some (a + r / 2).
Proof.
  intros E. transitivity (if Nat.even r then Some (a + r / 2) else None); [reflexivity|rewrite E; reflexivity].
Qed.
Lemma carryP_e2 a q t r : Nat.even r = true -> carryP r (a :: q :: t) = carryP (a + r / 2 - 2) (q :: t).
Proof.
  intros E. transitivity (if Nat.even r then carryP (a + r / 2 - 2) (q :: t) else None); [reflexivity|rewrite E; reflexivity].
Qed.
Lemma carryP_o a t r : Nat.even r = false -> carryP r (a :: t) = None.
Proof.
  intros E. destruct t as [|q t].
  - transitivity (if Nat.even r then Some (a + r / 2) else None); [reflexivity|rewrite E; reflexivity].
  - transitivity (if Nat.even r then carryP (a + r / 2 - 2) (q :: t) else None); [reflexivity|rewrite E; reflexivity].
Qed.

(** Facts on the list map. *)
Lemma top_ne f P : top (S f) P <> [].
Proof. cbn [top]. destruct (Nat.even P); discriminate. Qed.

Lemma InvT_cons x t : t <> [] -> 3 <= x -> InvT t -> InvT (x :: t).
Proof. intros Hn H3 Ht. destruct t as [|y t]; [congruence|]. simpl. split; assumption. Qed.

(** One step of the first-run stage, both cases. *)
Lemma top_even f P : Nat.even P = true -> top (S f) P = (P / 2 + 1) :: top f (P / 2 - 1).
Proof. intros E. cbn [top]. rewrite E. reflexivity. Qed.
Lemma top_odd f P : Nat.even P = false -> top (S f) P = [(P + 1) / 2 + 3; (P + 1) / 2].
Proof. intros E. cbn [top]. rewrite E. reflexivity. Qed.

Lemma top_even_shape P : Nat.even P = true -> 1 <= P -> ~ pw P ->
  exists m, P = 2 * m + 4 /\ P / 2 = m + 2.
Proof.
  intros E H1 Hn. destruct (evenP_form P E H1) as [m ->].
  destruct m as [|m]; [exfalso; apply Hn; exact pw_2|].
  exists m. split; [lia|]. apply dv. lia.
Qed.

Lemma InvT_top f P : 1 <= P -> P <= f -> ~ pw P -> InvT (top f P).
Proof.
  revert P. induction f as [|f IH]; intros P H1 Hf Hn; [lia|].
  destruct (Nat.even P) eqn:E.
  - rewrite top_even by exact E.
    destruct (top_even_shape P E H1 Hn) as [m [Hm Hd]]. rewrite Hd.
    assert (Hn' : ~ pw (m + 2 - 1)).
    { intros Hp. apply Hn. apply pw_half; [exact E|lia|]. rewrite Hd. exact Hp. }
    destruct f as [|f']; [lia|].
    apply InvT_cons; [apply top_ne|lia|]. apply IH; [lia|lia|exact Hn'].
  - rewrite top_odd by exact E. destruct (oddP_form P E) as [m ->].
    assert (Hd : (2 * m + 1 + 1) / 2 = m + 1) by (apply dv; lia). rewrite Hd. simpl. lia.
Qed.

Lemma top_all2_len f P : 1 <= P -> P <= f -> ~ pw P -> 1 <= length (top f P).
Proof.
  intros H1 Hf _. destruct f as [|f']; [lia|]. destruct (top (S f') P) eqn:E; [|simpl; lia].
  exfalso. apply (top_ne f' P). exact E.
Qed.

Lemma nohit_even r a t : Nat.even r = true ->
  (forall P, carryP r (a :: t) = Some P -> ~ pw P) ->
  match t with
  | [] => ~ pw (a + r / 2)
  | _ :: _ => forall P, carryP (a + r / 2 - 2) t = Some P -> ~ pw P
  end.
Proof.
  intros E H. destruct t as [|q t'].
  - apply (H (a + r / 2)). apply carryP_e1. exact E.
  - intros P HP. apply (H P). rewrite carryP_e2 by exact E. exact HP.
Qed.

Lemma Inv_carry t : forall a r, 2 <= r -> InvT (a :: t) ->
  (forall P, carryP r (a :: t) = Some P -> ~ pw P) ->
  InvT (carry r (a :: t)) /\ 2 <= length (carry r (a :: t)).
Proof.
  induction t as [|q t IH]; intros a r H2 HI Hn; destruct (Nat.even r) eqn:E.
  - destruct (even_form r E H2) as [m Hm].
    assert (Hd : r / 2 = m + 1) by (apply dv; lia).
    pose proof (nohit_even r a [] E Hn) as Hn'. cbn iota beta in Hn'.
    rewrite carry_e1 by exact E. rewrite Hd in *. simpl in HI.
    assert (HT := InvT_top (a + (m + 1)) (a + (m + 1)) ltac:(lia) ltac:(lia) Hn').
    assert (HL := top_all2_len (a + (m + 1)) (a + (m + 1)) ltac:(lia) ltac:(lia) Hn').
    split; [|cbn [length]; lia].
    destruct (top (a + (m + 1)) (a + (m + 1))) as [|y z]; [simpl in HL; lia|].
    split; [lia|exact HT].
  - destruct (odd_form r E H2) as [m Hm].
    assert (Hd1 : (r + 9) / 2 = m + 6) by (apply dv; lia).
    assert (Hd2 : (r + 3) / 2 = m + 3) by (apply dv; lia).
    rewrite carry_o by exact E. rewrite Hd1, Hd2. simpl in HI. simpl. lia.
  - destruct (even_form r E H2) as [m Hm].
    assert (Hd : r / 2 = m + 1) by (apply dv; lia).
    pose proof (nohit_even r a (q :: t) E Hn) as Hn'. cbn iota beta in Hn'.
    rewrite carry_e2 by exact E. rewrite Hd in *. destruct HI as [Ha HI].
    destruct (IH q (a + (m + 1) - 2) ltac:(lia) HI) as [I1 I2]; [exact Hn'|].
    split; [|cbn [length]; lia].
    destruct (carry (a + (m + 1) - 2) (q :: t)) as [|y z]; [simpl in I2; lia|].
    split; [lia|exact I1].
  - destruct (odd_form r E H2) as [m Hm].
    assert (Hd1 : (r + 9) / 2 = m + 6) by (apply dv; lia).
    assert (Hd2 : (r + 3) / 2 = m + 3) by (apply dv; lia).
    rewrite carry_o by exact E. rewrite Hd1, Hd2. destruct HI as [Ha HI].
    split; [|simpl; lia].
    split; [lia|]. destruct t as [|y t]; [simpl in HI; simpl; lia|].
    split; [lia|]. exact HI.
Qed.

Lemma Inv_step s : Inv s -> (forall P, topP s = Some P -> ~ pw P) -> Inv (step s).
Proof.
  intros [HI HL] Hn. destruct s as [|x [|q t]]; simpl in HL; try lia.
  destruct HI as [Hx HI]. cbn [topP] in Hn.
  destruct (Inv_carry t q (x + 2) ltac:(lia) HI Hn) as [A B]. split; assumption.
Qed.

Section Generic.
Variable tm : TM.
Variable C : list nat -> Q * tape.
Variable Stage : list nat -> nat -> nat -> list nat -> Q * tape.
Variable LSf : nat -> list nat -> Q * tape.

Hypothesis H_tail : forall x q ll, 3 <= x ->
  C (x :: q :: ll) -[ tm ]->+ Stage ll q (x + 2) tail0.
Hypothesis H_even : forall q ll a r rr, Nat.even r = true -> 2 <= r -> 3 <= a ->
  Stage (q :: ll) a r rr -[ tm ]->+ Stage ll q (a + r / 2 - 2) ((r / 2 + 2) :: rr).
Hypothesis H_odd : forall ll a r rr, Nat.even r = false -> 3 <= r -> 1 <= a -> all2 rr ->
  Stage ll a r (rr ++ tail0) -[ tm ]->+ C (rev rr ++ ((r + 9) / 2) :: (a + (r + 3) / 2) :: ll).
Hypothesis H_topc : forall a r rr, Nat.even r = true -> 2 <= r -> 1 <= a ->
  Stage [] a r rr -[ tm ]->+ LSf (a + r / 2) ((r / 2 + 2) :: rr).
Hypothesis H_lse : forall P rr, Nat.even P = true -> 4 <= P ->
  LSf P rr -[ tm ]->+ LSf (P / 2 - 1) ((P / 2 + 1) :: rr).
Hypothesis H_lso : forall P rr, Nat.even P = false -> all2 rr ->
  LSf P (rr ++ tail0) -[ tm ]->+ C (rev rr ++ [(P + 1) / 2 + 3; (P + 1) / 2]).
Hypothesis H_ls2 : forall rr, exists c, LSf 2 rr -[ tm ]->* c /\ halted tm c.
Hypothesis H_start : c0 -[ tm ]->+ C s0.

Lemma top_run f : forall P rr, 1 <= P -> P <= f -> ~ pw P -> all2 rr ->
  LSf P (rr ++ tail0) -[ tm ]->+ C (rev rr ++ top f P).
Proof.
  induction f as [|f IH]; intros P rr H1 Hf Hn Ha; [lia|].
  destruct (Nat.even P) eqn:E.
  - rewrite top_even by exact E.
    destruct (top_even_shape P E H1 Hn) as [m [Hm Hd]].
    assert (Hn' : ~ pw (P / 2 - 1)).
    { intros Hp. apply Hn. apply pw_half; [exact E|lia|exact Hp]. }
    eapply progress_trans; [apply H_lse; [exact E|lia]|].
    rewrite Hd in *.
    replace (rev rr ++ (m + 2 + 1) :: top f (m + 2 - 1))
      with (rev ((m + 2 + 1) :: rr) ++ top f (m + 2 - 1))
      by (simpl; rewrite <- app_assoc; reflexivity).
    change ((m + 2 + 1) :: rr ++ tail0) with (((m + 2 + 1) :: rr) ++ tail0).
    apply IH; [lia|lia|exact Hn'|constructor; [lia|exact Ha]].
  - rewrite top_odd by exact E. apply H_lso; assumption.
Qed.

Lemma casc t : forall a r rr, 2 <= r -> InvT (a :: t) -> all2 rr ->
  (forall P, carryP r (a :: t) = Some P -> ~ pw P) ->
  Stage t a r (rr ++ tail0) -[ tm ]->+ C (rev rr ++ carry r (a :: t)).
Proof.
  induction t as [|q t IH]; intros a r rr H2 HI Ha Hn; destruct (Nat.even r) eqn:E.
  - destruct (even_form r E H2) as [m Hm].
    assert (Hd : r / 2 = m + 1) by (apply dv; lia).
    pose proof (nohit_even r a [] E Hn) as Hn'. cbn iota beta in Hn'. simpl in HI.
    rewrite carry_e1 by exact E.
    eapply progress_trans; [apply H_topc; [exact E|exact H2|exact HI]|].
    rewrite Hd in *.
    replace (rev rr ++ (m + 1 + 2) :: top (a + (m + 1)) (a + (m + 1)))
      with (rev ((m + 1 + 2) :: rr) ++ top (a + (m + 1)) (a + (m + 1)))
      by (simpl; rewrite <- app_assoc; reflexivity).
    change ((m + 1 + 2) :: rr ++ tail0) with (((m + 1 + 2) :: rr) ++ tail0).
    apply top_run; [lia|lia|exact Hn'|constructor; [lia|exact Ha]].
  - destruct (odd_form r E H2) as [m Hm]. simpl in HI.
    rewrite carry_o by exact E.
    apply H_odd; [exact E|lia|exact HI|exact Ha].
  - destruct (even_form r E H2) as [m Hm].
    assert (Hd : r / 2 = m + 1) by (apply dv; lia).
    pose proof (nohit_even r a (q :: t) E Hn) as Hn'. cbn iota beta in Hn'.
    destruct HI as [Ha3 HI].
    rewrite carry_e2 by exact E.
    eapply progress_trans; [apply H_even; [exact E|exact H2|exact Ha3]|].
    rewrite Hd in *.
    replace (rev rr ++ (m + 1 + 2) :: carry (a + (m + 1) - 2) (q :: t))
      with (rev ((m + 1 + 2) :: rr) ++ carry (a + (m + 1) - 2) (q :: t))
      by (simpl; rewrite <- app_assoc; reflexivity).
    change ((m + 1 + 2) :: rr ++ tail0) with (((m + 1 + 2) :: rr) ++ tail0).
    apply IH; [lia|exact HI|constructor; [lia|exact Ha]|exact Hn'].
  - destruct (odd_form r E H2) as [m Hm]. destruct HI as [Ha3 HI].
    rewrite carry_o by exact E.
    apply H_odd; [exact E|lia|lia|exact Ha].
Qed.

Lemma C_step s : Inv s -> (forall P, topP s = Some P -> ~ pw P) -> C s -[ tm ]->+ C (step s).
Proof.
  intros [HI HL] Hn. destruct s as [|x [|q t]]; simpl in HL; try lia.
  destruct HI as [Hx HI]. cbn [topP] in Hn. cbn [step].
  eapply progress_trans; [apply H_tail; exact Hx|].
  apply (casc t q (x + 2) [] ltac:(lia) HI (Forall_nil _) Hn).
Qed.

Lemma pw_chain k : forall P rr, 2 <= P -> P + 2 = 2 ^ k ->
  exists c, LSf P rr -[ tm ]->* c /\ halted tm c.
Proof.
  induction k as [|k IH]; intros P rr H2 Hk; [simpl in Hk; lia|].
  destruct (Nat.eq_dec P 2) as [->|N2]; [apply H_ls2|].
  rewrite Nat.pow_succ_r' in Hk.
  assert (HP : P = 2 * (2 ^ k - 1)) by lia.
  assert (Hpk : 2 ^ k >= 1) by (apply Nat.pow_le_mono_r_iff || (pose proof (Nat.pow_nonzero 2 k); lia)).
  assert (He : Nat.even P = true) by (apply Nat.even_spec; exists (2 ^ k - 1); lia).
  assert (H6 : 4 <= P).
  { destruct (even_form P He H2) as [m Hm]. lia. }
  assert (Hd : P / 2 = 2 ^ k - 1) by (apply dv; lia).
  assert (H3 : 3 <= 2 ^ k) by lia.
  assert (H4' : 4 <= 2 ^ k).
  { destruct k as [|[|k]]; simpl in *; lia. }
  destruct (IH (P / 2 - 1) ((P / 2 + 1) :: rr)) as [c [Hc Hh]]; [lia|lia|].
  exists c. split; [|exact Hh].
  eapply evstep_trans; [apply progress_evstep; apply H_lse; [exact He|exact H6]|exact Hc].
Qed.

Lemma casc_halt t : forall a r rr P, 2 <= r -> InvT (a :: t) ->
  carryP r (a :: t) = Some P -> pw P ->
  exists c, Stage t a r rr -[ tm ]->* c /\ halted tm c.
Proof.
  induction t as [|q t IH]; intros a r rr P H2 HI HP [k Hk]; destruct (Nat.even r) eqn:E;
    try (rewrite carryP_o in HP by exact E; discriminate).
  - destruct (even_form r E H2) as [m Hm]. rewrite carryP_e1 in HP by exact E. injection HP as <-. simpl in HI.
    assert (Hd : r / 2 = m + 1) by (apply dv; lia).
    destruct (pw_chain k (a + r / 2) ((r / 2 + 2) :: rr) ltac:(lia) Hk) as [c [Hc Hh]].
    exists c. split; [|exact Hh].
    eapply evstep_trans; [apply progress_evstep; apply H_topc; [exact E|exact H2|exact HI]|exact Hc].
  - destruct (even_form r E H2) as [m Hm]. destruct HI as [Ha3 HI]. rewrite carryP_e2 in HP by exact E.
    assert (Hd : r / 2 = m + 1) by (apply dv; lia).
    destruct (IH q (a + r / 2 - 2) ((r / 2 + 2) :: rr) P ltac:(lia) HI HP (ex_intro _ k Hk)) as [c [Hc Hh]].
    exists c. split; [|exact Hh].
    eapply evstep_trans; [apply progress_evstep; apply H_even; [exact E|exact H2|exact Ha3]|exact Hc].
Qed.

Lemma C_halt s : Inv s -> hit s -> exists c, C s -[ tm ]->* c /\ halted tm c.
Proof.
  intros [HI HL] [P [HP Hw]]. destruct s as [|x [|q t]]; simpl in HL; try lia.
  destruct HI as [Hx HI]. cbn [topP] in HP.
  destruct (casc_halt t q (x + 2) tail0 P ltac:(lia) HI HP Hw) as [c [Hc Hh]].
  exists c. split; [|exact Hh].
  eapply evstep_trans; [apply progress_evstep; apply H_tail; exact Hx|exact Hc].
Qed.

Lemma Inv_s0 : Inv s0.
Proof. unfold Inv, s0. simpl. lia. Qed.

Lemma hit_dec s : {hit s} + {~ hit s}.
Proof.
  destruct (topP s) as [P|] eqn:E.
  - destruct (pw_dec P) as [W|W].
    + left. exists P. split; assumption.
    + right. intros [P' [HP Hw]]. rewrite E in HP. injection HP as <-. exact (W Hw).
  - right. intros [P' [HP Hw]]. rewrite E in HP. discriminate.
Qed.

Lemma reach_hit n : forall s, Inv s -> hit (Nat.iter n step s) ->
  exists c, C s -[ tm ]->* c /\ halted tm c.
Proof.
  induction n as [|n IH]; intros s HI Hh.
  - apply C_halt; assumption.
  - destruct (hit_dec s) as [H|H]; [apply C_halt; assumption|].
    assert (Hn : forall P, topP s = Some P -> ~ pw P).
    { intros P HP Hw. apply H. exists P. split; assumption. }
    rewrite Nat.iter_succ_r in Hh.
    destruct (IH (step s) (Inv_step s HI Hn) Hh) as [c [Hc Hhc]].
    exists c. split; [|exact Hhc].
    eapply evstep_trans; [apply progress_evstep; apply C_step; assumption|exact Hc].
Qed.

Lemma search k : forall s, Inv s -> halts_in tm (C s) k -> exists n, hit (Nat.iter n step s).
Proof.
  induction k using strong_induction. intros s HI Hk.
  destruct (hit_dec s) as [Hh|Hh]; [exists 0; exact Hh|].
  assert (Hn : forall P, topP s = Some P -> ~ pw P).
  { intros P HP Hw. apply Hh. exists P. split; assumption. }
  pose proof (C_step s HI Hn) as Hst.
  apply progress_multistep in Hst as [m Hm].
  destruct (Nat.leb_spec (S m) k).
  - assert (Hk' : halts_in tm (C (step s)) (k - S m)) by eauto using preceeds_halt.
    destruct (H (k - S m) ltac:(lia) (step s) (Inv_step s HI Hn) Hk') as [n Hn'].
    exists (S n). rewrite Nat.iter_succ_r. exact Hn'.
  - exfalso. eauto using exceeds_halt.
Qed.

(** The exact map: until a hit, the machine passes through the tape of every stack of the orbit, in order. *)
Theorem reach_orbit n : (forall k, k < n -> ~ hit (orbit k)) -> Inv (orbit n) /\ c0 -[ tm ]->+ C (orbit n).
Proof.
  induction n as [|n IH]; intros H.
  - split; [exact Inv_s0|exact H_start].
  - destruct IH as [HI Hr]; [intros k Hk; apply H; lia|].
    assert (Hn : forall P, topP (orbit n) = Some P -> ~ pw P).
    { intros P HP Hw. apply (H n ltac:(lia)). exists P. split; assumption. }
    change (orbit (S n)) with (step (orbit n)). split.
    + apply Inv_step; assumption.
    + eapply progress_trans; [exact Hr|apply C_step; assumption].
Qed.

Theorem generic_main : halts tm c0 <-> exists n, hit (orbit n).
Proof.
  split.
  - intros [k Hk].
    apply progress_multistep in H_start as [m Hm].
    destruct (Nat.leb_spec (S m) k).
    + exact (search (k - S m) s0 Inv_s0 ltac:(eauto using preceeds_halt)).
    + exfalso. eauto using exceeds_halt.
  - intros [n Hn].
    destruct (reach_hit n s0 Inv_s0 Hn) as [c [Hc Hhc]].
    assert (Hev : c0 -[ tm ]->* c).
    { eapply evstep_trans; [apply progress_evstep; exact H_start|exact Hc]. }
    destruct (with_counter Hev) as [k Hk].
    exists k. exists c. split; assumption.
Qed.
End Generic.
