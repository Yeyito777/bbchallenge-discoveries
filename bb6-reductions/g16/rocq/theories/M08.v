(** 1RB---_0RC1RB_1LC1RD_1RA0LE_1RB0LF_0RD1LF *)
From Coq Require Import List Lia String.
From BusyCoq Require Import Individual62.
From G16 Require Import Spec Tape Generic Fam2.
Import ListNotations.
Open Scope list.
Open Scope sym.

Definition tm0 := TM_from_str "1RB---_0RC1RB_1LC1RD_1RA0LE_1RB0LF_0RD1LF".
Definition tm := Eval compute in tm0.
Notation "'fS'" := F (only parsing).
Notation "'aS'" := B (only parsing).

Lemma WRa : forall n l r, l {{aS}}> [1]^^n *> r -[ tm ]->* ([1]^^n *> l) {{aS}}> r.
Proof. apply WR. reflexivity. Qed.
Lemma WLf : forall n l r, ([1]^^n *> l) <{{fS}} r -[ tm ]->* l <{{fS}} [1]^^n *> r.
Proof. apply WL. reflexivity. Qed.

Ltac wk := first [ eapply evstep_trans; [apply WRa|]; simpl_tape; nz
                 | eapply evstep_trans; [apply WLf|]; simpl_tape; nz ].
Ltac st := eapply evstep_step; [prove_step|simpl_tape; nz].
Ltac run := repeat (try solve [cfin]; first [st | wk]).
Ltac go := unfold cfg, AP, LSc, Cc; intros; cbn [RS tail0 s0]; eapply progress_intro; [prove_step|simpl_tape; nz]; run.

Lemma R_round lx p n y rx : cfg fS lx p (S (S n)) y rx -[ tm ]->+ cfg fS lx (S p) n (S y) rx.
Proof. go. Qed.
Lemma R_even q lx p y rx : cfg fS (0 >> [1]^^q *> lx) (S p) 0 y rx -[ tm ]->+ cfg fS lx q p 1 (0 >> [1]^^y *> rx).
Proof. go. Qed.
Lemma R_odd lx p y rx : cfg fS lx p 1 y rx -[ tm ]->+ AP aS (y + 3) (0 >> [1]^^(S p) *> lx) rx.
Proof. go. Qed.
Lemma R_cross cur lx e rx : AP aS cur lx (0 >> [1]^^(S (S e)) *> rx) -[ tm ]->+ AP aS (S (S e)) (0 >> [1]^^cur *> lx) rx.
Proof. go. Qed.
Lemma R_tail x q lx : AP aS 2 (0 >> [1]^^4 *> 0 >> [1]^^6 *> 0 >> [1]^^(S (S (S x))) *> 0 >> [1]^^q *> lx) (const 0)
    -[ tm ]->+ cfg fS lx q (x + 7) 1 (RS tail0).
Proof. go. Qed.
Lemma R_top p y rx : cfg fS (const 0) (S p) 0 y rx -[ tm ]->+ LSc fS (S p) (0 >> [1]^^y *> rx).
Proof. go. Qed.
Lemma R_ls n rx : LSc fS (S (S (S (S n)))) rx -[ tm ]->+ cfg fS (const 0) 1 (S n) 2 rx.
Proof. go. Qed.
Lemma R_ls1 rx : LSc fS 2 rx -[ tm ]->+ AP aS 4 (RS (1%nat :: nil)) rx.
Proof. go. Qed.
Lemma R_ls2 rx : exists c, LSc fS 3 rx -[ tm ]->* c /\ halted tm c.
Proof.
  unfold LSc. eexists. split; [repeat (first [st | wk]); apply evstep_refl|reflexivity].
Qed.
Lemma R_start : c0 -[ tm ]->+ Cc aS 2 s0.
Proof.
  unfold c0, tape0, Cc. cbn [RS s0]. eapply progress_intro; [prove_step|simpl_tape; nz]. run.
Qed.

Theorem main_tm : halts tm c0 <-> exists n, hit (orbit n).
Proof.
  exact (fam2_main tm fS aS R_round R_even R_odd R_cross R_tail R_top R_ls R_ls1 R_ls2 R_start).
Qed.

Theorem main_M08 : halts (TM_from_str "1RB---_0RC1RB_1LC1RD_1RA0LE_1RB0LF_0RD1LF") c0 <-> exists n, hit (orbit n).
Proof.
  exact main_tm.
Qed.

Theorem map_M08 n : (forall k, (k < n)%nat -> ~ hit (orbit k)) -> c0 -[ tm ]->+ Cc aS 2 (orbit n).
Proof.
  exact (fam2_map tm fS aS R_round R_even R_odd R_cross R_tail R_top R_ls R_ls1 R_start n).
Qed.
