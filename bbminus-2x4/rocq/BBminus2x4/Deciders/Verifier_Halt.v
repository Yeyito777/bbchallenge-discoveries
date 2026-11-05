From BBminus2x4 Require Import Tactics.
From BBminus2x4 Require Import BBminus2x4_Statement.
From BBminus2x4 Require Import List_Tape.
From BBminus2x4 Require Import TM.

(** Checks that `tm` started on `es` reaches an undefined transition after exactly `n` steps.
  (Coq-BB5's version starts on the blank tape; here the start `ListES` is a parameter.) *)
Definition halt_time_verifier(tm:TM Σ)(n:nat)(es:ListES):bool :=
  match ListES_Steps tm n es with
  | Some {| List_Tape.l:=_; List_Tape.r:=_; List_Tape.m :=m0; List_Tape.s :=s0 |} =>
    match tm s0 m0 with
    | None => true
    | _ => false
    end
  | None => false
  end.

Lemma halt_time_verifier_spec tm n es:
  halt_time_verifier tm n es = true ->
  HaltsAt _ tm n (ListES_toES es).
Proof.
  unfold halt_time_verifier,HaltsAt.
  intro H.
  pose proof (ListES_Steps_spec tm n es).
  destruct (ListES_Steps tm n es).
  2: cg.
  eexists.
  split.
  - apply H0.
  - destruct l as [l0 r0 m0 s0].
    cbn.
    destruct (tm s0 m0); cg.
Qed.
