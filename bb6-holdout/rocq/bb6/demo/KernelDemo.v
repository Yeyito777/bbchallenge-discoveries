(** One chunk of the chain, checked inside the Rocq kernel by native_compute: no extraction, no OCaml of ours.
    The chunk is the first 2^24 phases of the orbit, from A(6,1). The totals are what the extracted checker prints. *)
From Coq Require Import ZArith Uint63.
From BB6 Require Import Num Vec Map Big Check.

Definition B0 : W := mkW 0 1.
Definition Y0 : W := mkW 0 20345673609576897.
Definition n0 : W := mkW 0 6129742349388793.
Definition acc0 : V := mkV 4346765498079327054 7676994991155174933 472287747 0 0.

Lemma chunk0 : check_seg false B0 false Y0 = Some (n0, acc0).
Proof. native_cast_no_check (eq_refl (Some (n0, acc0))). Time Qed.

Theorem chunk0_reach : exists R, Reach 6 1 6 20345673609576897 6129742349388793 R /\ cong PM (vval acc0) R.
Proof. exact (check_seg_sound _ _ _ _ _ _ chunk0). Qed.
Print Assumptions chunk0_reach.
