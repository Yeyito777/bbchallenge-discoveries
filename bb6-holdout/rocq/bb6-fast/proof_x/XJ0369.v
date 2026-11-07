From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z369 XCuts.b369 XCuts.z370 XCuts.b370 XCuts.n369 XCuts.v369 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
