From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z551 XCuts.b551 XCuts.z552 XCuts.b552 XCuts.n551 XCuts.v551 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
