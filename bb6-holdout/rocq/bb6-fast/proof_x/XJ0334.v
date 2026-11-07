From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z334 XCuts.b334 XCuts.z335 XCuts.b335 XCuts.n334 XCuts.v334 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
