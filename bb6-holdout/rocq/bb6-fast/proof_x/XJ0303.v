From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z303 XCuts.b303 XCuts.z304 XCuts.b304 XCuts.n303 XCuts.v303 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
