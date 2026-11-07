From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z429 XCuts.b429 XCuts.z430 XCuts.b430 XCuts.n429 XCuts.v429 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
