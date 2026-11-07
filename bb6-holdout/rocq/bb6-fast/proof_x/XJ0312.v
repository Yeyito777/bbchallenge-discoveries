From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z312 XCuts.b312 XCuts.z313 XCuts.b313 XCuts.n312 XCuts.v312 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
