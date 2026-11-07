From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z59 XCuts.b59 XCuts.z60 XCuts.b60 XCuts.n59 XCuts.v59 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
