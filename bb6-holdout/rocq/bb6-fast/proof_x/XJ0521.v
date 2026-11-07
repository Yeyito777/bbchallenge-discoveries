From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z521 XCuts.b521 XCuts.z522 XCuts.b522 XCuts.n521 XCuts.v521 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
