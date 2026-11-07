From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z121 XCuts.b121 XCuts.z122 XCuts.b122 XCuts.n121 XCuts.v121 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
