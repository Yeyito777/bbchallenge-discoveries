From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z306 XCuts.b306 XCuts.z307 XCuts.b307 XCuts.n306 XCuts.v306 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
