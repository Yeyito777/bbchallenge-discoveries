From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z501 XCuts.b501 XCuts.z502 XCuts.b502 XCuts.n501 XCuts.v501 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
