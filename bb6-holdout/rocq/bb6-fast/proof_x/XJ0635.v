From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z635 XCuts.b635 XCuts.z636 XCuts.b636 XCuts.n635 XCuts.v635 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
