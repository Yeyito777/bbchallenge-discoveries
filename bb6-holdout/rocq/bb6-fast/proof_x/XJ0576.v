From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z576 XCuts.b576 XCuts.z577 XCuts.b577 XCuts.n576 XCuts.v576 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
