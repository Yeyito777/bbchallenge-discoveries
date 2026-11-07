From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z425 XCuts.b425 XCuts.z426 XCuts.b426 XCuts.n425 XCuts.v425 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
