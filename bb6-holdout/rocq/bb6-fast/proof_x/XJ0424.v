From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z424 XCuts.b424 XCuts.z425 XCuts.b425 XCuts.n424 XCuts.v424 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
