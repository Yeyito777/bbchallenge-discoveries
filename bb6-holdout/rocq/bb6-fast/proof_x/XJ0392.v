From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z392 XCuts.b392 XCuts.z393 XCuts.b393 XCuts.n392 XCuts.v392 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
