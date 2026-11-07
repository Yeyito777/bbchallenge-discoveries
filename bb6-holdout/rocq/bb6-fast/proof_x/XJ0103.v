From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z103 XCuts.b103 XCuts.z104 XCuts.b104 XCuts.n103 XCuts.v103 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
