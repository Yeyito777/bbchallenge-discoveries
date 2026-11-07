From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z556 XCuts.b556 XCuts.z557 XCuts.b557 XCuts.n556 XCuts.v556 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
