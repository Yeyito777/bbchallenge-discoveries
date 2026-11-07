From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z248 XCuts.b248 XCuts.z249 XCuts.b249 XCuts.n248 XCuts.v248 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
