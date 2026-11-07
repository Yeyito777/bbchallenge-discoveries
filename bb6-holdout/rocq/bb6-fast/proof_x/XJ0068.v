From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z68 XCuts.b68 XCuts.z69 XCuts.b69 XCuts.n68 XCuts.v68 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
