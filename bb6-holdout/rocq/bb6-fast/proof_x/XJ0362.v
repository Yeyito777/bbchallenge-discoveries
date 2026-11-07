From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z362 XCuts.b362 XCuts.z363 XCuts.b363 XCuts.n362 XCuts.v362 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
