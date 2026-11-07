From H Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
From H.jobs Require J0521 J0522.
(* two-link chain from checkpoint 521: tests the composition the full Chain.v uses *)
Lemma test_chain : chain 296346816884503 1 25878808081107.
Proof. exact (ch_step _ _ _ _ _ _ _ J0521.J0521 (ch_halt _ _ _ _ J0522.J0522)). Qed.
Print Assumptions test_chain.
