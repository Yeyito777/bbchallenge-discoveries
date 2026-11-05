(* Exploration only, not part of the proof: extracts the TNF enumeration on 110[1]011 with the current
   decider pipeline to OCaml, counting decisions per decider and printing the machines left undecided. *)
From BBminus2x4 Require Import TNF BBminus2x4_Statement BB2x4_Deciders_Generic BB2x4_Deciders_Pipeline TM BB2x4_Make_TM.
From BBminus2x4 Require Import Deciders_Common.
Require Import Extraction.
Require Import ExtrOcamlBasic ExtrOcamlNatInt.

Definition TM0: TM Σ := fun x i => None.
Definition root := {| TNF_tm:=TM0; TNF_cnt:=CountHaltTrans (TM0); TNF_ptr:=St1 |}.

Definition step_all (q:SearchQueue) : SearchQueue := SearchQueue_upds q decider_all 14.

Definition unmakeTM (f:TM Σ) :=
  (f St0 Σ0, f St0 Σ1, f St0 Σ2, f St0 Σ3, f St1 Σ0, f St1 Σ1, f St1 Σ2, f St1 Σ3).

Extract Constant node_halt => "fun h d a -> Stats.halt (Obj.magic h) (Obj.magic d); a".
Extract Constant node_nonhalt => "fun h d a -> Stats.nonhalt (Obj.magic h) (Obj.magic d); a".

Definition children := TNF_Node_expand root St0 Σ1.

Extraction "explore_out.ml" root children step_all unmakeTM TNF_tm.
