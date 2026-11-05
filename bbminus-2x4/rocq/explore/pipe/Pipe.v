(* Exploration only: TNF search with a pipeline assembled at run time (OCaml side). *)
From BBminus2x4 Require Import TNF BBminus2x4_Statement BB2x4_Deciders_Generic TM BB2x4_Make_TM.
From BBminus2x4 Require Import Deciders_Common Decider_Loop Decider_NGramCPS Decider_RepWL Decider_Halt.
Require Import Extraction.
Require Import ExtrOcamlBasic ExtrOcamlNatInt.
Definition TM0: TM Σ := fun x i => None.
Definition root := {| TNF_tm:=TM0; TNF_cnt:=CountHaltTrans (TM0); TNF_ptr:=St1 |}.
Definition children := TNF_Node_expand root St0 Σ1.
Definition unmakeTM (f:TM Σ) :=
  (f St0 Σ0, f St0 Σ1, f St0 Σ2, f St0 Σ3, f St1 Σ0, f St1 Σ1, f St1 Σ2, f St1 Σ3).
Extract Constant node_halt => "fun h d a -> Stats.halt (Obj.magic h) (Obj.magic d); a".
Extract Constant node_nonhalt => "fun h d a -> Stats.nonhalt (Obj.magic h) (Obj.magic d); a".
Extraction "pipe_out.ml" root children SearchQueue_upds HaltDecider_list unmakeTM TNF_tm TNF_Node_expand
  loop1_decider NGramCPS_decider_impl1 NGramCPS_decider_impl2 NGramCPS_LRU_decider RepWL_ES_decider halt_decider.
