(* Exploration only: extracts single deciders to try parameters on undecided machines. *)
From BBminus2x4 Require Import BBminus2x4_Statement TM Deciders_Common Decider_Loop Decider_NGramCPS Decider_RepWL Decider_Halt.
Require Import Extraction.
Require Import ExtrOcamlBasic ExtrOcamlNatInt.
Extraction "decx.ml" loop1_decider NGramCPS_decider_impl1 NGramCPS_decider_impl2 NGramCPS_LRU_decider RepWL_ES_decider halt_decider.
