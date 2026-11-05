Require Import List.
From BBminus2x4 Require Import BBminus2x4_Statement TM Deciders_Common Verifier_ClosedAut.
Require Import TestCerts.
Time Eval vm_compute in (map (fun p => match closed_aut_decider (snd p) (fst p) with Result_NonHalt => true | _ => false end) aut_certs).
