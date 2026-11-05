Require Import List.
From BBminus2x4 Require Import TNF TNF_Common.
Time Eval native_compute in (length (snd (Nat.iter 4000 q_suc (SearchQueue_init (nth 1 root_children root))))).
