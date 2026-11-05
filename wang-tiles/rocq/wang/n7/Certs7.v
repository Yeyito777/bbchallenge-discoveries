(* the 64 shard certificates of n = 7 in one list *)
From Coq Require Import List.
Import ListNotations.
From WangTiles Require Import Wang_Checker.
From WangTiles.n7 Require Import Cert7_s000 Cert7_s001 Cert7_s002 Cert7_s003 Cert7_s004 Cert7_s005 Cert7_s006 Cert7_s007 Cert7_s008 Cert7_s009 Cert7_s010 Cert7_s011 Cert7_s012 Cert7_s013 Cert7_s014 Cert7_s015 Cert7_s016 Cert7_s017 Cert7_s018 Cert7_s019 Cert7_s020 Cert7_s021 Cert7_s022 Cert7_s023 Cert7_s024 Cert7_s025 Cert7_s026 Cert7_s027 Cert7_s028 Cert7_s029 Cert7_s030 Cert7_s031 Cert7_s032 Cert7_s033 Cert7_s034 Cert7_s035 Cert7_s036 Cert7_s037 Cert7_s038 Cert7_s039 Cert7_s040 Cert7_s041 Cert7_s042 Cert7_s043 Cert7_s044 Cert7_s045 Cert7_s046 Cert7_s047 Cert7_s048 Cert7_s049 Cert7_s050 Cert7_s051 Cert7_s052 Cert7_s053 Cert7_s054 Cert7_s055 Cert7_s056 Cert7_s057 Cert7_s058 Cert7_s059 Cert7_s060 Cert7_s061 Cert7_s062 Cert7_s063.

Definition certs7 : list cert := [cert7_s000; cert7_s001; cert7_s002; cert7_s003; cert7_s004; cert7_s005; cert7_s006; cert7_s007; cert7_s008; cert7_s009; cert7_s010; cert7_s011; cert7_s012; cert7_s013; cert7_s014; cert7_s015; cert7_s016; cert7_s017; cert7_s018; cert7_s019; cert7_s020; cert7_s021; cert7_s022; cert7_s023; cert7_s024; cert7_s025; cert7_s026; cert7_s027; cert7_s028; cert7_s029; cert7_s030; cert7_s031; cert7_s032; cert7_s033; cert7_s034; cert7_s035; cert7_s036; cert7_s037; cert7_s038; cert7_s039; cert7_s040; cert7_s041; cert7_s042; cert7_s043; cert7_s044; cert7_s045; cert7_s046; cert7_s047; cert7_s048; cert7_s049; cert7_s050; cert7_s051; cert7_s052; cert7_s053; cert7_s054; cert7_s055; cert7_s056; cert7_s057; cert7_s058; cert7_s059; cert7_s060; cert7_s061; cert7_s062; cert7_s063].

Lemma certs7_length : length certs7 = 64. Proof. reflexivity. Qed.
Lemma certs7_shards : map c_shard certs7 = seq 0 64. Proof. reflexivity. Qed.
Lemma certs7_params : Forall (fun c => c_n c = 7 /\ c_D c = 17 /\ c_reset c = 10 /\ c_shards c = 64) certs7.
Proof. repeat constructor. Qed.
