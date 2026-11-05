(* the 64 shard lemmas together *)
From Coq Require Import List.
Import ListNotations.
From WangTiles Require Import Wang_Checker.
From WangTiles.n7 Require Import Wang7_Prefixes Certs7 Check7_s000 Check7_s001 Check7_s002 Check7_s003 Check7_s004 Check7_s005 Check7_s006 Check7_s007 Check7_s008 Check7_s009 Check7_s010 Check7_s011 Check7_s012 Check7_s013 Check7_s014 Check7_s015 Check7_s016 Check7_s017 Check7_s018 Check7_s019 Check7_s020 Check7_s021 Check7_s022 Check7_s023 Check7_s024 Check7_s025 Check7_s026 Check7_s027 Check7_s028 Check7_s029 Check7_s030 Check7_s031 Check7_s032 Check7_s033 Check7_s034 Check7_s035 Check7_s036 Check7_s037 Check7_s038 Check7_s039 Check7_s040 Check7_s041 Check7_s042 Check7_s043 Check7_s044 Check7_s045 Check7_s046 Check7_s047 Check7_s048 Check7_s049 Check7_s050 Check7_s051 Check7_s052 Check7_s053 Check7_s054 Check7_s055 Check7_s056 Check7_s057 Check7_s058 Check7_s059 Check7_s060 Check7_s061 Check7_s062 Check7_s063.

Lemma checks7 : forall c, In c certs7 -> check refs7 c = true.
Proof.
  intros c Hc. unfold certs7 in Hc.
  destruct Hc as [<-|Hc]; [exact shard7_s000_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s001_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s002_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s003_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s004_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s005_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s006_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s007_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s008_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s009_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s010_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s011_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s012_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s013_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s014_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s015_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s016_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s017_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s018_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s019_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s020_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s021_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s022_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s023_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s024_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s025_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s026_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s027_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s028_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s029_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s030_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s031_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s032_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s033_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s034_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s035_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s036_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s037_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s038_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s039_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s040_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s041_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s042_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s043_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s044_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s045_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s046_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s047_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s048_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s049_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s050_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s051_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s052_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s053_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s054_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s055_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s056_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s057_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s058_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s059_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s060_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s061_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s062_ok|].
  destruct Hc as [<-|Hc]; [exact shard7_s063_ok|].
  destruct Hc.
Qed.
