Set warnings "-notation-overridden,-parsing".
Require Import Framework_common.
Require Import Framework_SOS.
From Coq Require Import BinNat.
From Coq Require Import omega.Omega.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Bool.Bool.

Definition is_final (conf:Config) :=
  exists s, conf = Final s.

Theorem strong_progress:
forall conf:Config,
 is_final conf
 \/
 (exists conf', conf ==> conf').
Proof.
intro.
induction conf.
- right. induction S.
  + eexists. apply SSAss. reflexivity.
  + eexists. apply SSSkip. 
  + inversion IHS1. induction x.
    * exists <<S; S2,s0>>. apply SSCompI. assumption.                           
    * exists <<S2, s0>>. apply SSCompII. assumption.
  + assert (Beval s b = true \/ Beval s b = false).
    { induction (B[[b]]s). 
      - left. reflexivity.
      - right. reflexivity.
    }
   destruct H.
    * exists <<S1,s>>. apply SSIftrue. assumption.
    * exists <<S2,s>>. apply SSIffalse. assumption.
  + exists <<IF_ b THEN (S; WHILE b DO S) ELSE SKIP,s>>. apply SSWhile. 
- left. unfold is_final. exists s. reflexivity.
Qed.