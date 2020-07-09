(* First, we need some imports from the Coq library *)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import BinNat.
Require Import Framework_common.
Import ListNotations.

(* Open Z scope, needed for Num *)
Local Open Scope Z_scope.
Open Scope while_scope.

(* semantics Stm and notation for transitions *)
Reserved Notation "conf '-->' st'"
                  (at level 40).

Inductive Seval : Config -> State -> Prop :=
  | ass_ns  : forall st a1 n x,
      Aeval st a1 = n ->
      Seval (Running (x ::= a1) st) (t_update st x n)
  | skip_ns : forall st,
      Seval (Running SKIP st) st
  | comp_ns : forall s1 s2 st st' st'',
      Seval (Running s1 st) st' ->
      Seval (Running s2 st') st'' ->
      Seval (Running (s1;s2) st) st''
  | if_tt_ns : forall st st' b s1 s2,
      Beval st b = true ->
      Seval (Running s1 st) st' ->
      Seval (Running (IF_ b THEN s1 ELSE s2) st) st'
  | if_ff_ns : forall st st' b s1 s2,
      Beval st b = false ->
      Seval (Running s2 st) st' ->
      Seval (Running (IF_ b THEN s1 ELSE s2) st) st'
  | while_tt_ns : forall st st' st'' b s,
      Beval st b = true ->
      Seval (Running s st) st' ->
      Seval (Running (WHILE b DO s) st') st'' ->
      Seval (Running (WHILE b DO s) st) st''
  | while_ff_ns : forall b st s,
      Beval st b = false ->
      Seval (Running (WHILE b DO s) st) st.

Notation "conf '-->' st'" := (Seval conf st')
                                   (at level 40).

(* Semantic Equivalence *)
Definition Aequiv (a1 a2 : Aexp) : Prop :=
  forall (st : State),
    Aeval st a1 = Aeval st a2.

Definition Bequiv (b1 b2 : Bexp) : Prop :=
  forall (st : State),
    Beval st b1 = Beval st b2.

Definition Sequiv (S1 S2 : Stm) : Prop :=
  forall (st st' : State),
    Seval (Running S1 st) st' <-> Seval (Running S2 st) st'.

Theorem ExampleSkip : forall (S:Stm),
  Sequiv
    (SKIP; S) 
    (SKIP; SKIP; S).
Proof.
  Admitted.