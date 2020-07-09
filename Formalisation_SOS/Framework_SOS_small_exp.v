Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
(*From PLF Require Import Maps.
From PLF Require Import Imp.*)


Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x: string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
  
Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Definition total_map (A : Type) := string -> A.  
Definition state := total_map nat.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
 Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Definition empty_state := (_ !-> 0).
Notation "x '!->' v ',' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).
Notation "x '!->' v" := (x!->v,empty_state)
                              (at level 100, v at next level, right associativity).
  
Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.
  
Fixpoint beval (st:state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.


(** that one is nice **)
Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.


Inductive statement : Type :=
  | SSkip
  | SAss (x : string) (a : aexp)
  | SComp (c1 c2 : statement)
  | SIf (b : bexp) (c1 c2 : statement)
  | SWhile (b : bexp) (c : statement).
  
  
  
Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).


Reserved Notation "'A[[' a ']]' st '-->a' a' "
                  (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Num: forall st n,
     A[[n]] st -->a n
  | AS_Id : forall st i,
      A[[AId i]] st -->a ANum (st i)
  | AS_Plus1 : forall st a1 a1' a2,
      (A[[a1]] st -->a a1') ->
      (A[[APlus a1 a2]] st -->a (APlus a1' a2))
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      A[[a2]] st -->a a2' ->
      A[[APlus v1 a2]] st -->a (APlus v1 a2')
  | AS_Plus : forall st n1 n2,
      A[[APlus (ANum n1) (ANum n2)]] st -->a ANum (n1 + n2)
  | AS_Minus1 : forall st a1 a1' a2,
      A[[a1]] st -->a a1' ->
      A[[(AMinus a1 a2)]] st -->a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      A[[a2]] st -->a a2' ->
      A[[(AMinus v1 a2)]] st -->a (AMinus v1 a2')
  | AS_Minus : forall st n1 n2,
      A[[AMinus (ANum n1) (ANum n2)]] st -->a (ANum (minus n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      A[[a1]] st -->a a1' ->
      A[[AMult a1 a2]] st -->a (AMult a1' a2)
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      A[[a2]] st -->a a2' ->
      A[[AMult v1 a2]] st -->a (AMult v1 a2')
  | AS_Mult : forall st n1 n2,
      A[[AMult (ANum n1) (ANum n2)]] st -->a (ANum (mult n1 n2))

    where "'A[[' a ']]' st '-->a' a' " := (astep st a a').

Reserved Notation "'B[[' t ']]' st '-->b' t' "
                  (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq1 : forall st a1 a1' a2,
    A[[a1]] st -->a a1' ->
    B[[BEq a1 a2]] st -->b (BEq a1' a2)
| BS_Eq2 : forall st v1 a2 a2',
    aval v1 ->
    A[[a2]] st -->a a2' ->
    B[[BEq v1 a2]] st -->b (BEq v1 a2')
| BS_Eq : forall st n1 n2,
    B[[BEq (ANum n1) (ANum n2)]] st -->b
    (if (n1 =? n2) then BTrue else BFalse)
| BS_LtEq1 : forall st a1 a1' a2,
   A[[a1]] st -->a a1' ->
    B[[BLe a1 a2]] st -->b (BLe a1' a2)
| BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    A[[a2]] st -->a a2' ->
    B[[BLe v1 a2]] st -->b (BLe v1 a2')
| BS_LtEq : forall st n1 n2,
   B[[BLe (ANum n1) (ANum n2)]] st -->b
             (if (n1 <=? n2) then BTrue else BFalse)
| BS_NotStep : forall st b1 b1',
    B[[b1]] st -->b b1' ->
    B[[BNot b1]] st -->b (BNot b1')
| BS_NotTrue : forall st,
    B[[BNot BTrue]] st -->b BFalse
| BS_NotFalse : forall st,
    B[[BNot BFalse]] st -->b BTrue
| BS_AndTrueStep : forall st b2 b2',
    B[[b2]] st -->b b2' ->
    B[[BAnd BTrue b2]] st -->b (BAnd BTrue b2')
| BS_AndStep : forall st b1 b1' b2,
    B[[b1]] st -->b b1' ->
    B[[BAnd b1 b2]] st -->b (BAnd b1' b2)
| BS_AndTrueTrue : forall st,
    B[[BAnd BTrue BTrue]] st -->b BTrue
| BS_AndTrueFalse : forall st,
    B[[BAnd BTrue BFalse]] st -->b BFalse
| BS_AndFalse : forall st b2,
    B[[BAnd BFalse b2]] st -->b BFalse

where "'B[[' t ']]' st '-->b' t' " := (bstep st t t').


Notation "x + y" := (APlus x y) (at level 50, left associativity) (*: while_scope*).
Notation "x - y" := (AMinus x y) (at level 50, left associativity) (*: while_scope*).
Notation "x * y" := (AMult x y) (at level 40, left associativity) (*: while_scope*).
Notation "x <= y" := (BLe x y) (at level 70, no associativity) (*: while_scope*).
Notation "x = y" := (BEq x y) (at level 70, no associativity) (*: while_scope*).
Notation "x && y" := (BAnd x y) (at level 40, left associativity) (*: while_scope*).
Notation "'~' b" := (BNot b) (at level 75, right associativity) (*: while_scope*).


Inductive Config: Type :=
|Running (S:statement) (s:state)
|Final (s:state).

Coercion Final: state >-> Config.
Notation "'<<' s '>>' " := (Final s).
Notation "'<<' S ',,' st '>>'" := (Running S st).

Notation "x '::=' a" :=
  (SAss x a) (at level 60).
Notation "'SKIP'" :=
   SSkip.
Notation "s1 ; s2" := 
  (SComp s1 s2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' s 'END'" :=
  (SWhile b s) (at level 80, right associativity).
Notation "'IFS' b 'THEN' s1 'ELSE' s2 " := 
  (SIf b s1 s2) (at level 80, right associativity).



Reserved Notation " conf '-->' conf' "
                  (at level 40). (*levels?*)

Inductive sstep : Config -> Config -> Prop:=
|SSSkip : forall  st,
  <<SKIP,, st>> --> st

|SSAss: forall x a n st,
    A[[a]]st -->a (ANum n) ->
    <<(x::=a),, st>> --> Final (x !-> n, st)(*t_update st x n)*)

(*don't forget - a derivation tree is written bottom up but read top-down. 
This is reading*)
|SSCompI: forall S1 S1' S2 st st',
  <<S1,, st>> --> <<S1',, st'>> ->
    <<S1; S2,, st>> --> <<S1'; S2,, st'>>

|SSCompII:  forall S1  S2 st st',
  <<S1,, st>> --> Final st' ->
  <<S1;S2,, st>> --> <<S2,, st'>>
  
|SSIftrue: forall b S1 S2 st,
  B[[b]]st -->b BTrue ->
  <<IFS b THEN S1 ELSE S2,, st>> --> <<S1,, st>>

|SSIffalse: forall b S1 S2 st,
  B[[b]]st -->b BFalse ->
  <<IFS b THEN S1 ELSE S2,, st>> --> <<S2,, st>>
  
|SSWhile: forall b S st,
  <<WHILE b DO S END,, st>> --> <<IFS b THEN (S; WHILE b DO S END) ELSE SKIP,, st>>
  where " conf '-->' conf' " := (sstep conf conf').
(*  
Pierce indeed uses those, and it seemed like an intersting idea to try them out,
 but coudl not get them to work, as I need to state exacly which constructors of 
 a/b exp I use in the proofs. Leaving them here, to write a bit about them.
|SSAssStep : forall x a a' st,
    A[[a]]st -->a a' ->
    <<(x::=a),, st>> --> <<(x::=a'),, st>>
|SSIfStep: forall b b' S1 S2 st,
  B[[b]]st -->b b' ->
  <<IFS b THEN S1 ELSE S2,, st>> --> <<IFS b' THEN S1 ELSE S2,, st>> 
    where " conf '-->' conf' " := (sstep conf conf').*)

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
                    
Notation " t '-->*' t' " := (multi sstep t t') (at level 40).


(*Exersises are started here for now, in case we need to add notations 
or tweaks, and it is annoying to recommpile every time.*)
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".


