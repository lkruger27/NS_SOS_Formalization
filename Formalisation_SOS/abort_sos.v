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
Import ListNotations.

(* Open Z scope, needed for Num *)
Local Open Scope Z_scope.
Declare Scope while_scope.
Open Scope while_scope.

(*Num *)
Inductive Num : Type :=
  | NZero
  | NOne
  | NEven (n : Num)
  | NOdd (n : Num).

Fixpoint Neval (n : Num) : Z :=
  match n with
  | NZero => 0
  | NOne => 1
  | NEven n => 2*(Neval n)
  | NOdd n => 2*(Neval n) + 1
  end.

Coercion Neval: Num >-> Z.

Print Z.
Print positive.
Compute (xH).
 
 Fixpoint pos_to_num (n:positive): Num:=
 match n with
  |xH => NOne
  |xO n' => NEven (pos_to_num n')
  |xI n' => NOdd (pos_to_num n')
  end.
  
 Fixpoint z_to_num (z:Z) : Num :=
  match z with
   | Z0 => NZero
   | Zpos n => pos_to_num n
   | Zneg n => pos_to_num n
   end.
   
Compute (z_to_num 0).
   
Coercion z_to_num: Z >-> Num.   
   
(*State*)
Definition total_map (A : Type) := string -> A.  
Definition State := total_map Z.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
 Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Definition empty_State := (_ !-> 0).
Notation "x '!->' v ',' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).
Notation "x '!->' v" := (x!->v,empty_State)
                              (at level 100, v at next level, right associativity).
  
(* Aexp*)
Inductive Aexp : Type :=
  | ANum (n : Num)
(*  | ANum (n : Z)*)
  | AId (x : string)
  | APlus (a1 a2 : Aexp)
  | AMinus (a1 a2 : Aexp)
  | AMult (a1 a2 : Aexp).

(* Semantics Aexp *)
Fixpoint Aeval (st : State) (a : Aexp) : Z :=
  match a with
  | ANum n => Neval n
  (*| ANum n => n*)
  | AId x => st x
  | APlus a1 a2 => (Aeval st a1) + (Aeval st a2)
  | AMinus a1 a2  => (Aeval st a1) - (Aeval st a2)
  | AMult a1 a2 => (Aeval st a1) * (Aeval st a2)
  end.
  
Coercion AId : string >-> Aexp.
Coercion ANum : Num >-> Aexp.
(*Coercion ANum : Z >-> Aexp.*)

  
  (* Bexp*)
Inductive Bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : Aexp)
  | BLe (a1 a2 : Aexp)
  | BNot (b : Bexp)
  | BAnd (b1 b2 : Bexp).

Fixpoint Beval (st : State) (b : Bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (Aeval st a1) =? (Aeval st a2)
  | BLe a1 a2   => (Aeval st a1) <=? (Aeval st a2)
  | BNot b1     => negb (Beval st b1)
  | BAnd b1 b2  => andb (Beval st b1) (Beval st b2)
  end.

Definition bool_to_bexp (b : bool) : Bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> Bexp.

Bind Scope while_scope with Aexp.
Bind Scope while_scope with Bexp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : while_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity): while_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity): while_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity): while_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity): while_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity): while_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity): while_scope.

Notation " 'A[[' a ']]' st " := (Aeval st a)
        (at level 90, left associativity)(*: while_scope*).
Notation " 'B[[' b ']]' st " := (Beval st b)
        (at level 90, left associativity)(*: while_scope*).
Notation " 'N[[' n ']]'" := (Neval n)
        (at level 90, left associativity)(*: while_scope*).
        
(*Statement*)
Inductive Stm : Type :=
  | ass (x : string) (a : Aexp)
  | skip
  | comp (s1 s2 : Stm)
  | if_ (b : Bexp) (s1 s2 : Stm)
  | while (b : Bexp) (s : Stm)
  | abort.

(* some notations *)

Notation "x '::=' a" :=
  (ass x a) (at level 60).
Notation "'SKIP'" :=
   skip.
Notation "s1 ; s2" := 
  (comp s1 s2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' s " :=
  (while b s) (at level 80, right associativity).
Notation "'IF_' b 'THEN' s1 'ELSE' s2 " := 
  (if_ b s1 s2) (at level 80, right associativity).

Inductive Config: Type :=
|Running (S:Stm) (s:State)
|Final (s:State)
|Stuck (s:State).

Coercion Final: State >-> Config.
Notation "'<<' s '>>' " := (Final s).
Notation "'<<' S ',' st '>>'" := (Running S st).

Definition w : string := "w".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".



Ltac eq_states :=
  apply functional_extensionality; intros; unfold t_update; simpl;
  repeat match goal with
  |- context [eqb_string ?v ?x] =>
    destruct (eqb_string v x)
  end;
  reflexivity.
Close Scope while_scope.
  
Notation "'ABORT'" := abort (at level 80, right associativity).

Reserved Notation " conf '==>' conf' "
                  (at level 99). (*levels?*)
  
  Definition is_final (conf:Config) :=
  exists s, conf = Final s.

Inductive Asstep : Config -> Config -> Prop:=
|SSSkip : forall  st,
  <<SKIP, st>> ==> st

|SSAss: forall x a n st,
    Aeval st a = n ->
    <<(x::=a), st>> ==> <<(x !-> n, st)>>(*t_update st x n)*)

(*don't forget - a derivation tree is written bottom up but read top-down. 
This is reading*)
|SSCompI: forall S1 S1' S2 st st',
  <<S1, st>> ==> <<S1', st'>> ->
    <<S1; S2, st>> ==> <<S1'; S2, st'>>

|SSCompII:  forall S1  S2 st st',
  <<S1, st>> ==> Final st' ->
  <<S1;S2, st>> ==> <<S2, st'>>
  
|SSIftrue: forall b S1 S2 st,
  Beval st b = true ->
  <<IF_ b THEN S1 ELSE S2, st>> ==> <<S1, st>>

|SSIffalse: forall b S1 S2 st,
  Beval st b=  false ->
  <<IF_ b THEN S1 ELSE S2, st>> ==> <<S2, st>>
  
|SSWhile: forall b S st,
  <<WHILE b DO S, st>> ==>
       <<IF_ b THEN (S; WHILE b DO S) ELSE SKIP, st>>
|SSAbort: forall st,
   <<ABORT, st>> ==> Stuck st

  where " conf '==>' conf' " := (Asstep conf conf').
  
Lemma no_strong_progress':
  ~forall conf:Config,
   is_final conf
   \/
   (exists conf', conf ==> conf').
Proof.
intros contra.
specialize (contra  (Stuck empty_State)).
destruct contra.
- unfold is_final in H. destruct H. inversion H.
- destruct H. induction x0.
  + inversion H.
  + inversion H.
  + inversion H; subst.
Qed.

  

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
  + inversion IHS1. induction x0.
    * exists <<S; S2,s0>>. apply SSCompI. assumption.                           
    * exists <<S2, s0>>. apply SSCompII. assumption.
    * inversion H; subst.
      eexists.
     (*Problem here - what should the step after <<ABORT;S2,s0>> be?*)
      Admitted.
  + assert (Beval s b = true \/ Beval s b = false).
    { induction (B[[b]]s). 
      - left. reflexivity.
      - right. reflexivity.
    }
   destruct H.
    * exists <<S1,s>>. apply SSIftrue. assumption.
    * exists <<S2,s>>. apply SSIffalse. assumption.
  + exists <<IF_ b THEN (S; WHILE b DO S) ELSE SKIP,s>>. apply SSWhile. 
  + exists <<s>>. apply SSAbort.
- left. unfold is_final. exists s. reflexivity.
Qed.


(*alternitively, if you could comment out the above two deifinitions*)

Inductive alt_Asstep : Config -> Config -> Prop:=
|SSSkip : forall  st,
  <<SKIP, st>> ==> st

|SSAss: forall x a n st,
    Aeval st a = n ->
    <<(x::=a), st>> ==> <<(x !-> n, st)>>(*t_update st x n)*)

(*don't forget - a derivation tree is written bottom up but read top-down. 
This is reading*)
|SSCompI: forall S1 S1' S2 st st',
  <<S1, st>> ==> <<S1', st'>> ->
    <<S1; S2, st>> ==> <<S1'; S2, st'>>

|SSCompII:  forall S1  S2 st st',
  <<S1, st>> ==> Final st' ->
  <<S1;S2, st>> ==> <<S2, st'>>
  

|SSCompIII:  forall S1  S2 st,
  <<S1, st>> ==> Stuck st ->
  <<S1;S2, st>> ==> <<st>>
|SSIftrue: forall b S1 S2 st,
  Beval st b = true ->
  <<IF_ b THEN S1 ELSE S2, st>> ==> <<S1, st>>

|SSIffalse: forall b S1 S2 st,
  Beval st b=  false ->
  <<IF_ b THEN S1 ELSE S2, st>> ==> <<S2, st>>
  
|SSWhile: forall b S st,
  <<WHILE b DO S, st>> ==>
       <<IF_ b THEN (S; WHILE b DO S) ELSE SKIP, st>>
|SSAbort: forall st,
   <<ABORT, st>> ==> Stuck st

  where " conf '==>' conf' " := (alt_Asstep conf conf').
  
Definition is_final (conf:Config) :=
  exists s, conf = Final s.

Lemma test:
~ forall P Q:Prop, P -> Q.
Proof.
  intros contra.
  specialize (contra True False). (* replace the hypothesis 
                                     by [True -> False] *)
  apply contra. (* At this point the goal becomes [True] *)
  trivial.
Qed.

Lemma no_strong_progress:
  ~forall conf:Config,
   is_final conf
   \/
   (exists conf', conf ==> conf').
Proof.
intros contra.
specialize (contra  (Stuck empty_State)).
destruct contra.
- unfold is_final in H. destruct H. inversion H.
- destruct H. induction x0.
  + inversion H.
  + inversion H.
  + inversion H; subst.
Qed.

  

Theorem strong_progress':
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
  + inversion IHS1. induction x0.
    * exists <<S; S2,s0>>. apply SSCompI. assumption.                           
    * exists <<S2, s0>>. apply SSCompII. assumption.
    * eexists <<s>>. apply SSCompIII.
      assert(s = s0).
      {inversion H. reflexivity.
      }
      subst. assumption.
  + assert (Beval s b = true \/ Beval s b = false).
    { induction (B[[b]]s). 
      - left. reflexivity.
      - right. reflexivity.
    }
   destruct H.
    * exists <<S1,s>>. apply SSIftrue. assumption.
    * exists <<S2,s>>. apply SSIffalse. assumption.
  + exists <<IF_ b THEN (S; WHILE b DO S) ELSE SKIP,s>>. apply SSWhile. 
  + exists (Stuck s). apply SSAbort.
- left. unfold is_final. exists s. reflexivity.
- left. unfold is_final. exists s.
 (*Problem - Stuch is not the same as final!*)
(*Qed.*)

