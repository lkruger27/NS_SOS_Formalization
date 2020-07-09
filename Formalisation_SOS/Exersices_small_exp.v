(*there is a commented definition of cstep in Thesis_SOS.
Those proofs are made with it, with the apttempt of small step
addition. *)

Set Warnings "-notation-overridden,-parsing".
Require Import Framework_SOS_small_exp.
From Coq Require Import Strings.String.

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Bind Scope while_scope with aexp.
Bind Scope while_scope with bexp.
Bind Scope while_scope with statement.
Delimit Scope while_scope with while.


Notation "x + y" := (APlus x y) (at level 50, left associativity) : while_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : while_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : while_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : while_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : while_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : while_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : while_scope.

(*Statement nodation remindes:
Coercion Final: state >-> Config.
Notation "'<<' S ',' st '>>'" := (Running S st).
Notation "x '::=' a" :=
  (SAss x a) (at level 60).
Notation "'SKIP'" :=
   SSkip.
Notation "s1 ; s2" := 
  (SComp s1 s2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' s " :=
  (SWhile b s) (at level 80, right associativity).
Notation "'IFS' b 'THEN' s1 'ELSE' s2 END " := 
  (SIf b s1 s2) (at level 80, right associativity).

*)


(*tiny derivation trees*)

Example trivia_1:
<< X::=1+3; SKIP,, (Y!->3, Z!->3)>> --> <<SKIP,, X!->4, Y!->3, Z!->3>>.

Proof.
  - eapply SSCompII.
    + eapply SSAss. eapply AS_Plus. Qed.


Example trivia_2:

<< X::=4; SKIP,, (X!->1, Y!->3, Z!->3)>> --> <<SKIP,, X!->4, X!->1, Y!->3, Z!->3>>.
(*is it supposed to keep memory of prevous values of X?
 Maybe tweak the update state function to remove the thing it is updating?  (and the order matters?)*)
Proof.
  - eapply SSCompII.
    + eapply SSAss. eapply AS_Num.
 Qed.

Example trivia_3:

<< X::=Y,, (X!->1, Y!->4, Z!->3)>> --> << X!->4, X!->1, Y!->4, Z!->3>>.
Proof.
  eapply SSAss. eapply AS_Id. Qed.


Example trivia_4:

<< X::=Y; SKIP,, (X!->1, Y!->7, Z!->3)>> --> <<SKIP,, X!->7, X!->1, Y!->7, Z!->3>>.
Proof.
  - eapply SSCompII. (*note the 7-s*)
    + eapply SSAss. eapply AS_Id.
 Qed.

(*two tiny derivation trees*)
Example trivia_5_multi:

<< X::=4; SKIP,, (X!->1, Y!->3, Z!->3)>> -->* << X!->4, X!->1, Y!->3, Z!->3>>.

Proof.
  - eapply multi_step.
    + eapply SSCompII.
      * eapply SSAss. eapply AS_Num.   
    + eapply multi_step. eapply SSSkip. eapply multi_refl. Qed.

