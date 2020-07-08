

Set warnings "-notation-overridden,-parsing".
Require Import Framework_SOS_match.
Require Import Framework_common.
From Coq Require Import BinNat.
From Coq Require Import omega.Omega.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Bool.Bool.

Local Open Scope Z_scope.

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition w : string := "w".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Bind Scope while_scope with Aexp.
Bind Scope while_scope with Bexp.
Bind Scope while_scope with Stm.
Delimit Scope while_scope with while.

Notation "x + y" := (APlus x y) (at level 50, left associativity).
Notation "x - y" := (AMinus x y) (at level 50, left associativity).
Notation "x * y" := (AMult x y) (at level 40, left associativity).
Notation "x <= y" := (BLe x y) (at level 70, no associativity).
Notation "x = y" := (BEq x y) (at level 70, no associativity).
Notation "x && y" := (BAnd x y) (at level 40, left associativity).
Notation "'~' b" := (BNot b) (at level 75, right associativity).
Open Scope while.

(*tiny derivation squences*)

Example triv_1:
<< x::= (1+3); SKIP, (y!->3, z!->3)>> ==> <<SKIP, x!->4, y!->3, z!->3>>.

Proof.
  - eapply SSCompII.
    + eapply SSAss. reflexivity.
Qed.




Example triv_2:

<< x::=4; SKIP, (x!->1, y!->3, z!->3)>> ==> <<SKIP, x!->4, y!->3, z!->3>>.
Proof.
  eapply stm_eq.
  - eapply SSCompII.
    + eapply SSAss. reflexivity.
  - apply conf_eq_rn. eq_states.
Qed.

Example triv_3:

<< x::=y, (x!->1, y!->4, z!->3)>> ==> << x!->4, y!->4, z!->3>>.
Proof.
  eapply stm_eq.
  eapply SSAss. reflexivity.
  apply conf_eq_fn.
  eq_states.
  Qed.


Example triv_4:

<< x::=y; SKIP, (x!->1, y!->7, z!->3)>> ==> <<SKIP, x!->7, y!->7, z!->3>>.
Proof.
   eapply stm_eq.
  - eapply SSCompII. (*note the 7-s*)
    + eapply SSAss. reflexivity.
  - apply conf_eq_rn. eq_states.
    Qed.

Example triv_5:

<< y::=x; SKIP, (x!->1, y!->7, z!->3)>> ==> <<SKIP, y!->1, x!->1, z!->3>>.
Proof.
  eapply stm_eq.
  - eapply SSCompII. (*note the 7-s*)
    + eapply SSAss. reflexivity.
  - apply conf_eq_rn. eq_states.
     Qed.


(*two tiny derivation trees*)
Example triv_6_multi:

<< x::=4; SKIP, (x!->1, y!->3, z!->3)>> ==>* << x!->4, y!->3, z!->3>>.

Proof.

  - eapply multistep.
    + eapply SSCompII.
      * eapply SSAss. reflexivity.
    + eapply multistep. eapply SSSkip.
   eapply no_stm_eq.
   eapply multirefl. apply conf_eq_fn. eq_states.
     Qed.

Example triv_7_lecture:
<< z ::=x; x ::= y; y ::=z, (x!->3, y!->4,  z!->5)>> ==>* 
    (*<< ( x!->4, y!-> 3, z!-> 3, x!->3, y!->4,  z!->5)>>.*)
    << (y!->3, x!->4, z!->3, x!->3, y!-> 4, z!-> 5)>>.
Proof.
  - eapply multistep. 
    + apply SSCompII. apply SSAss. reflexivity.
    + apply multistep with (<<y ::=z, x!->4, z!-> 3, x!->3, y!->4,  z!->5>>). 
      * apply SSCompII. apply SSAss. reflexivity.
      * apply multistep with <<(y!->3, x!->4, z!->3, x!->3, y!-> 4, z!-> 5)>>. 
        apply SSAss. reflexivity.  
   eapply no_stm_eq.
   eapply multirefl. apply conf_eq_fn. eq_states. Qed.
    (*<< ( x!->4, y!-> 3, z!-> 3, x!->3, y!->4,  z!->5)>>.*)
    (*<< (y!->3, x!->4, z!->3, x!->3, y!-> 4, z!-> 5)>>.*)
(*the power of eapply*)
Example triv_7_lecture':
<< z ::=x; x ::= y; y ::=z, (x!->3, y!->4,  z!->5)>> ==>* 
    << (y!->3, x!->4, z!->3)>>.
Proof.
  - apply multistep with <<x ::= y; y ::=z, z!->3, x!->3, y!-> 4, z!-> 5>>. 
    + apply SSCompII. apply SSAss. reflexivity.
    + eapply multistep.
      * apply SSCompII. apply SSAss. reflexivity.
      * eapply multistep. apply SSAss. reflexivity. 
   eapply no_stm_eq.
   eapply multirefl. apply conf_eq_fn. eq_states. Qed.

(*when will we need to use comp1*)
Example triv_7_lecture'':
<< (z ::=x; x ::= y); y ::=z, (x!->3, y!->4,  z!->5)>> ==>* 
    << (y!->3, x!->4, z!->3)>>.
Proof.
  - apply multistep with <<x::=y; y ::=z,  z!->3, x!->3, y!-> 4, z!-> 5>>. 
    + eapply SSCompI. (*<--- Used Comp 1! *)
      * apply SSCompII. apply SSAss. reflexivity.
    + apply multistep with <<y ::=z, x!->4, z!-> 3, x!->3, y!->4,  z!->5>>. 
      * apply SSCompII. apply SSAss. reflexivity.
      * apply multistep with << (y!->3, x!->4, z!->3, x!->3, y!-> 4, z!-> 5)>>.
       apply SSAss. reflexivity.  
   eapply no_stm_eq.
   eapply multirefl. apply conf_eq_fn. eq_states.
   Qed.


Definition triv_8_while: Stm :=
  x ::= 2;
  WHILE (~ (x=1))
  DO x ::= (AId x - 1)
  .

(*using apply, so that it is easier to see the step whem reading the proof*)
Example proof_8_while:
  <<triv_8_while , empty_State>> ==>* << x!->1>>.
Proof.
  unfold triv_8_while.
  - apply multistep with   <<WHILE (~ (x=1))
                          DO x ::= (x - 1 )
                          , x!->2>>.
    + apply SSCompII. apply SSAss. reflexivity.
    + eapply multistep.
      * apply SSWhile.
      * eapply multistep.
             ** apply SSIftrue. reflexivity.
             ** eapply multistep. 
                  apply SSCompII. apply SSAss. reflexivity.
                  eapply multistep.
                  *** apply SSWhile.
                  *** eapply multistep.
                      apply SSIffalse. reflexivity. 
                         eapply multistep. apply SSSkip.
   eapply no_stm_eq.
   eapply multirefl. apply conf_eq_fn. eq_states. Qed.
                  

Example proof_8_while':
  <<triv_8_while;SKIP, empty_State>> ==>* << x!->1>>.
Proof.
  unfold triv_8_while.
  - eapply multistep.
    + apply SSCompI. (* <-- NEW*)
      apply SSCompII. apply SSAss. reflexivity.
    + eapply multistep.
      ++ apply SSCompI. apply SSWhile.
      ++ eapply multistep. 
          * apply SSCompI. apply SSIftrue. reflexivity.
          * eapply multistep.
              ** apply SSCompI. apply SSCompII. apply SSAss. reflexivity.
              ** eapply multistep.
                *** apply SSCompI. apply SSWhile.
                *** eapply multistep.
                      -- apply SSCompI. apply SSIffalse. reflexivity.
                      -- eapply multistep.
                          apply SSCompII. apply SSSkip.
                          eapply multistep.   apply SSSkip.
    (*wrap_up_star.*)
   eapply no_stm_eq.
   eapply multirefl. apply conf_eq_fn. eq_states. Qed.
                  

(*using apply, so that it is easier to see the step whem reading the proof*)
Example proof_8_while_details:
  <<triv_8_while, empty_State>> ==>* << x!->1, x!->2>>.
Proof.
  unfold triv_8_while.
  - apply multistep with   <<WHILE (~ (x=1))
                          DO x ::= (x - 1 )
                          , x!->2>>.
    + apply SSCompII. apply SSAss. reflexivity.
    + apply multistep with <<IF_ (~(x=1)) THEN( x ::= (x - 1 );
                                              WHILE (~ (x=1))
                                              DO x ::= (x - 1 )
                                              )
                                         ELSE SKIP, x!->2>>.
      * apply SSWhile.
      * apply multistep with <<x ::= (x - 1 );
                              WHILE (~ (x=1))
                              DO x ::= (x - 1) , x!->2>>.
             ** apply SSIftrue. reflexivity.
             ** apply multistep  with <<WHILE (~ (x=1))
                                      DO x ::= (x - 1) , x!->1, x!->2>>. 
                  apply SSCompII. apply SSAss. reflexivity.
                  apply multistep with <<IF_ (~(x=1)) THEN( x ::= (x - 1 );
                                              WHILE (~ (x=1))
                                              DO x ::= (x - 1 )
                                              )
                                         ELSE SKIP, x!-> 1, x!->2>>.
                  *** apply SSWhile.
                  *** apply multistep with <<SKIP, x!->1, x!->2>>.
                      apply SSIffalse. reflexivity. 
                         apply multistep with << x!->1, x!->2>>. 
                         apply SSSkip. apply multirefl. Qed.

(*trying to use apply here is especially tedious, but helps to 
show where there are differences with the prevoiuos example. *)
Example proof_8_while_detail'':
  <<triv_8_while;SKIP, empty_State>> ==>* << x!->1, x!->2>>.
Proof.
  unfold triv_8_while.
  - apply multistep with   <<(WHILE (~ (x=1))
                          DO x ::= (x - 1 ))
                          ;SKIP, x!->2>>. (*<-- added ; SKIP*)
    + apply SSCompI. (* <-- NEW*)
      apply SSCompII. apply SSAss. reflexivity.
    +  apply multistep with   <<(IF_ (~(x=1)) THEN( x ::= (x - 1 );
                                              WHILE (~ (x=1))
                                              DO x ::= (x - 1 )
                                              )
                                         ELSE SKIP); SKIP, x!->2>>.
      ++ apply SSCompI. apply SSWhile.
      ++ apply multistep with <<(x::=(x-1);
                                WHILE (~ (x=1))
                                DO x ::= (x - 1 )
                                ); SKIP
                                , x!->2>>. 
          * apply SSCompI. apply SSIftrue. reflexivity.
          * apply multistep with <<(WHILE (~ (x=1))
                                DO x ::= (x - 1 ))
                                ; SKIP
                                , x!->1, x!->2>>.
              ** apply SSCompI. apply SSCompII. apply SSAss. reflexivity.
              ** apply multistep with   <<(IF_ (~(x=1)) THEN( x ::= (x - 1 );
                                              WHILE (~ (x=1))
                                              DO x ::= (x - 1 )
                                              )
                                         ELSE SKIP); SKIP, x!->1, x!->2>>.
                *** apply SSCompI. apply SSWhile.
                *** apply multistep with <<SKIP; SKIP, x!->1, x!->2>>. 
                      -- apply SSCompI. apply SSIffalse. reflexivity.
                      -- apply multistep with <<SKIP, x!->1, x!->2>>.
                          apply SSCompII. apply SSSkip.
                          apply multistep with <<x!->1, x!->2>>.  
                          apply SSSkip. apply multirefl. Qed.
                  
             
             

(* This works now, but not with the small steps expressions. *)
Example test:
<< x::= 1+1+1, empty_State>> ==> <<x!->3>>.
Proof.
  eapply SSAss. reflexivity.

Close Scope while.
