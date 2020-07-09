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
From NS Require Import Framework_common.
From NS Require Import FrameworkNS.
Import ListNotations.

Local Open Scope Z_scope.
Open Scope while_scope.
(* ---------------------------Natural_Semantics------------------------------*)
(* We can computate what certain expressions evaluate to in certain states.
   Both expressions below should evaluate to x=4 *)
Compute (Aeval (x !-> 3) (x + 1)).
Compute (A[[x+1]] (x !-> 3)).

(* We can also proof that it should evaluate to 4 *)
Example Example1_5 :
  (A[[x+1]] (x !-> 3)) = 4.
Proof. 
reflexivity.
Qed.

(* We can also do some proofs from the book Nielson and Nielson *)
Example Example2_1 :
  << ( z::= x ; x::= y ) ; y::= z , y !-> 7, x !-> 5 >> 
  --> (y !-> 5, x !-> 7, z !-> 5, y !-> 7, x !-> 5).
Proof.
  apply comp_ns with (x !-> 7, z !-> 5, y !-> 7, x !-> 5).
  - apply comp_ns with (z !-> 5, y !-> 7, x !-> 5).
    + apply ass_ns. reflexivity.
    + apply ass_ns. reflexivity.
  - apply ass_ns. reflexivity.
Qed.
(* It is suboptimal that we need to supply the intermediate states for some
   rules and that the sequence of states needs to be defined instead of only
   the final states.*)

(* eapply is a tactic that allows the user omit the intermediate state
   that needs to be added when applying certain natural semantic rules *)
Example Example2_1b :
  << ( z::= x ; x::= y ) ; y::= z , z !-> 0, y !-> 7, x !-> 5 >>
  --> (y !-> 5, x !-> 7, z !-> 5, z !-> 0, y !-> 7, x !-> 5).
Proof.
  eapply comp_ns.
  - eapply comp_ns.
    + apply ass_ns. reflexivity.
    + apply ass_ns. reflexivity.
  - apply ass_ns. reflexivity.
Qed.

(* This theorem allows us to eapply all the rules to a dummy state s and
   then we need to prove that the dummy state s is the same as the given
   state *)
Theorem stm_eq :
  forall S s s' s'',
  << S, s >> --> s' ->
  s' = s'' ->
  << S, s >> --> s''.
Proof.
  intros.
  rewrite H0 in H.
  apply H.
Qed.

Example Example2_1c :
  << ( z::= x ; x::= y ); y::= z, y !-> 7, x !-> 5 >> 
  --> (y !-> 5, x !-> 7, z !-> 5).
Proof.
  eapply stm_eq.
  eapply comp_ns.
  - eapply comp_ns.
    + apply ass_ns. reflexivity.
    + apply ass_ns. reflexivity.
  - apply ass_ns. reflexivity.
  - apply functional_extensionality.
    intros x0.
    unfold t_update.
    simpl.
    destruct (eqb_string y x0). reflexivity.
    destruct (eqb_string x x0). reflexivity.
    reflexivity.
Qed.

(* This tactic can be used if the goal is to show that two states are equal.
   It only works on quite simple states but that is enough for this Coq file *)
Ltac eq_states :=
  apply functional_extensionality; intros;
  unfold t_update; simpl;
  repeat match goal with
  |- context [eqb_string ?v ?x] =>
    destruct (eqb_string v x)
  end;
  reflexivity.

(* Now we can use all the new tricks to easily solve this statement *)
Example Example2_1d :
  << ( z::= x ; x::= y ) ; y::= z, y !-> 7, x !-> 5 >> 
  --> (y !-> 5, x !-> 7, z !-> 5).
Proof.
  eapply stm_eq.
  eapply comp_ns.
  - eapply comp_ns.
    + apply ass_ns. reflexivity.
    + apply ass_ns. reflexivity.
  - apply ass_ns. reflexivity.
  - eq_states.
Qed.

(* A different example that uses a while statement *)
Theorem Example2_2 :
  << y::= 1 ; WHILE ~(x=1) DO ( y ::= y * x ; x ::= x-1 ),
  x !-> 3 >> --> (x !-> 1, y !-> 6, x !-> 2, y !-> 3, y !-> 1, x !-> 3).
Proof.
  apply comp_ns with ( y !-> 1, x !-> 3).
  - apply ass_ns. reflexivity.
  - apply while_tt_ns with ( x !-> 2 , y !-> 3, y !-> 1, x !-> 3).
    + reflexivity.
    + apply comp_ns with ( y !-> 3, y !-> 1, x !-> 3).
      * apply ass_ns. reflexivity.
      * apply ass_ns. reflexivity.
    + apply while_tt_ns with
        ( x !-> 1, y !-> 6, x !-> 2, y !-> 3, y !-> 1, x !-> 3).
      * reflexivity.
      * apply comp_ns with 
        ( y !-> 6, x !-> 2, y !-> 3, y !-> 1, x !-> 3).
        { apply ass_ns. reflexivity. }
        { apply ass_ns. reflexivity. }
      * apply while_ff_ns.
        reflexivity.
Qed.

Theorem Example2_2b :
  << y ::= 1; WHILE ~(x=1) DO ( y ::= y * x ; x ::= x - 1 ), x !-> 3 >>
  --> ( x !-> 1, y !-> 6, x !-> 2, y !-> 3, y !-> 1, x !-> 3).
Proof.
  eapply stm_eq.
  eapply comp_ns.
  - eapply ass_ns. reflexivity.
  - eapply while_tt_ns.
    + reflexivity.
    + eapply comp_ns.
      * eapply ass_ns. reflexivity.
      * eapply ass_ns. reflexivity.
    + eapply while_tt_ns.
      * reflexivity.
      * eapply comp_ns.
        { eapply ass_ns. reflexivity. }
        { eapply ass_ns. reflexivity. }
      * eapply while_ff_ns.
        reflexivity.
  - eq_states.
Qed.

Theorem Exercise2_3 :
  << z::= 0; WHILE y <= x DO (z ::= z + 1 ; x ::= x - y), y !-> 5, x !-> 17 >>
  --> (x !-> 2, z !-> 3, x !-> 7, z !-> 2, x !-> 12, z !-> 1, z !-> 0,
       y !-> 5, x !-> 17).
Proof.
  apply comp_ns with ( z !-> 0, y !-> 5, x !-> 17).
  - apply ass_ns. reflexivity.
  - apply while_tt_ns with ( x !-> 12, z !-> 1, z !-> 0, y !-> 5, x !-> 17).
    + reflexivity.
    + apply comp_ns with ( z !-> 1, z !-> 0, y !-> 5, x !-> 17).
      * apply ass_ns. reflexivity.
      * apply ass_ns. reflexivity.
    + apply while_tt_ns with ( x !-> 7, z !-> 2, x !-> 12, z !-> 1,
        z !-> 0, y !-> 5, x !-> 17).
      * reflexivity.
      * apply comp_ns with ( z !-> 2, x !-> 12, z !-> 1, z !-> 0, y !-> 5,
        x !-> 17).
        {apply ass_ns. reflexivity. }
        {apply ass_ns. reflexivity. }
      * apply while_tt_ns with ( x !-> 2, z !-> 3, x !-> 7, z !-> 2, x !-> 12,
        z !-> 1, z !-> 0, y !-> 5, x !-> 17).
        { reflexivity. }
        { apply comp_ns with ( z !-> 3, x !-> 7, z !-> 2, x !-> 12, z !-> 1,
          z !-> 0, y !-> 5, x !-> 17).
          - apply ass_ns. reflexivity.
          - apply ass_ns. reflexivity.
        }
        { apply while_ff_ns. reflexivity. }
Qed.

Theorem Exercise2_3b :
  << z ::= 0; WHILE y <= x DO (z ::= z + 1 ; x ::= x - y), y !-> 5, x !-> 17 >>
  --> (x !-> 2, z !-> 3, x !-> 7, z !-> 2, x !-> 12, z !-> 1, z !-> 0,
       y !-> 5, x !-> 17).
Proof.
  eapply stm_eq.
  eapply comp_ns.
  - eapply ass_ns. reflexivity.
  - eapply while_tt_ns.
    + reflexivity.
    + eapply comp_ns.
      * eapply ass_ns. reflexivity.
      * eapply ass_ns. reflexivity.
    + eapply while_tt_ns.
      * reflexivity.
      * eapply comp_ns.
        {eapply ass_ns. reflexivity. }
        {eapply ass_ns. reflexivity. }
      * eapply while_tt_ns.
        { reflexivity. }
        { eapply comp_ns.
          - eapply ass_ns. reflexivity.
          - eapply ass_ns. reflexivity.
        }
        { eapply while_ff_ns. reflexivity. }
  - eq_states.
Qed.


(*---------------------------Semantic_Equivalence----------------------------*)
(* A simple proof of semantic equivalence, no need for induction yet *)
Theorem Lemma2_5 : forall b S,
  Sequiv
    ( WHILE b DO S )
    ( IF_ b THEN (S ; WHILE b DO S) ELSE SKIP ).
Proof.
  intros b S st st''.
  symmetry.
  split; intros Hce.
  - (* -> while b do S, s -> s''*)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply while_tt_ns with (st' := st').
      apply H4.
      apply H3.
      apply H6.
    + (* loop doesn't run *)
      inversion H5; subst.
      apply while_ff_ns.
      apply H4.
  -  (* <- <if b then (S; while b do S) else skip, s> -> s''*)
    inversion Hce; subst.
    + (* loop runs *)
      apply if_tt_ns.
      apply H2.
      apply comp_ns with (st' := st').
      apply H4.
      apply H5.
    + (* loop doesn't run *)
      apply if_ff_ns.
      apply H3.
      apply skip_ns.
Qed.

(* Another simple example of semantic equivalence *)
Theorem Exercise2_6: forall S1 S2 S3,
  Sequiv ( (S1 ; S2) ; S3) ( S1 ; (S2 ; S3)).
Proof.
  intros S1 S2 S3.
  split; intros.
  - inversion H; subst.
    inversion H4; subst.
    apply comp_ns with (st' := st'1).
    + apply H6.
    + apply comp_ns with (st' := st'0).
      * apply H7.
      * apply H5.
  - inversion H; subst. inversion H5; subst.
    apply comp_ns with (st' := st'1).
    + apply comp_ns with (st' := st'0).
      * apply H4.
      * apply H6.
    + apply H7.
Qed.

(* We can introduce the repeat statement and then try to prove that
   repeat S until b is semantically equivalent to S;while b do S. *)
Module Repeat.
Declare Scope rep.
Open Scope rep.

Inductive Stm : Type :=
  | ass (x : string) (a : Aexp)
  | skip
  | comp (s1 s2 : Stm)
  | if_ (b : Bexp) (s1 s2 : Stm)
  | while (b : Bexp) (s : Stm)
  | repeat (s : Stm) (b : Bexp).

Bind Scope rep with Stm.
Notation "x '::=' a" :=
  (ass x a) (at level 60) : rep.
Notation "'SKIP'" :=
   skip : rep.
Notation "s1 ; s2" := 
  (comp s1 s2) (at level 80, right associativity) : rep.
Notation "'WHILE' b 'DO' s " :=
  (while b s) (at level 80, right associativity) : rep.
Notation "'IF_' b 'THEN' s1 'ELSE' s2 " := 
  (if_ b s1 s2) (at level 80, right associativity) : rep.
Notation "'REPEAT' s1 'UNTIL' b1 " :=
  (repeat s1 b1) (at level 80, right associativity) : rep.

Inductive Seval : State -> Stm -> State -> Prop :=
  | ass_ns  : forall st a1 n x,
      Aeval st a1 = n ->
      Seval st (x ::= a1) (t_update st x n)
  | skip_ns : forall st,
      Seval st SKIP st
  | comp_ns : forall s1 s2 st st' st'',
      Seval st s1 st' ->
      Seval st' s2 st'' ->
      Seval st (s1 ; s2) st''
  | if_tt_ns : forall st st' b1 s1 s2,
      Beval st b1 = true ->
      Seval st s1 st' ->
      Seval st (IF_ b1 THEN s1 ELSE s2) st'
  | if_ff_ns : forall st st' b1 s1 s2,
      Beval st b1 = false ->
      Seval st s2 st' ->
      Seval st (IF_ b1 THEN s1 ELSE s2) st'
  | while_tt_ns : forall st st' st'' b1 s1,
      Beval st b1 = true ->
      Seval st s1 st' ->
      Seval st' (WHILE b1 DO s1) st'' ->
      Seval st (WHILE b1 DO s1) st''
  | while_ff_ns : forall b1 st s1,
      Beval st b1 = false ->
      Seval st (WHILE b1 DO s1) st
  | repeat_until_tt_ns : forall st st' b1 s1,
      Seval st s1 st' ->
      Beval st' b1 = true ->
      Seval st (repeat s1 b1) st'
  | repeat_until_ff_ns : forall st st' st'' b1 s1,
      Seval st s1 st' ->
      Beval st' b1 = false ->
      Seval st' (repeat s1 b1) st'' ->
      Seval st (repeat s1 b1) st''.

Notation "<< s , st >> --> st'" := (Seval st s st')
                                 (at level 40).

Definition Sequiv (S1 S2 : Stm) : Prop :=
  forall (st st' : State),
    Seval st S1 st' <-> Seval st S2 st'.

(* We need a lemma for this, just like in the assignment *)
Lemma Lem_Assignment:
  forall b S s s' s'',  
    << WHILE ~b DO S , s'' >> --> s' 
  -> 
    << S , s >> --> s'' 
  -> 
    << REPEAT S UNTIL b , s >> --> s'.
Proof.
  intros b S.
  intros st st' st'' H0.
  remember (WHILE ~b DO S) as Swhile eqn:HeqSwhile.
  generalize dependent st.
  induction H0.
  - (* ass *)
    inversion HeqSwhile.
  - (* skip *)
    inversion HeqSwhile.
  - (* comp *)
    inversion HeqSwhile.
  - (* if tt *)
    inversion HeqSwhile.
  - (* if ff *)
    inversion HeqSwhile.
  - (* while tt *)
     inversion HeqSwhile; subst.
     intro st'''.
     intro H1.
     apply repeat_until_ff_ns with (st':=st).
     + assumption.
     + simpl in H.
       apply negb_true_iff in H.
       assumption.
     + apply IHSeval2.
       reflexivity.
       assumption.
  - (* while ff *) 
    inversion HeqSwhile; subst.
    intro s.
    intro H1.
    apply repeat_until_tt_ns.
    + apply H1.
    + simpl in H.
      apply negb_false_iff in H.
      assumption.
  - (* repeat until tt *)
    inversion HeqSwhile.
  - (* repeat until ff *)
    inversion HeqSwhile.
Qed.

Theorem repeat_until_slides : forall b S,
  Sequiv
    ( REPEAT S UNTIL b )
    ( S ; WHILE ~b DO S ).
Proof.
  intros b S.
  split; intro HSe.
  - (* -> *)
    remember (REPEAT S UNTIL b ) as Srepunt eqn:HeqSrepunt.
    induction HSe.
    + (* ass *)
      inversion HeqSrepunt.
    + (* skip *)
      inversion HeqSrepunt.
    + (* comp *)
      inversion HeqSrepunt.
    + (* if tt *)
      inversion HeqSrepunt.
    + (* if ff *)
      inversion HeqSrepunt.
    + (* while tt *)
      inversion HeqSrepunt.
    + (* while ff *)
      inversion HeqSrepunt.
    + (* repeat until tt *)
       inversion HeqSrepunt; subst.
       apply comp_ns with (st' := st').
       assumption.
       apply while_ff_ns.
       simpl.
       apply negb_false_iff.
       assumption.
    + (* repeat until ff *)
       inversion HeqSrepunt; subst.
       assert (<< S; WHILE ~ b DO S, st' >> --> st'').
       { apply IHHSe2.
         reflexivity. }
       inversion H0; subst.
       apply comp_ns with (st' := st').
       * assumption.
       * apply while_tt_ns with (st' := st'0).
         simpl.
         apply negb_true_iff.
         assumption.
         assumption.
         assumption.
  - (* <- *)
    inversion HSe; subst.
    apply Lem_Assignment with (s'':=st'0).
    assumption.
    assumption.
Qed.

End Repeat.
(*--------------------------------Determinism--------------------------------*)
(* Natural Semantics is deterministic *)
Theorem Seval_deterministic: forall S s s' s'',
     << S, s >> --> s'  ->
     << S, s >> --> s'' ->
     s' = s''.
Proof.
  intros S s s' s'' H1 H2.
  generalize dependent s''.
  induction H1; intros s'' H2; inversion H2; subst.
  - (* ass *) reflexivity.
  - (* skip *) reflexivity.
  - (* comp *)
    assert (st' = st'0) as H3.
    { apply IHSeval1; assumption. }
    subst st'0.
    apply IHSeval2. assumption.
  - (* if tt, b1 evaluates to true *)
      apply IHSeval. assumption.
  - (* if tt,  b1 evaluates to false (contradiction) *)
      rewrite H in H7. discriminate H7.
  - (* if ff, b1 evaluates to true (contradiction) *)
      rewrite H in H7. discriminate H7.
  - (* if ff, b1 evaluates to false *)
      apply IHSeval. assumption.
  - (* while tt, b1 evaluates to true *)
      assert (st' = st'0) as H3.
      { apply IHSeval1; assumption. }
      subst st'0.
      apply IHSeval2. assumption.
  - (* while tt, b1 evaluates to false (contradiction) *)
    rewrite H in H5. discriminate H5.
  - (* while ff, b1 evaluates to true (contradiction) *)
    rewrite H in H4. discriminate H4.
  - (* while ff, b1 evaluates to false *)
    reflexivity.
Qed.
