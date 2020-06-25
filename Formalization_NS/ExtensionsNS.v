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
Import ListNotations.

Local Open Scope Z_scope.
Open Scope while_scope.

(*----------------------------Non-determinism--------------------------------*)
(* We proved that natural semantics for While without extensions is
   deterministic. But we can add non-deterministic statements to While.
   For example, an or statement that gets two different statements and 
   executes one of the statements randomly is non-deterministic. *)

Module Non_determinism.
Declare Scope or.
Open Scope or.

Inductive Stm : Type :=
  | ass (x : string) (a : Aexp)
  | skip
  | comp (s1 s2 : Stm)
  | if_ (b : Bexp) (s1 s2 : Stm)
  | while (b : Bexp) (s : Stm)
  | or (S1 S2 : Stm).

Bind Scope or with Stm.
Notation "x '::=' a" :=
  (ass x a) (at level 60) : or.
Notation "'SKIP'" :=
   skip : or.
Notation "s1 ; s2" := 
  (comp s1 s2) (at level 80, right associativity) : or.
Notation "'WHILE' b 'DO' s " :=
  (while b s) (at level 80, right associativity) : or.
Notation "'IF_' b 'THEN' s1 'ELSE' s2 " := 
  (if_ b s1 s2) (at level 80, right associativity) : or.
Notation "s1 'OR' s2" :=
  (or s1 s2) (at level 80, right associativity) : or.

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
  | or_1_ns : forall st st' s1 s2,
      Seval st s1 st' ->
      Seval st (or s1 s2) st'
  | or_2_ns : forall st st' s1 s2,
      Seval st s2 st' ->
      Seval st (or s1 s2) st'.

Notation "<< s , st >> --> st'" := (Seval st s st')
                                 (at level 40).

(* We use this theorem defined in ApplicationNS to make the proofs a easier. *)
Theorem stm_eq :
  forall S s s' s'',
  << S , s >> --> s' ->
  s' = s'' ->
  << S , s >> --> s''.
Proof.
  intros.
  rewrite H0 in H.
  apply H.
Qed.

(* We also use the tactic defined in ApplicationNS. *)
Ltac eq_states :=
  apply functional_extensionality; intros; unfold t_update; simpl;
  repeat match goal with
  |- context [eqb_string ?v ?x] =>
    destruct (eqb_string v x)
  end;
  reflexivity.

(* We can now proof 2 different outcomes for the same tree *)
Example nondet1 :
  << x ::= 1 OR (x ::= 2 ; x ::= x + 2), x !-> 0 >> --> (x !-> 1).
Proof.
  eapply stm_eq.
  - eapply or_1_ns.
    eapply ass_ns. 
    reflexivity.
  - eq_states.
Qed. 

Example nondet2 :
  << x ::= 1 OR (x ::= 2 ; x ::= x + 2), x !-> 0 >> --> (x !-> 4).
Proof.
  eapply stm_eq.
  - eapply or_2_ns.
    eapply comp_ns.
    + eapply ass_ns. 
      reflexivity.
    + eapply ass_ns.
      reflexivity.
  - eq_states.
Qed.

Example nondet3 :
 << (WHILE true DO SKIP) OR (x ::= 2 ; x ::= x + 2), x !-> 0 >> 
 --> (x !-> 4).
Proof.
  eapply stm_eq.
  - eapply or_1_ns.
    eapply while_tt_ns.
    + reflexivity.
    + eapply skip_ns.
    + eapply while_tt_ns.
(* There is no derivation tree for this because it loops forever.
Therefore, the statement is not provable using or_1_ns. *)
    Admitted.

Example nondet4 :
 << (WHILE true DO SKIP) OR (x ::= 2; x ::= x + 2), x !-> 0 >> 
 --> (x !-> 4).
Proof.
  eapply stm_eq.
  - eapply or_2_ns.
    eapply comp_ns.
    + eapply ass_ns. 
      reflexivity.
    + eapply ass_ns.
      reflexivity.
  - eq_states.
Qed.
(* This does have a derivation tree *)

End Non_determinism.

(*-----------------------------------Break-----------------------------------*)
(* We can make an extension of While that has a break status. The break
   statement causes the loop around the break statement to terminate.
   This means that if a break occurs in the body of a while statement,
   every statement after the break is not executed. *)

Module Break.
Declare Scope br.
Open Scope br.

Inductive Stm : Type :=
  | ass (x : string) (a : Aexp)
  | skip
  | comp (s1 s2 : Stm)
  | if_ (b : Bexp) (s1 s2 : Stm)
  | while (b : Bexp) (s : Stm)
  | break.

Bind Scope br with Stm.
Notation "x '::=' a" :=
  (ass x a) (at level 60) : br.
Notation "'SKIP'" :=
   skip : br.
Notation "s1 ; s2" := 
  (comp s1 s2) (at level 80, right associativity) : br.
Notation "'WHILE' b 'DO' s " :=
  (while b s) (at level 80, right associativity) : br.
Notation "'IF_' b 'THEN' s1 'ELSE' s2 " := 
  (if_ b s1 s2) (at level 80, right associativity) : br.
Notation "'BREAK'" :=
  break : br.

(* Syntax Break status *)
Inductive Bstatus : Type :=
  | b
  | no_b.

(* New transition that includes the break status *)
Reserved Notation "'<<' S ',' st '>>' '-->' '(' st' ',' br ')'"
         (at level 40, st' at next level).

Inductive Seval : State -> Stm -> State -> Bstatus -> Prop :=
  | ass_ns  : forall st a1 n x,
      Aeval st a1 = n ->
      Seval st (x ::= a1) (t_update st x n) no_b
  | skip_ns : forall st,
      Seval st SKIP st no_b
  | comp_b_ns : forall s1 s2 st st',
      Seval st s1 st' b ->
      Seval st (s1 ; s2) st' b
  | comp_no_b_ns : forall s1 s2 st st' st'' B,
      Seval st s1 st' no_b ->
      Seval st' s2 st'' B ->
      Seval st (s1 ; s2) st'' B
  | if_tt_ns : forall st st' b1 s1 s2 B,
      Beval st b1 = true ->
      Seval st s1 st' B ->
      Seval st (IF_ b1 THEN s1 ELSE s2) st' B
  | if_ff_ns : forall st st' b1 s1 s2 B,
      Beval st b1 = false ->
      Seval st s2 st' B ->
      Seval st (IF_ b1 THEN s1 ELSE s2) st' B
  | while_tt_b_ns : forall st st' b1 s1,
      Beval st b1 = true ->
      Seval st s1 st' b ->
      Seval st (WHILE b1 DO s1) st' no_b
  | while_tt_no_b_ns : forall st st' st'' b1 s1 B,
      Beval st b1 = true ->
      Seval st s1 st' no_b ->
      Seval st' (WHILE b1 DO s1) st'' B ->
      Seval st (WHILE b1 DO s1) st'' no_b
  | while_ff_ns : forall b1 st s1,
      Beval st b1 = false ->
      Seval st (WHILE b1 DO s1) st no_b
  | break_ns : forall st,
      Seval st (BREAK) st b
where "'<<' s ',' st '>>' '-->' '(' st' ',' br ')'" := 
      (Seval st s st' br).

(* Some theorems to check if the break does what it should do,
   Taken from Software Foundations chapter Imp *)
Theorem break_ignore : forall S st st' B,
     << BREAK ; S, st >> --> ( st', B ) ->
     st = st'.
Proof.
  intros.
  inversion H; subst.
  - inversion H5; subst.
    reflexivity.
  - inversion H3.
Qed.

Theorem while_continue : forall b S st st' B,
  << WHILE b DO S, st >> --> ( st', B ) ->
  B = no_b.
Proof.
  intros.
  inversion H; subst.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem while_stops_on_break : forall bo S st st',
  Beval st bo = true ->
  << S, st >> --> (st', b) ->
  << WHILE bo DO S, st >> --> (st', no_b).
Proof.
  intros.
  apply while_tt_b_ns.
  - apply H.
  - apply H0.
Qed.

(* We will need stm_eq and eq_states from the ApplicationNS.v file to easily
   show that the given state is equal to the rules applied to a dummy state. *)

Theorem stm_eq :
  forall S s s' s'' B,
  << S, s >> --> (s', B) ->
  s' = s'' ->
  << S, s >> --> (s'', B).
Proof.
  intros.
  rewrite H0 in H.
  apply H.
Qed.

Ltac eq_states :=
  apply functional_extensionality; intros; unfold t_update; simpl;
  repeat match goal with
  |- context [eqb_string ?v ?x] =>
    destruct (eqb_string v x)
  end;
  reflexivity.

(* The first example from the lecture *)
Definition program1 :=
  x ::= 5;
  y ::= 3;
  WHILE (x <= 7) DO
    x ::= x + 2;
    (IF_ ~(x <= 8) THEN BREAK ELSE SKIP);
    y ::= y*3.

Example proof1 :
  << program1, x !-> 0 >> --> ( (x !-> 9, y !-> 9), no_b).
Proof.
  unfold program1.
  eapply stm_eq.
  - eapply comp_no_b_ns.
    + apply ass_ns.
      reflexivity.
    + eapply comp_no_b_ns.
      * apply ass_ns.
        reflexivity.
      * eapply while_tt_no_b_ns.
        { reflexivity. }
        { eapply comp_no_b_ns.
          - apply ass_ns.
            reflexivity.
          - eapply comp_no_b_ns.
            + eapply if_ff_ns.
              * reflexivity.
              * apply skip_ns.
            + apply ass_ns.
                reflexivity.
        }
        { eapply while_tt_b_ns.
          - reflexivity.
          - eapply comp_no_b_ns.
            + apply ass_ns.
              reflexivity.
            + eapply comp_b_ns.
              eapply if_tt_ns.
              * reflexivity.
              * apply break_ns.
        }
  - eq_states.
Qed.

(* The second example from the lecture *)
Definition program2 :=
  x ::= 5;
  BREAK;
  y ::= 3;
  WHILE (x <= 7) DO
    x ::= x + 2;
    (IF_ ~(x <= 8) THEN BREAK ELSE SKIP);
    y ::= y*3.

Example proof2 :
  << program2, x !-> 0 >> --> ((x !-> 5, x !-> 0), b).
Proof.
  unfold program2.
  apply comp_no_b_ns with (x !-> 5, x !-> 0).
  - apply ass_ns.
    reflexivity.
  - apply comp_b_ns.
    apply break_ns.
Qed.

End Break.

(*---------------------------------Continue----------------------------------*)
(* If a continue occurs inside a while loop then the statements after the
   continue are not executed but then loop condition is evaluated again. *)
Module Continue.
Declare Scope con.
Open Scope con.

Inductive Stm : Type :=
  | ass (x : string) (a : Aexp)
  | skip
  | comp (s1 s2 : Stm)
  | if_ (b : Bexp) (s1 s2 : Stm)
  | while (b : Bexp) (s : Stm)
  | continue.

Bind Scope con with Stm.
Notation "x '::=' a" :=
  (ass x a) (at level 60) : con.
Notation "'SKIP'" :=
   skip : con.
Notation "s1 ; s2" := 
  (comp s1 s2) (at level 80, right associativity) : con.
Notation "'WHILE' b 'DO' s " :=
  (while b s) (at level 80, right associativity) : con.
Notation "'IF_' b 'THEN' s1 'ELSE' s2 " := 
  (if_ b s1 s2) (at level 80, right associativity) : con.
Notation "'CONTINUE'" :=
  continue : con.

(* Syntax for the continue status *)
Inductive Cstatus : Type :=
  | c
  | no_c.

Reserved Notation "'<<' S ',' st '>>' '-->' '(' st' ',' con ')'"
         (at level 40, st' at next level).

Inductive Seval : State -> Stm -> State -> Cstatus -> Prop :=
  | ass_ns  : forall st a1 n x,
      Aeval st a1 = n ->
      Seval st (x ::= a1) (t_update st x n) no_c
  | skip_ns : forall st,
      Seval st SKIP st no_c
  | comp_c_ns : forall s1 s2 st st',
      Seval st s1 st' c ->
      Seval st (s1 ; s2) st' c
  | comp_no_c_ns : forall s1 s2 st st' st'' C,
      Seval st s1 st' no_c ->
      Seval st' s2 st'' C ->
      Seval st (s1 ; s2) st'' C
  | if_tt_ns : forall st st' b1 s1 s2 C,
      Beval st b1 = true ->
      Seval st s1 st' C ->
      Seval st (IF_ b1 THEN s1 ELSE s2) st' C
  | if_ff_ns : forall st st' b1 s1 s2 C,
      Beval st b1 = false ->
      Seval st s2 st' C ->
      Seval st (IF_ b1 THEN s1 ELSE s2) st' C
  | while_tt_c_ns : forall st st' st'' b1 s1 C,
      Beval st b1 = true ->
      Seval st s1 st' c ->
      Seval st' (WHILE b1 DO s1) st'' C ->
      Seval st (WHILE b1 DO s1) st' no_c
  | while_tt_no_c_ns : forall st st' st'' b1 s1 C,
      Beval st b1 = true ->
      Seval st s1 st' no_c ->
      Seval st' (WHILE b1 DO s1) st'' C ->
      Seval st (WHILE b1 DO s1) st'' no_c
  | while_ff_ns : forall b1 st s1,
      Beval st b1 = false ->
      Seval st (WHILE b1 DO s1) st no_c
  | continue_ns : forall st,
      Seval st (CONTINUE) st c
where "'<<' s ',' st '>>' '-->' '(' st' ',' con ')'" :=
      (Seval st s st' con).

(* We will need stm_eq and eq_states from the ApplicationNS.v file to easily
   show that the given state is equal to the rules applied to a dummy state. *)
Theorem stm_eq :
  forall S s s' s'' C,
  << S, s >> --> (s', C) ->
  s' = s'' ->
  << S, s >> --> (s'', C).
Proof.
  intros.
  rewrite H0 in H.
  apply H.
Qed.

Ltac eq_states :=
  apply functional_extensionality; intros; unfold t_update; simpl;
  repeat match goal with
  |- context [eqb_string ?v ?x] =>
    destruct (eqb_string v x)
  end;
  reflexivity.

(* The first example program for break now using continue *)
Definition program1 :=
  x ::= 5;
  y ::= 3;
  WHILE (x <= 7) DO
    x ::= x + 2;
    (IF_ ~(x <= 8) THEN CONTINUE ELSE SKIP);
    y ::= y*3.

Example proof1 :
  << program1, x !-> 0 >> --> ( (x !-> 9, y !-> 9), no_c).
Proof.
  unfold program1.
  eapply stm_eq.
  - eapply comp_no_c_ns.
    + apply ass_ns.
      reflexivity.
    + eapply comp_no_c_ns.
      * apply ass_ns.
        reflexivity.
      * eapply while_tt_no_c_ns.
        { reflexivity. }
        { eapply comp_no_c_ns.
          - apply ass_ns.
            reflexivity.
          - eapply comp_no_c_ns.
            + eapply if_ff_ns.
              * reflexivity.
              * apply skip_ns.
            + apply ass_ns.
                reflexivity.
        }
        { eapply while_tt_c_ns.
          - reflexivity.
          - eapply comp_no_c_ns.
            + apply ass_ns.
              reflexivity.
            + eapply comp_c_ns.
              eapply if_tt_ns.
              * reflexivity.
              * apply continue_ns.
          - eapply while_ff_ns.
            reflexivity.
        }
  - eq_states.
Qed.

(* The second example program for break now using continue *)
Definition program2 :=
  x ::= 5;
  CONTINUE;
  y ::= 3;
  WHILE (x <= 7) DO
    x ::= x + 2;
    (IF_ ~(x <= 8) THEN CONTINUE ELSE SKIP);
    y ::= y*3.

Example proof2 :
  << program2, x !-> 0 >> --> ( (x !-> 5, x !-> 0), c).
Proof.
  unfold program2.
  apply comp_no_c_ns with (x !-> 5, x !-> 0).
  - apply ass_ns.
    reflexivity.
  - apply comp_c_ns.
    apply continue_ns.
Qed.

End Continue.