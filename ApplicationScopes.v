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
From NS Require Import FrameworkScopes.
Import ListNotations.

Local Open Scope Z.
Open Scope while_scope.
Definition x : string := "x".
Definition y : string := "y".
(*-----------------------------------Blocks----------------------------------*)
(* A simple blocks example *)
Definition example1 :=
  BEGIN var x := 1; var x := x + 1, 
    x ::= 4
  END.

Theorem blocksproof1 :
  << example1, x !-> 0 >>
  --> (x !-> 0).
Proof.
  unfold example1.
  eapply stm_eq.
  eapply block_ns with (x:=x).
  - eapply var_ns.
    + reflexivity.
    + eapply var_ns.
        * reflexivity.
        * apply none_ns.
  - eapply ass_ns.
    reflexivity.
  - simpl.
    unfold var_update.
    simpl.
    apply functional_extensionality.
    intros.
    destruct (string_dec x0 y).
    + rewrite e.
      reflexivity.
    + destruct (string_dec x0 x).
      * subst. reflexivity.
      * rewrite t_update_neq.
        { destruct (string_dec x0 x).
          - apply eqb_string_false_iff in n0.
            apply eqb_string_true_iff in e.
            rewrite n0 in e.
            discriminate e.
          - repeat (try (rewrite t_update_neq); try reflexivity;
            try (apply not_sym; assumption)).
          }
        apply not_sym. assumption.
Qed.

(* The Blocks example from the slides *)
Definition example2 :=
  BEGIN var y := 1,
    ( x ::= 1;
      (BEGIN var x := 2, y ::= x + 1 END);
      x ::= y + x )
  END.

Theorem blocksproof2 :
  << example2, y !-> 0, x !-> 0 >>
  --> (x !-> 4, y !-> 0).
Proof.
  unfold example2.
  eapply stm_eq.
  eapply block_ns with (x := y).
  - eapply var_ns.
    + reflexivity.
    + eapply none_ns.
  - eapply comp_ns.
    + eapply ass_ns.
      reflexivity.
    + eapply comp_ns.
      * eapply block_ns with (x := x).
        { eapply var_ns.
          - reflexivity.
          - eapply none_ns.
        }
        { eapply ass_ns.
          reflexivity.
        }
      * eapply ass_ns.
        reflexivity.
  - simpl.
    unfold var_update.
    simpl.
    apply functional_extensionality.
    intros.
    destruct (string_dec x0 y).
    + rewrite e.
      reflexivity.
    + destruct (string_dec x0 x).
      * subst. reflexivity.
      * rewrite t_update_neq.
        { destruct (string_dec x0 x).
          - apply eqb_string_false_iff in n0.
            apply eqb_string_true_iff in e.
            rewrite n0 in e.
            discriminate e.
          - repeat (try (rewrite t_update_neq);
            try reflexivity;
            try (apply not_sym; assumption)).
          }
        apply not_sym.
        assumption.
Qed.

(*-----------------------------Dynamic_Scopes--------------------------------*)
Module DynamicApplication.
Import Dynamic.

(* The Proc program from the slides *)
Definition procprogram :=
  BEGIN var x := 0,
    (proc p is ( x ::= x * 2 );
    proc q is ( CALL p )),
    BEGIN var x := 5,
      proc p is ( x ::= x + 1 ),
      ( (CALL q) ; y ::= x )
    END
  END.

(* Dynamic procedure scope proof *)
Theorem dynamic_proof :
  empty |- << Some procprogram, x !-> 0 >>
  -->
  (y !-> 6, x !-> 0).
Proof.
  eapply stm_eq_env.
  - unfold procprogram.
    eapply block_ns with (x := x).
    + eapply var_ns.
      * reflexivity.
      * eapply none_ns.
    + eapply block_ns with (x := x).
      * eapply var_ns.
        { reflexivity. }
        { eapply none_ns. }
      * eapply comp_ns.
        { simpl. eapply call_rec_ns.
          eapply call_rec_ns.
          eapply ass_ns.
          reflexivity. }
        { eapply ass_ns.
          reflexivity. }
  - simpl.
    unfold var_update.
    simpl.
    apply functional_extensionality.
    intros.
    destruct (string_dec x0 x).
    + rewrite e.
      reflexivity.
    + destruct (string_dec x0 y).
      * subst. reflexivity.
      * rewrite t_update_neq.
        { repeat (try (rewrite t_update_neq);
          try reflexivity;
          try (apply not_sym; assumption)). }
        { apply not_sym. assumption. }
Qed.

End DynamicApplication.
(*------------------------------Mixed_Scopes---------------------------------*)
Module MixedApplication.
Import Mixed.

Definition procprogram : Stm :=
  BEGIN var x := 0,
    (proc p is ( x ::= x * 2 );
    proc q is ( CALL p )),
    BEGIN var x := 5,
      proc p is ( x ::= x + 1 ),
      ( ( CALL q ) ; y ::= x )
    END
  END.

(* Static procedure scope proof *)
Theorem static_proof :
  empty_envp |- << procprogram, x !-> 0 >>
  -->
  (y !-> 10, x !-> 0).
Proof.
  eapply stm_eq_env.
  - unfold procprogram.
    eapply block_ns with (x:=x).
    + eapply var_ns.
      * reflexivity.
      * eapply none_ns.
    + simpl. eapply block_ns with (x := x).
      * eapply var_ns.
        { reflexivity. }
        { eapply none_ns. }
      * eapply comp_ns.
        { simpl.
          eapply call_ns.
          simpl.
          eapply call_ns.
          simpl.
          apply ass_ns.
          reflexivity.
        }
          eapply ass_ns.
          reflexivity.
  - simpl.
    unfold var_update.
    simpl.
    apply functional_extensionality.
    intros.
    destruct (string_dec x0 x).
    + rewrite e.
      reflexivity.
    + destruct (string_dec x0 y).
      * subst. reflexivity.
      * rewrite t_update_neq.
        { repeat (try (rewrite t_update_neq);
          try reflexivity;
          try (apply not_sym; assumption)). }
        { apply not_sym. assumption. }
Qed.

(* Dynamic procedure scope proof using the new environment *)
Theorem dynamic_proof :
  empty_envp |- << procprogram, x !-> 0 >>
  -->
  (y !-> 6, x !-> 0).
Proof.
  eapply stm_eq_env.
  - unfold procprogram.
    eapply block_ns with (x := x).
    + eapply var_ns.
      * reflexivity.
      * eapply none_ns.
    + eapply block_ns with (x := x).
      * eapply var_ns.
        { reflexivity. }
        { eapply none_ns. }
      * eapply comp_ns.
        { simpl. eapply call_rec_ns.
          eapply call_rec_ns.
          eapply ass_ns.
          reflexivity. }
        { eapply ass_ns.
          reflexivity. }
  - simpl.
    unfold var_update.
    simpl.
    apply functional_extensionality.
    intros.
    destruct (string_dec x0 x).
    + rewrite e.
      reflexivity.
    + destruct (string_dec x0 y).
      * subst. reflexivity.
      * rewrite t_update_neq.
        { repeat (try (rewrite t_update_neq);
          try reflexivity;
          try (apply not_sym; assumption)). }
        { apply not_sym. assumption. }
Qed.

End MixedApplication.
