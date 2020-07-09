Set warnings "-notation-overridden,-parsing".
Require Import Framework_common.
Require Import Framework_SOS.
Require Import multi_k.
From Coq Require Import BinNat.
From Coq Require Import omega.Omega.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Bool.Bool.




Lemma star_stuck_stops:
forall s conf,
 <<s>> ==>* conf -> conf = <<s>>.
 Proof.
 intros.
 inversion H. reflexivity. subst.
 inversion H0.
 Qed.

Lemma star_implies_k:
forall conf conf',
  conf ==>* conf'
  ->
  exists k,
    conf ==>[k] conf'.
Proof.
intros.
induction H.
 - exists 0. apply zero_steps_rev. reflexivity.
 - inversion IHmulti. 
   exists (S x0).
   apply multikstep with y.
    + assumption.
    + assumption.
Qed.

Lemma k_implies_star:
forall conf conf' k,
  conf ==>[k] conf'
  ->
  conf ==>* conf'.
Proof.
intros.
induction H.
- apply multirefl.
- apply multistep with y.
  + assumption.
  + assumption.
Qed.

Lemma k_equiv_star:
forall conf conf',
  conf ==>* conf'
  <->
  exists k,
    conf ==>[k] conf'.
Proof.
intros. split.
- apply star_implies_k.
- intros.
  inversion H.
  apply k_implies_star with x. assumption.
Qed.
    
    
    
(*determinism-----------------------------*)
Lemma one_step_fin_deterministic:
forall s s' conf,
  conf ==> <<s>> ->
  conf ==> <<s'>> ->
  s = s'.
Proof.
intros.
inversion H; subst.
 - inversion H0. subst. reflexivity.
 - inversion H0. subst. reflexivity.
Qed.


Theorem conf_eq_rn_rev:
  forall S s s',
  <<S,s>> = <<S,s'>> -> s = s'.
Proof.
intros.
inversion H.
reflexivity.
Qed.

Theorem state_statement_eq:
forall S S' s s',
<<S, s>> = <<S', s'>>
-> S = S' /\ s = s'.
Proof.
intros.
inversion H.
split.
reflexivity. reflexivity.
Qed.

Theorem one_step_deterministic:
forall conf' conf'' conf,
  conf ==> conf' ->
  conf ==> conf'' ->
  conf' = conf''.
Proof.
intros c c1 c2 Hc1 Hc2.
generalize dependent c1.
induction Hc1; intros c2 Hc2.
 - (*SKIP*) inversion Hc2. reflexivity.
 - (*ASS*) inversion Hc2. subst. reflexivity.
 - (*COMPI*)inversion Hc2; subst.
    + assert (<<S1', st'>> = <<S1'0, st'0>>).
      {
        rewrite <- (IHHc1 <<S1'0, st'0>>).
        reflexivity. assumption.
      }
      inversion H. subst. reflexivity.
    + assert (<<S1', st'>> = << st'0>>).
      {
        rewrite <- (IHHc1 << st'0>>).
        reflexivity. assumption.
      }inversion H.
 - (*COMPII*)inversion Hc2; subst.
    + assert (<<S1', st'0>> = << st'>>).
      {
        rewrite <- (IHHc1 << S1', st'0>>).
        reflexivity. assumption.
      } inversion H.
    + assert (<< st'0>> = << st'>>).
      {
        rewrite <- (IHHc1 <<  st'0>>).
        reflexivity. assumption.
      } inversion H. subst. reflexivity. 
- (*IF TRUE*) inversion Hc2; subst.
    + reflexivity.
    + rewrite H5 in H. inversion H.
- (*IF FALSE*) inversion Hc2; subst.
    + rewrite H5 in H. inversion H.
    + reflexivity.
- (*WHILE*)  inversion Hc2; subst.
    reflexivity.
Qed.
   

Lemma final_state:
forall s s',
<<s>> = <<s'>>
-> s = s'.
Proof.
intros.
inversion H.
reflexivity. 
Qed.
(*
Lemma multikstep_deterministic:
forall s s' conf k,
  conf ==>[k] <<s>> ->
  conf ==>[k] <<s'>> ->
  s = s'.
Proof.
intros.
induction k.
- (*0*)
  apply zero_steps in H.
  apply zero_steps in H0.
  inversion H0. subst.
  apply final_state. assumption.
- (*s k*)
  inversion H; subst. inversion H0; subst.
  assert (y0 = y).
  { apply one_step_deterministic.
  }



Lemma multistep_deterministic:
forall s s' conf,
  conf ==>* <<s>> ->
  conf ==>* <<s'>> ->
  s = s'.
Proof.
intros.
apply star_implies_k in H.
apply star_implies_k in H0.

generalize dependent s'.
induction conf. (*; intros; inversion H0; subst.*)
-  intros. inversion H0; subst. inversion H; subst.

inversion H; subst.
- inversion H0. reflexivity. subst.
  apply star_stuck_stops in H0.
   inversion H0. reflexivity.
- apply star_implies_k in H. apply star_implies_k in H0.
  inversion H. inversion H0.
  induction x.
  induction x0.
  apply zero_steps in H3.
  apply zero_steps in H4.
  subst. apply final_state. assumption.
 induction conf; subst.
  inversion H1. 
inversion s'; subst.



 
Qed.
*)
