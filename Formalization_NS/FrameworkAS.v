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
Import ListNotations.

(* We don't use the Z scope here because we need many lemmas
   for mathematical things that are defined for natural numbers but not for
   integers. This means we will not be using the Num type. *)
(*----------------------Redefinition_Basic_Framework-------------------------*)
Declare Scope ns_scope.
Open Scope ns_scope.

Definition w : string := "w".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.
Notation "x '!->' v ',' m" := (t_update m x v)
        (at level 100, v at next level, right associativity).

Definition State := total_map nat.

(* Syntax Aexp*)
Inductive Aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : Aexp)
  | AMinus (a1 a2 : Aexp)
  | AMult (a1 a2 : Aexp).

(* Semantics Aexp *)
Fixpoint Aeval (st : State) (a : Aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (Aeval st a1) + (Aeval st a2)
  | AMinus a1 a2  => (Aeval st a1) - (Aeval st a2)
  | AMult a1 a2 => (Aeval st a1) * (Aeval st a2)
  end.

(* Syntax Bexp *)
Inductive Bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : Aexp)
  | BLe (a1 a2 : Aexp)
  | BNot (b : Bexp)
  | BAnd (b1 b2 : Bexp).

(* Semantics Bexp *)
Fixpoint Beval (st : State) (b : Bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (Aeval st a1) =? (Aeval st a2)
  | BLe a1 a2   => (Aeval st a1) <=? (Aeval st a2)
  | BNot b1     => negb (Beval st b1)
  | BAnd b1 b2  => andb (Beval st b1) (Beval st b2)
  end.

Coercion AId : string >-> Aexp.
Coercion ANum : nat >-> Aexp.

Definition bool_to_bexp (b : bool) : Bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> Bexp.

Declare Scope imp_scope.
Bind Scope imp_scope with Aexp.
Bind Scope imp_scope with Bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Definition empty_st := (_ !-> 0).

Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Notation " 'A' '[[' a ']]' st " := (Aeval st a)
        (at level 90, left associativity) : ns_scope.
Notation " 'B' '[[' b ']]' st " := (Beval st b)
        (at level 90, left associativity) : ns_scope.

Inductive Stm : Type :=
  | Sass (x : string) (a : Aexp)
  | Sskip
  | Scomp (s1 s2 : Stm)
  | Sif (b : Bexp) (s1 s2 : Stm)
  | Swhile (b : Bexp) (s : Stm).

Bind Scope ns_scope with Stm.
Notation "x '::=' a" :=
  (Sass x a) (at level 60) : ns_scope.
Notation "'SKIP'" :=
   Sskip : ns_scope.
Notation "s1 ; s2" := 
  (Scomp s1 s2) (at level 80, right associativity) : ns_scope.
Notation "'WHILE' b 'DO' s " :=
  (Swhile b s) (at level 80, right associativity) : ns_scope.
Notation "'IF_' b 'THEN' s1 'ELSE' s2 " := 
  (Sif b s1 s2) (at level 80, right associativity) : ns_scope.

Reserved Notation "'<<' S ',' st '>>' '-->' st'"
                  (at level 40).

Inductive Seval : Stm -> State -> State -> Prop :=
  | ass_ns  : forall st a1 n x,
      Aeval st a1 = n ->
      Seval (x ::= a1) st (t_update st x n)
  | skip_ns : forall st,
      Seval SKIP st st
  | comp_ns : forall s1 s2 st st' st'',
      Seval s1 st st' ->
      Seval s2 st' st'' ->
      Seval (s1;s2) st st''
  | if_tt_ns : forall st st' b s1 s2,
      Beval st b = true ->
      Seval s1 st st' ->
      Seval (IF_ b THEN s1 ELSE s2) st st'
  | if_ff_ns : forall st st' b s1 s2,
      Beval st b = false ->
      Seval s2 st st' ->
      Seval (IF_ b THEN s1 ELSE s2) st st'
  | while_tt_ns : forall st st' st'' b s,
      Beval st b = true ->
      Seval s st st' ->
      Seval (WHILE b DO s) st' st'' ->
      Seval (WHILE b DO s) st st''
  | while_ff_ns : forall b st s,
      Beval st b = false ->
      Seval (WHILE b DO s) st st.

Notation "<< S , st >> --> st'" := (Seval S st st')
                                   (at level 40).

(*-------------------------------Hoare_Logic---------------------------------*)
Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.

(* We first define assertions, these are the core of Axiomatic Semantics. *)
Definition Assertion := State -> Prop.

Definition as2 : Assertion := fun st => st x <= st y.

(* P and Q are predicates and S is a statement as usual. We say that P is
   the precondition and Q is the postcondition. *)
Definition hoare_triple
  (P : Assertion) (S : Stm) (Q : Assertion) : Prop :=
  forall st st',
     << S , st >> --> st'  ->
     P st  ->
     Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(* This is the informal definition of assertions: If predicate P holds in the
   starting state and statement S terminates on that starting state, then
   predicate Q must hold in the resulting final state. *)

(* Assertions can be true or false *)
Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H.
  unfold hoare_triple.
  intros st st' Heval HP.
  apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H.
  unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H.
  apply H in HP.
  inversion HP.
Qed.

(* We can define notation to use our normal logical operators with predicates*)
Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P =>> Q" := (assert_implies P Q)
  (at level 80) : hoare_spec_scope.

Definition assn_sub x a P : Assertion :=
  fun (st : State) => P (x !-> Aeval st a , st).

Notation "P [ x |-> a ]" := (assn_sub x a P)
  (at level 10, x at next level).

Definition bassn b : Assertion :=
  fun st => (Beval st b = true).

Notation " 'B' '[[' b ']]'" := (bassn b)
        (at level 90, left associativity) : ns_scope.

Definition bassn2 b : Assertion :=
  fun st => ~(Beval st b = true).

Notation " '~B' '[[' b ']]'" := (bassn2 b)
        (at level 90, left associativity) : ns_scope.

Definition and_sub (P1 P2 : Assertion) : Assertion :=
  fun (st : State) => P1 st /\ P2 st.

Notation "P1 /\p P2" := (and_sub P1 P2)
  (at level 10).

Definition or_sub (P1 P2 : Assertion) : Assertion :=
  fun (st : State) => P1 st \/ P2 st.

Notation "P1 \/p P2" := (or_sub P1 P2)
  (at level 10).


(* We can also define the rules that belong to the notation. The thing about
   axiomatic semantics is that we can also proof all the rules are correct. *)
Theorem assp : forall Q x a,
  {{Q [x |-> a]}} x ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q x a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

Theorem consp_pre : forall (P P' Q : Assertion) S,
  {{P'}} S {{Q}} ->
  P =>> P' ->
  {{P}} S {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem consp_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' =>> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

Theorem consp : forall (P P' Q Q' : Assertion) S,
  {{P'}} S {{Q'}} ->
  P =>> P' ->
  Q' =>> Q ->
  {{P}} S {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply consp_pre with (P' := P').
  apply consp_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

Theorem skipp : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

Theorem compp : forall P Q R S1 S2,
     {{Q}} S2 {{R}} ->
     {{P}} S1 {{Q}} ->
     {{P}} S1; S2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(* We can also define useful facts about bassn *)
Lemma Bexp_eval_true : forall b st,
  Beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma Bexp_eval_false : forall b st,
  Beval st b = false -> ~(bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn.
  rewrite Hbe.
  unfold not.
  intros.
  discriminate H.
Qed.

Theorem ifp : forall P Q b S1 S2,
  {{B[[b]] /\p P}} S1 {{Q}} ->
  {{~B[[b]] /\p P}} S2 {{Q}} ->
  {{P}} IF_ b THEN S1 ELSE S2 {{Q}}.
Proof.
  intros P Q b S1 S2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
    assumption.
    split.
    apply Bexp_eval_true.
    assumption.
    assumption.
  - (* b is false *)
    apply (HFalse st st').
    assumption.
    split.
    apply Bexp_eval_false.
    assumption. 
    assumption.
Qed.

Theorem whilep : forall P b c,
  {{B[[b]] /\p P}} c {{P}} ->
  {{P}} WHILE b DO c {{~B[[b]] /\p P}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* We need to use induction to talk about the complete loop *)
  remember (WHILE b DO c) as wcom eqn:Heqwcom.
  induction He;
  try (inversion Heqwcom);
  subst;
  clear Heqwcom.
  - (* while true *)
    apply IHHe2.
    reflexivity.
    apply (Hhoare st st').
    assumption.
    split.
    apply Bexp_eval_true.
    assumption.
    assumption. 
  - (* while false *) 
    split.
    apply Bexp_eval_false.
    assumption.
    assumption. 
Qed.

(*----------------------------Annotated_Programs-----------------------------*)
(* The derivation trees for axiomatic semantics tend to get very wide. We can
   improve the readability of the proofs by making annotated programs. This is
   quite a complex definition, it is not needed to understand how this works.*)

Module Annotated.

(* syntax annotated programs of statements with embedded assertions *)
Inductive AStm : Type :=
  | Aass : string -> Aexp ->  Assertion -> AStm
  | Askip :  Assertion -> AStm
  | Acomp : AStm -> AStm -> AStm
  | Aif : Bexp ->  Assertion -> AStm ->  Assertion -> AStm
           -> Assertion-> AStm
  | Awhile : Bexp -> Assertion -> AStm -> Assertion -> AStm
  | Apre : Assertion -> AStm -> AStm
  | Apost : AStm -> Assertion -> AStm.

Inductive Annotated : Type :=
  | annotated : Assertion -> AStm -> Annotated.

(* Notations to make it easier to write these programs *)
Declare Scope annot.
Open Scope annot.
Notation "x '::=' a {{ P }}"
      := (Aass x a P)
      (at level 60, a at next level) : annot.
Notation "'SKIP' {{ P }}"
      := (Askip P)
      (at level 10) : annot.
Notation " S1 ; S2 "
      := (Acomp S1 S2)
      (at level 80, right associativity)  : annot.
Notation "'IF_' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' {{ Q }}"
      := (Aif b P d P' d' Q)
      (at level 80, right associativity)  : annot.
Notation "'WHILE' b 'DO' {{ Pbody }} d {{ Ppost }}"
      := (Awhile b Pbody d Ppost)
      (at level 80, right associativity) : annot.
Notation "'=>>' {{ P }} d"
      := (Apre P d)
      (at level 90, right associativity)  : annot.
Notation "d '=>>' {{ P }}"
      := (Apost d P)
      (at level 80, right associativity)  : annot.
Notation "{{ P }} d"
      := (annotated P d)
      (at level 90)  : annot.

(* We can erase all the annotations from an annotated program to get only the
   statements *)
Fixpoint extract (a : AStm) : Stm :=
  match a with
  | Aass x y _        => x ::= y
  | Askip _           => SKIP
  | Acomp a1 a2       => (extract a1 ; extract a2)
  | Aif b _ a1 _ a2 _ => IF_ b THEN extract a1 ELSE extract a2
  | Awhile b _ a _    => WHILE b DO extract a
  | Apre _ a          => extract a
  | Apost a _         => extract a
  end.

Definition extract_ann (ann : Annotated) : Stm :=
  match ann with
  | annotated P a => extract a
  end.

(* AStm S together with a precondition P determines a Hoare triple
   {{P}} (extract S) {{post S}}, where post is defined as follows: *)
Fixpoint post (a : AStm) : Assertion :=
  match a with
  | Aass x y Q             => Q
  | Askip P                => P
  | Acomp a1 a2            => post a2
  | Aif  _ _ a1 _ a2 Q     => Q
  | Awhile b Pbody c Ppost => Ppost
  | Apre _ a               => post a
  | Apost c Q              => Q
  end.

(* Extracting precondition and the postcondition *)
Definition pre_ann (ann : Annotated) : Assertion :=
  match ann with
  | annotated P a => P
  end.

Definition post_ann (ann : Annotated) : Assertion :=
  match ann with
  | annotated P a => post a
  end.

(* An annotated program is correct if the following holds *)
Definition ann_correct (ann : Annotated) :=
  {{pre_ann ann}} (extract_ann ann) {{post_ann ann}}.

(* The function verification_conditions takes a AStm a together with a
   precondition P and returns a proposition that, if it can be proved,
   implies that the triple {{P}} (extract S) {{post S}} is valid. *)
Fixpoint verification_cond (P : Assertion) (a : AStm) : Prop :=
  match a with
  | Aass x y Q =>
      (P =>> Q [x |-> y])
  | Askip Q =>
      (P =>> Q)
  | Acomp a1 a2 =>
      verification_cond P a1
      /\ verification_cond (post a1) a2
  | Aif b P1 a1 P2 a2 Q =>
      ((fun st => bassn b st /\ P st) =>> P1)
      /\ ((fun st => (bassn2 b st) /\ P st) =>> P2)
      /\ (post a1 =>> Q) /\ (post a2 =>> Q)
      /\ verification_cond P1 a1
      /\ verification_cond P2 a2
  | Awhile b Pbody a Ppost =>
      (P =>> post a)
      /\ ((fun st => bassn b st /\ post a st ) =>> Pbody)
      /\ ((fun st => (bassn2 b st) /\ post a st) =>> Ppost)
      /\ verification_cond Pbody a
  | Apre P' a =>
      (P =>> P') /\ verification_cond P' a
  | Apost a Q =>
      verification_cond P a /\ (post a =>> Q)
  end.

Lemma Bev : forall (b:Bexp) (st:State),
  (~B[[b]] st) = (~ (B[[b]]) st).
Proof.
  intros.
  unfold bassn2.
  unfold bassn.
  reflexivity.
Qed.

(* This theorem proves that verification_conditions works correctly *)
Theorem verification_correct : forall a P,
  verification_cond P a -> {{P}} (extract a) {{post a}}.
Proof.
  induction a; intros P H; simpl in *.
  - (* ass *)
    eapply consp_pre.
    apply assp.
    assumption.
  - (* skip *)
    eapply consp_pre.
    apply skipp.
    assumption.
  - (* comp *)
    destruct H as [H1 H2].
    eapply compp.
    apply IHa2.
    apply H2.
    apply IHa1.
    apply H1.
  - (* if *)
    destruct H as [HPre1 HPre2].
    destruct HPre2 as [HPre2 Hd1].
    destruct Hd1 as [Hd1 Hd2].
    destruct Hd2 as [Hd2 HThen].
    destruct HThen as [HThen HElse].
    apply IHa1 in HThen. clear IHa1.
    apply IHa2 in HElse. clear IHa2.
    apply ifp.
      + eapply consp_post with (Q':=post a2); eauto.
         eapply consp_pre; eauto.
      + eapply consp_post with (Q':=post a4); eauto.
         eapply consp_pre; eauto.
  - (* while *)
    destruct H as [HPre Hbody1].
    destruct Hbody1 as [Hbody1 Hpost1].
    destruct Hpost1 as [Hpost1 Hd].
    eapply consp_pre; eauto.
    eapply consp_post; eauto.
    apply whilep.
    eapply consp_pre; eauto.
  - (* pre *)
    destruct H as [HP Hd].
    eapply consp_pre.
    apply IHa.
    apply Hd.
    assumption.
  - (* post *)
    destruct H as [Hd HQ].
    eapply consp_post.
    apply IHa.
    apply Hd.
    assumption.
Qed.

(* Now we can verify an entire annotated program *)
Definition verification_cond_ann (ann : Annotated) : Prop :=
  match ann with
  | annotated P a => verification_cond P a
  end.

Lemma verification_correct_ann : forall ann,
  verification_cond_ann ann -> ann_correct ann.
Proof.
  intros [P a].
  apply verification_correct.
Qed.

(* verification_conditions generates many often trivial subgoals. We can make
   a tactic that can solve these subgoals on itself by using lemmas. We first
   need to define these lemmas. Some of these lemmas have already been used
   in other Coq files but we will redefine them for clarity here. Other lemmas
   used are in the Coq standard library. *)
Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [|Hs].
   - subst.
     split.
     reflexivity.
     reflexivity.
   - split.
     + intros contra.
       discriminate contra.
     + intros H.
       rewrite H in Hs.
       destruct Hs.
       reflexivity.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y.
  rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false.
  reflexivity.
Qed.

Lemma t_update_eq : forall (m : total_map nat) x v,
    (x !-> v , m) x = v.
Proof.
  unfold t_update.
  intros.
  destruct (eqb_string x0 x0) eqn:E.
  - reflexivity.
  - apply eqb_string_false_iff in E.
    unfold not in E.
    destruct E.
    reflexivity.
Qed.

Theorem t_update_neq : forall (m : total_map nat) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v , m) x2 = m x2.
Proof.
  unfold t_update.
  intros.
  destruct (eqb_string x1 x2 ) eqn:E.
  - unfold not in H.
    rewrite eqb_string_true_iff in E.
    destruct H.
    apply E.
  - reflexivity.
Qed.

(* This is the tactic, taken from Software Foundations chapter Hoare2 *)
Tactic Notation "verify" :=
  apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold bassn in *;unfold bassn2 in *;
  unfold Beval in *; unfold Aeval in *;
  unfold assn_sub; intros;
  repeat rewrite t_update_eq;
  repeat (rewrite t_update_neq; [| (intro X; inversion X)]);
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  repeat
    match goal with
      [st : State |- _] =>
        match goal with
          [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try omega.

End Annotated.

(*--------------------------------Soundness----------------------------------*)
(* Valid Hoare triple: For all states s and s', if P s = tt and <S, s> -> s'
     then Q s' = tt.
   Provable Hoare triple: There exists an inference tree with {P} S {Q} as
     conclusion.
   Soundness: The inference system of the axiomatic semantics is sound,
     that is for every partial correctness formula {P} S {Q} we have
     (provable) {P} S {Q} implies (valid) {P} S {Q}.
   We already defined when a Hoare triple is valid in the previous chapter,
   we can already define what it means for a Hoare triple to be provable. *)

(* Provability *)
Inductive hoare_proof : Assertion -> Stm -> Assertion -> Type :=
  | ass_p : forall Q x a,
      hoare_proof (assn_sub x a Q) (x ::= a) Q
  | skip_p : forall P,
      hoare_proof P (SKIP) P
  | comp_p  : forall P S1 Q S2 R,
      hoare_proof P S1 Q ->
      hoare_proof Q S2 R ->
      hoare_proof P (S1;S2) R
  | if_p : forall P Q b S1 S2,
    hoare_proof (fun st => P st /\ bassn b st) S1 Q ->
    hoare_proof (fun st => P st /\ ~(bassn b st)) S2 Q ->
    hoare_proof P (IF_ b THEN S1 ELSE S2 ) Q
  | while_p : forall P b S,
    hoare_proof (fun st => P st /\ bassn b st) S P ->
    hoare_proof P (WHILE b DO S ) (fun st => P st /\ ~ (bassn b st))
  | cons_p  : forall (P Q P' Q' : Assertion) S,
    hoare_proof P' S Q' ->
    (forall s, P s -> P' s) ->
    (forall s, Q' s -> Q s) ->
    hoare_proof P S Q.

(* Now we can prove that axiomatic semantics is sound *)
Theorem hoare_proof_sound : forall P S Q,
  hoare_proof P S Q -> {{P}} S {{Q}}.
Proof.
  intros.
  induction X.
  - unfold hoare_triple.
    intros.
    inversion H; subst.
    apply H0.
  - unfold hoare_triple.
    intros.
    inversion H; subst.
    apply H0.
  - unfold hoare_triple.
    intros.
    inversion H; subst.
    apply (IHX2 st'0 st').
    apply H6.
    apply (IHX1 st st'0). 
    apply H3.
    apply H0.
  - unfold hoare_triple.
    intros.
    inversion H; subst.
    + apply (IHX1 st st').
      apply H7.
      split.
      apply H0.
      apply H6.
    + apply (IHX2 st st').
      apply H7.
      split.
      apply H0.
      apply Bexp_eval_false.
      apply H6.
  - unfold hoare_triple.
    intros.
    remember (WHILE b DO S ) as wStm eqn:HeqwStm.
    induction H.
    + inversion HeqwStm.
    + inversion HeqwStm.
    + inversion HeqwStm.
    + inversion HeqwStm.
    + inversion HeqwStm.
    + inversion HeqwStm; subst.
      apply IHSeval2.
      reflexivity.
      apply (IHX st st').
      apply H1.
      split.
      apply H0.
      apply Bexp_eval_true.
      apply H.
    + inversion HeqwStm; subst.
      split.
      apply H0.
      apply Bexp_eval_false.
      apply H.
  - unfold hoare_triple.
    intros.
    apply q.
    apply (IHX st st').
    apply H.
    apply p.
    apply H0.
Qed.

(*--------------------------------Completeness-------------------------------*)
(* Completeness: The inference system of the axiomatic semantics is complete,
   that is for every partial correctness formula {P} S {Q} we have
     (valid) {P} S {Q} implies (provable) {P} S {Q}.
   We can prove this using the weakest liberal precondition. 
   wlp(S, Q) s = tt if and only if for all states s', if <S, s> -> s' then 
     Q s' = tt. *)


Definition wlp (S : Stm) (Q : Assertion) : Assertion :=
  fun s => forall s', << S , s >> --> s' -> Q s'.

(* wlp has two important properties,
   property 1: (valid) {wlp(S, Q)} S {Q}
   property 2: If (valid p) {P} S {Q} then P => wlp(S, Q). *)
Lemma wlp_property1:
  forall S Q,
  {{wlp S Q}} S {{Q}}.
Proof.
  intros.
  unfold wlp.
  unfold hoare_triple.
  intros.
  apply H0.
  apply H.
Qed.

Lemma wlp_property2:
  forall P S Q,
      {{P}} S {{Q}} 
    -> 
      forall s, P s -> wlp S Q s.
Proof.
  intros.
  unfold wlp.
  unfold hoare_triple in H.
  intros.
  apply (H s).
  - apply H1.
  - apply H0.
Qed.

(* Now we can prove that Axiomatic Semantics is complete *)
Theorem hoare_proof_complete: forall P S Q,
  {{P}} S {{Q}} -> hoare_proof P S Q.
Proof.
  intros P S.
  generalize dependent P.
  induction S; intros P Q HT.
  - eapply cons_p.
    + eapply ass_p.
    + intro s.
      apply HT.
      econstructor.
      reflexivity.
    + intros.
      apply H.
  - eapply cons_p.
    + eapply skip_p.
    + intros.
      eapply H.
    + intro st. 
      apply HT.
      apply skip_ns.
  - apply comp_p with (wlp S2 Q).
    + eapply IHS1.
      unfold wlp.
      intros s s' E1 H. 
      intros s'' E2.
      eapply HT. 
      * econstructor.
        eapply E1.
        eapply E2.
      * apply H.
    + eapply IHS2.
      intros s s' E1 H.
      apply H.
      apply E1.
  - eapply if_p.
     + apply IHS1.
       intros s s' H [H1 H2].
       eapply HT.
       * apply if_tt_ns.
         apply H2.
         apply H.
       * apply H1.
     + apply IHS2.
       intros s s' H [H1 H2].
       eapply HT.
       * apply if_ff_ns.
         unfold bassn in H2.
         apply not_true_is_false in H2.
         apply H2.
         apply H.
       * apply H1.
  - eapply cons_p with (P' := wlp (WHILE b DO S ) Q).
    + apply while_p.
      apply IHS.
      intros s s' H [H2 H3] s'' H4.
      assert(<<(WHILE b DO S ) , s >> --> s'').
      * eapply while_tt_ns. 
        apply H3.
        apply H.
        apply H4.
      * eapply wlp_property1. 
        { apply H0. }
        { apply H2. }
    + apply wlp_property2. 
      apply HT.
    + intros s [H1 H2]. 
      eapply wlp_property1.
      * assert(<<(WHILE b DO S ),  s>> -->  s).
        { apply while_ff_ns. 
           unfold bassn in H2.
           apply not_true_is_false in H2.
           apply H2.
        }
        { apply H. }
      * apply H1. 
Qed.