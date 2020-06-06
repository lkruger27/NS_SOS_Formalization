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

Local Open Scope Z.
(*-----------------------------------Lemmas----------------------------------*)
(* To prove that the state is correct in proofs with blocks we need some
   supplementary lemmas. They are needed for blocks and procedures, so we
   define them here *)

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

Theorem t_update_neq : forall (m : total_map Z) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v , m) x2 = m x2.
Proof.
  intros m x1 x2 v H.
  unfold t_update.
  destruct (eqb_string x1 x2) eqn:E.
  apply eqb_string_false_iff in H.
  rewrite H in E.
  discriminate E.
  reflexivity.
Qed.

Lemma eqb_string_sym : forall x y : string,
  eqb_string x y = eqb_string y x.
Proof.
  unfold eqb_string.
  intros.
  destruct (string_dec x y), (string_dec y x).
  + reflexivity.
  + rewrite e in n.
    unfold not in n.
    destruct n.
    reflexivity.
  + rewrite e in n.
    unfold not in n.
    destruct n.
    reflexivity.
  + reflexivity.
Qed.

Lemma not_sym : forall (x y : string),
  x <> y <-> y <> x.
Proof.
  split; intros;
  apply eqb_string_false_iff;
  apply eqb_string_false_iff in H.
  assert (eqb_string x y = eqb_string y x).
    + apply eqb_string_sym.
    + rewrite H0 in H. apply H.
    + apply eqb_string_false_iff in H.
      apply eqb_string_false_iff in H.
      assert (eqb_string x y = eqb_string y x).
      * apply eqb_string_sym.
      * rewrite <- H0 in H. apply H.
Qed.

(*-----------------------------------Blocks----------------------------------*)
(* We can make an extensions of While that includes scopes. The extensions
   called Blocks has local variables. for this we need to define a set of
   variables and add or remove variables when we move in/out of scopes.
   The definition of the set DV is a slightly adapted version of the set
   definition from the standard library of Coq. *)
Declare Scope b_scope.
Open Scope b_scope.

Definition DV := list string.

Definition empty_DV : DV := nil.

(* Add a variable to the set *)
Fixpoint DV_add (x : string) (X : DV) : DV :=
  match X with
  | nil => x :: nil
  | x1 :: X1 =>
      match string_dec x x1 with
      | left _ => x1 :: X1
      | right _ => x1 :: DV_add x X1
      end
  end.

(* Check if a variable is a member of the set *)
Fixpoint DV_mem (x : string) (X : DV) : bool :=
    match X with
    | nil => false
    | x1 :: X1 =>
        match string_dec x x1 with
        | left _ => true
        | right _ => DV_mem x X1
        end
    end.

(* Syntax variable declarations*)
Inductive Dv : Type :=
  | dec_v (x : string) (a : Aexp) (Dv1 : Dv)
  | empty_v.

Notation "'var' x ':=' a ';' Dv1" := (dec_v x a Dv1)
  (at level 60, a at next level, right associativity) : b_scope.

Notation "'var' x ':=' a" := (var x := a; empty_v)
  (at level 60, a at next level, right associativity) : b_scope.

(* Semantics variable declarations *)
Fixpoint DVeval (dv : Dv) : DV :=
  match dv with
  | dec_v x a Dv1 => DV_add x (DVeval Dv1)
  | empty_v => nil
  end.

Inductive Stm : Type :=
  | ass (x : string) (a : Aexp)
  | skip
  | comp (S1 S2 : Stm)
  | if_ (b : Bexp) (S1 S2 : Stm)
  | while (b : Bexp) (S : Stm)
  | block (Dv1 : Dv) (S : Stm).

Bind Scope b_scope with Stm.
Notation "x '::=' a" :=
  (ass x a) (at level 60) : b_scope.
Notation "'SKIP'" :=
   skip : b_scope.
Notation "s1 ; s2" := 
  (comp s1 s2) (at level 80, right associativity) : b_scope.
Notation "'WHILE' b 'DO' s " :=
  (while b s) (at level 80, right associativity) : b_scope.
Notation "'IF_' b 'THEN' s1 'ELSE' s2 " := 
  (if_ b s1 s2) (at level 80, right associativity) : b_scope.
Notation "'BEGIN' Dv ',' S 'END'" :=
  (block Dv S) (at level 80, S at level 9, right associativity) : b_scope.

(* Semantics rules Dv and notation for transitions *)
Reserved Notation "'<<' S ',' st '>>' '-->D' st'"
                  (at level 40).

Inductive SDecV : Dv -> State -> State -> Prop :=
  | none_ns : forall st,
      SDecV empty_v st st
  | var_ns : forall st st' a1 n (x : string) (Dv1 : Dv),
      Aeval st a1 = n ->
      SDecV Dv1 (t_update st x n) st' ->
      SDecV (dec_v x a1 Dv1) st st'
where "'<<' S ',' st '>>' '-->D' st'" := (SDecV Dv st st).

(* Update the set of variables *)
Definition var_update (s s' : State) (X : DV) (a : string) :=
  fun a => if DV_mem a X then (s a) else (s' a).

(* semantics Stm and notation for transitions *)
Reserved Notation "'<<' S ',' st '>>' '-->' st'"
                  (at level 40).

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
  | block_ns : forall Dv S st st' st'' (x:string),
      SDecV Dv st st' ->
      Seval st' S st'' ->
      Seval st (BEGIN Dv, S END)
               (var_update st st'' (DVeval Dv) x).

Notation "<< s , st >> --> st'" := (Seval st s st')
                                 (at level 40).

(* stm_eq was defined and explained in ApplicationNS:Natural Semantics.
   This theorem allows to eapply the rules. *)
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

(*-----------------------------Dynamic_Scopes--------------------------------*)
(* We can also make an extension of While that has Blocks and Procedures.
   The body of procedures can hold statements that need to be executed at
   certain points in the program. We want to store the body of the procedure
   and if we call the procedure, search for the body of the procedure and
   execute it. There are two types of procedures: procedures with static scope
   and procedures with dynamic scopes. In the dynamic procedure scopes we
   execute the current definition of the procedure. In static procedure scopes
   we execute the original definition of the procedure at the time of
   declaration. First, we will handle dynamic procedure scopes. *)
Module Dynamic.

Open Scope while_scope.
Local Open Scope Z.
Declare Scope pro.
Open Scope pro.

(* Pname ranges over procedure names *)
Definition Pname := string.
Definition p : string := "p".
Definition q : string := "q".

(* We need a new type Dp but Stm uses Dp and Dp uses Stm so we define them 
   together with the keyword 'with'. *)
Inductive Stm : Type :=
  | ass (x : string) (a : Aexp)
  | skip
  | comp (S1 S2 : Stm)
  | if_ (b : Bexp) (S1 S2 : Stm)
  | while (b : Bexp) (S : Stm)
  | block (Dv1 : Dv) (Dp1 : Dp) (S : Stm)
  | call (p : Pname)
with Dp : Type :=
  | dec_p (p : Pname) (S : Stm) (Dp1 : Dp)
  | empty_p.

(* We need to keep track of which procedures are currently in the environment.
   For this we need a partial map from procedure names to statements *)
Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v , m).
Notation "x '|->' v ',' m" := (update m x v)
  (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Definition Env := partial_map Stm.

Bind Scope pro with Stm.
Notation "x '::=' a" :=
  (ass x a) (at level 60) : pro.
Notation "'SKIP'" :=
   skip : pro.
Notation "s1 ; s2" := 
  (comp s1 s2) (at level 80, right associativity) : pro.
Notation "'WHILE' b 'DO' s " :=
  (while b s) (at level 80, right associativity) : pro.
Notation "'IF_' b 'THEN' s1 'ELSE' s2 " := 
  (if_ b s1 s2) (at level 80, right associativity) : pro.
Notation "'BEGIN' Dv ',' Dp ',' S 'END'" :=
  (block Dv Dp S) (at level 80, right associativity) : pro.
Notation "'CALL' p" :=
  (call p) (at level 80, right associativity) : pro.

Notation "'proc' p 'is' S ';' Dp1" := (dec_p p S Dp1)
  (at level 60, S at next level, right associativity) : pro.
Notation "'proc' p 'is' S" := (dec_p p S empty_p)
  (at level 60, S at next level, right associativity) : pro.

(* We need to be able to update the environment *)
Fixpoint UpdP (dp : Dp) (envp : Env) : Env :=
  match dp with
  | dec_p p s dp => UpdP dp (update envp p s)
  | empty_p => envp
  end.

(* Natural semantics with dynamic scope for procedures. It also includes
   the new transition. *)
Inductive Seval : Env -> State -> option Stm -> State -> Prop :=
  | ass_ns  : forall envp st a1 n x,
      Aeval st a1 = n ->
      Seval envp st (Some (x ::= a1)) (t_update st x n)
  | skip_ns : forall envp st,
      Seval envp st (Some SKIP) st
  | comp_ns : forall envp s1 s2 st st' st'',
      Seval envp st (Some s1) st' ->
      Seval envp st' (Some s2) st'' ->
      Seval envp st (Some (s1 ; s2)) st''
  | if_tt_ns : forall envp st st' b1 s1 s2,
      Beval st b1 = true ->
      Seval envp st (Some s1) st' ->
      Seval envp st (Some (IF_ b1 THEN s1 ELSE s2)) st'
  | if_ff_ns : forall envp st st' b1 s1 s2,
      Beval st b1 = false ->
      Seval envp st (Some s2) st' ->
      Seval envp st (Some (IF_ b1 THEN s1 ELSE s2)) st'
  | while_tt_ns : forall envp st st' st'' b1 s1,
      Beval st b1 = true ->
      Seval envp st (Some s1) st' ->
      Seval envp st' (Some (WHILE b1 DO s1)) st'' ->
      Seval envp st (Some (WHILE b1 DO s1)) st''
  | while_ff_ns : forall envp b1 st s1,
      Beval st b1 = false ->
      Seval envp st (Some (WHILE b1 DO s1)) st
  | block_ns : forall envp (dv:Dv) (dp:Dp) S st st' st'' x,
      SDecV dv st st' ->
      Seval (UpdP dp envp) st' (Some S) st'' ->
      Seval envp st (Some (BEGIN dv, dp, S END))
                    (var_update st st'' (DVeval dv) x)
  | call_rec_ns : forall envp st st' p,
      Seval envp st (envp p) st' ->
      Seval envp st (Some (CALL p)) st'.
Notation "envp |- << s , st >> --> st'" := (Seval envp st s st')
                                 (at level 40).

Theorem stm_eq_env :
  forall envp S s s' s'',
  envp |- << S, s >> --> s' ->
  s' = s'' ->
  envp |- << S, s >> --> s''.
Proof.
  intros.
  rewrite H0 in H.
  apply H.
Qed.

End Dynamic.

(*------------------------------Mixed_Scopes---------------------------------*)
(* Now we will handle static scopes. For this we need a different kind of
   environment. Luckily, we can also add a rule for dynamic scopes using this
   environment *)
Module Mixed.
Declare Scope stat.
Open Scope stat.

Definition Pname := string.
Definition p : string := "p".
Definition q : string := "q".

Inductive Stm : Type :=
  | ass (x : string) (a : Aexp)
  | skip
  | comp (S1 S2 : Stm)
  | if_ (b : Bexp) (S1 S2 : Stm)
  | while (b : Bexp) (S : Stm)
  | block (Dv1 : Dv) (Dp1 : Dp) (S : Stm)
  | call (p : Pname)
with Dp : Type :=
  | dec_p (p : Pname) (S : Stm) (Dp1 : Dp)
  | empty_p.

(* This is the new environment. We need a more difficult function because
   it is a recursive definition. It can be problematic that this function is
   recursive. However, the environments are only growing from the empty
   environment so this is no problem *)
Inductive Envp : Type :=
  | static_env (f : Pname -> option (Stm * Envp)).

(* The function to extend the environment *)
Definition extend (e : Envp) (p : Pname) (s : Stm) : Envp :=
  match e with
  | static_env f => static_env (fun p' : Pname 
    => if eqb_string p p' then (Some (s,e)) else f p')
  end.

(* Definition of the empty environment *)
Definition empty_envp := static_env (fun _ => None).

Bind Scope stat with Stm.
Notation "x '::=' a" :=
  (ass x a) (at level 60) : stat.
Notation "'SKIP'" :=
   skip : stat.
Notation "s1 ; s2" := 
  (comp s1 s2) (at level 80, right associativity) : stat.
Notation "'WHILE' b 'DO' s " :=
  (while b s) (at level 80, right associativity) : stat.
Notation "'IF_' b 'THEN' s1 'ELSE' s2 " := 
  (if_ b s1 s2) (at level 80, right associativity) : stat.
Notation "'BEGIN' Dv ',' Dp ',' S 'END'" :=
  (block Dv Dp S) (at level 80, right associativity) : stat.
Notation "'CALL' p" :=
  (call p) (at level 80, right associativity) : stat.

Notation "'proc' p 'is' S ';' Dp1" := (dec_p p S Dp1)
  (at level 60, S at next level, right associativity) : stat.
Notation "'proc' p 'is' S" := (dec_p p S empty_p)
  (at level 60, S at next level, right associativity) : stat.

(* The function to update the environment *)
Fixpoint UpdP2 (dp : Dp) (envp : Envp) : Envp :=
  match dp with
  | dec_p p s dp => UpdP2 dp (extend envp p s)
  | empty_p => envp
  end.

(* We need to be able to get the Stm or the Envp from (Stm * Envp). This can
   be accomplished with the following functions. Inspired by fst and snd
   functions from the Coq standard library. *)
Definition fst2 (p: option (Stm * Envp)) :=
  match p with
  | Some (x, y) => x
  | None => SKIP
end.
Definition first (e : Envp) (p : Pname) := 
  match e with
  | static_env f => fst2 (f p)
  end.

Definition snd2 (p: option (Stm * Envp)) :=
  match p with
  | Some (x, y) => y
  | None => empty_envp
end.
Definition second (e : Envp) (p : Pname) := 
  match e with
  | static_env f => snd2 (f p)
  end.

(* Now we can define the natural semantics for the While extensions with both
   dynamic and static scopes. Make sure to only use either call_ns or
   call_rec_ns in proofs. They should not be mixed. *)
Inductive Seval : Envp -> State -> Stm -> State -> Prop :=
  | ass_ns  : forall envp st a1 n x,
      Aeval st a1 = n ->
      Seval envp st (x ::= a1) (t_update st x n)
  | skip_ns : forall envp st,
      Seval envp st SKIP st
  | comp_ns : forall envp s1 s2 st st' st'',
      Seval envp st s1 st' ->
      Seval envp st' s2 st'' ->
      Seval envp st (s1 ; s2) st''
  | if_tt_ns : forall envp st st' b1 s1 s2,
      Beval st b1 = true ->
      Seval envp st s1 st' ->
      Seval envp st (IF_ b1 THEN s1 ELSE s2) st'
  | if_ff_ns : forall envp st st' b1 s1 s2,
      Beval st b1 = false ->
      Seval envp st s2 st' ->
      Seval envp st (IF_ b1 THEN s1 ELSE s2) st'
  | while_tt_ns : forall envp st st' st'' b1 s1,
      Beval st b1 = true ->
      Seval envp st s1 st' ->
      Seval envp st' (WHILE b1 DO s1) st'' ->
      Seval envp st (WHILE b1 DO s1) st''
  | while_ff_ns : forall envp b1 st s1,
      Beval st b1 = false ->
      Seval envp st (WHILE b1 DO s1) st
  | block_ns : forall envp (dv:Dv) (dp:Dp) S st st' st'' x,
      SDecV dv st st' ->
      Seval (UpdP2 dp envp) st' S st'' ->
      Seval envp st (BEGIN dv, dp, S END)
                    (var_update st st'' (DVeval dv) x)
  | call_ns : forall (envp:Envp) st st' p,
      Seval (second envp p) st (first envp p) st' ->
      Seval envp st (CALL p) st'
  | call_rec_ns : forall envp st st' p,
      Seval envp st (first envp p) st' ->
      Seval envp st (CALL p) st'.
Notation "envp |- << s , st >> --> st'" := (Seval envp st s st')
                                 (at level 40).

Theorem stm_eq_env:
  forall envp S s s' s'',
  envp |- << S, s >> --> s' ->
  s' = s'' ->
  envp |- << S, s >> --> s''.
Proof.
  intros.
  rewrite H0 in H.
  apply H.
Qed.

End Mixed.