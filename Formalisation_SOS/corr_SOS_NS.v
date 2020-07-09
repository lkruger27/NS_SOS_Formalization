Set warnings "-notation-overridden,-parsing".
Require Import Framework_common.
Require Import Framework_SOS.
Require Import Framework_NS.
Require Import multi_k.
Require Import SOS_star_k.
From Coq Require Import BinNat.
From Coq Require Import omega.Omega.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Bool.Bool.



Check nat_ind.
Theorem strong_induction:
forall P : nat -> Prop,
  P 0 ->
  (forall n : nat, (forall k : nat, ((k <= n)%nat -> P k)) -> P (S n))
  ->
  forall n : nat, P n.
Proof.
intros.
induction n.
- assumption.
- apply H0. intros.
  inversion H1.
    apply IHn. subst.
  induction H1. assumption.
  apply IHle.
  subst.
exfalso.

  
Admitted. 


Theorem fin_stm_eq:
  forall s conf,
  <<s>>==>* conf ->
  conf = <<s>>.
Proof.
intros.
inversion H. reflexivity. subst.
inversion H0.
Qed. 
   
Theorem fn_eq_conf:
  forall s s',
  <<s>> = <<s'>> -> s = s'.
Proof.
intros. inversion H. 
reflexivity.
Qed.
   
Definition sos_ns_one:
forall S s s',
  <<S,s>> ==> <<s'>>
  ->
  <<S,s>> --> s'.
Proof.
intros. inversion H; subst.
apply skip_ns.
apply ass_ns. reflexivity.
Qed.
   
Definition sos_ns_k (k:nat):=
forall S s s',
  <<S,s>>==>[k]<<s'>>
  ->
  <<S,s>>-->s'.


Lemma sos_k_implies_ns:
forall k,
  sos_ns_k k.
Proof.
intros.
unfold sos_ns_k. 
induction k using strong_induction.
- intros. inversion H.
- rename k into k0.
  intros.
  inversion H0; subst.
  induction S.
  + (*ass*)
    assert (y = <<(x !-> A[[ a]] s, s)>>).
    {
      apply one_step_deterministic with << x ::= a, s >>. 
      assumption. apply SSAss. reflexivity. 
    }
    subst.
    assert ( k0 = 0 /\ <<s'>> = <<(x !-> A[[ a]] s, s)>>).
    {
      apply state_k_zero. assumption.
    }
    inversion H1. inversion H5.
    subst.
    apply ass_ns. reflexivity.
  + (*skip*)
    assert (y = <<s>>).
    {
      apply one_step_deterministic with << SKIP, s >>. 
      assumption. apply SSSkip.
    }
    subst.
    assert ( k0 = 0 /\ <<s'>> = << s>>).
    {
      apply state_k_zero. assumption.
    }
    inversion H1. inversion H5.
    subst.
    apply skip_ns.
  + (*comp*)
    apply comp_complete in H0.
    destruct H0. destruct H0. destruct H0. destruct H0.
    apply comp_ns with x.
    *     induction x1. 
          --  assert ( << S2, x >> = << s' >>).
              apply zero_steps. destruct H1.  assumption.
            inversion H4.
          -- apply  H with x0.
              generalize dependent x0.
              induction x0.
               ++ intros. omega.
               ++ intros. destruct H1.
                  assert (S x0 = S k0 - S x1). omega.
                  rewrite H5. omega.
               ++  assumption.
    *     induction x0. 
          --  assert ( << S1, s >> = << x >>).
              apply zero_steps. destruct H1.  assumption.
            inversion H4.
          -- apply  H with x1.
              generalize dependent x1.
              induction x1.
               ++ intros. omega.
               ++ intros. destruct H1.
                  assert ( S x1 =  S k0 - S x0). omega.
                  rewrite H5. omega.
               ++ destruct H1.  assumption.
  + (*if*)
    assert (y = <<S1, s>> \/y = <<S2, s>>).
    {
      inversion H2; subst. left. reflexivity.
                           right. reflexivity.
    }
    destruct H1; subst.
    * (* where y = <<S1, s>> *)
      inversion H2; subst.
      --  (*b evalates to true*)
         apply if_tt_ns.
            assumption.
            apply H with k0. reflexivity. assumption.
      --(*b evalates to false*)
          apply if_ff_ns.
            assumption.
            apply H with k0. reflexivity. assumption.
   *  (* where y = <<S2, s>> *)
      inversion H2; subst.
      -- (*b evalates to true*)
          apply if_tt_ns.
            assumption.
            apply H with k0. reflexivity. assumption.
      -- (*b evalates to false *)
          apply if_ff_ns.
            assumption.
            apply H with k0. reflexivity. assumption.
  + (*while*)
assert (y = <<IF_ b THEN (S; WHILE b DO S) ELSE SKIP, s>>).
        {
          inversion H2; subst. reflexivity.
        }
        subst.
        inversion H3; subst.
assert (y = <<S; WHILE b DO S, s>> \/ y = <<SKIP, s>>).
        {
          inversion H1. left. reflexivity.
                        right. reflexivity.
        }
        destruct H5; subst.
        * (* y = <<S; WHILE b DO S, s>>, hence b evaluates to true*)
          apply comp_complete in H4.
          destruct H4.  destruct H4. destruct H4. destruct H4. destruct H5.       

          eapply while_tt_ns with x.
            -- inversion H1; subst. assumption.
            -- apply H with x0. omega. assumption.
            -- apply H with x1. omega. assumption.
        * (* y = <<SKIP, s>> , hence b evaluates to true*)
          inversion H1; subst.
          inversion H4; subst.
          inversion H5; subst.
          apply state_k_zero in H7. destruct H7. inversion H8.
          apply while_ff_ns. assumption.
Qed.            
        


Lemma sos_implies_ns:
forall S s s',
  <<S,s>>==>*<<s'>>
  ->
  <<S,s>>-->s'.
Proof.
intros.
apply star_implies_k in H.
inversion H.
rename x into k. clear H.
(*careful to have the genralizations in the same order.
Otherwise, the premises will not match.*)
generalize dependent s'.
generalize dependent s.
generalize dependent S.
generalize dependent k.
apply sos_k_implies_ns.
Qed.



Lemma ns_k_implies_sos:
forall S s s',
  <<S,s>>-->s'
  ->
exists k,
  <<S,s>>==>[k]s'.
Proof.
intros.
  induction H.
  - (* ass *) exists 1. eapply multikstep. apply SSAss.
    apply H. eapply multikrefl.
  - (* skip *)exists 1. eapply multikstep. apply SSSkip. eapply multikrefl.
  - (*comp*) destruct IHSeval1. destruct IHSeval2.
             (*apply half_comp in H1.*)
             (*why does th book want us to use half_comp?*)
             (*it is a bit uncomfrotable yo use*)
              assert (
             forall k2 S1 s S2 s' s'',
                  <<S1, s>> ==>[x] << s'>>
                  ->
                  << S2, s'>> ==>[k2] <<s''>>
                  ->
                  exists k,
           <<S1; S2, s>> ==>[k] <<s''>> /\ k = x+k2).

             { apply exec_comp.
             }
             induction H3 with x0 s1 st s2 st' st''.
             * exists x1. destruct H4. assumption.
             *  assumption.
             * assumption.
  - (*if_tt*) destruct IHSeval. clear S.
    exists (S x). apply multikstep with << s1, st >>.
     * apply SSIftrue. assumption.
     *  assumption.
  - (*if_ff*)destruct IHSeval. clear S.
    exists (S x). apply multikstep with << s2, st >>.
     * apply SSIffalse. assumption.
     *  assumption.
  - (*while_tt*)
    destruct IHSeval2. destruct IHSeval1. clear S.
    exists (S (S (x0+x))). 
    apply multikstep with 
        <<IF_ b THEN (s0; WHILE b DO s0) ELSE SKIP, st>>.
        * apply SSWhile.
        * apply multikstep with 
          << s0; WHILE b DO s0, st>>.
          --  apply SSIftrue. assumption.
          -- assert (forall k2 S1 s S2 s' s'',
                  <<S1, s>> ==>[x0] << s'>>
                  ->
                  << S2, s'>> ==>[k2] <<s''>>
                  ->
                  exists k,
           <<S1; S2, s>> ==>[k] <<s''>> /\ k = x0+k2).

             { apply exec_comp.
             }
             induction H4
               with x s0 st (WHILE b DO s0) st' st''.
             ++ destruct H5. subst. assumption.
             ++ assumption.
             ++ assumption.
  - (*while_ff*)
    exists 3.
    apply multikstep with 
        <<IF_ b THEN (s0; WHILE b DO s0) ELSE SKIP, st>>.
    + apply SSWhile.
    + apply multikstep with <<SKIP, st>>.
      * apply SSIffalse. assumption.
      * apply multikstep with <<st>>.
        apply SSSkip. apply zero_steps_rev. reflexivity.
Qed.

Lemma ns_implies_sos:
forall S s s',
  <<S,s>>-->s'
  ->
  <<S,s>>==>*s'.
Proof.
   intros.
   assert(exists k,
  <<S,s>>==>[k]s').
  {
    apply ns_k_implies_sos. assumption.
  }
  destruct H0.
  apply k_implies_star with x.
  assumption.
Qed.

Theorem ns_eq_sos:
forall S s s',
  <<S,s>>-->s'
  <->
  <<S,s>>==>*s'.
Proof.
intros.
split.
apply ns_implies_sos.
apply sos_implies_ns.
Qed.