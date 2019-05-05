(* chains and anti-chains *)

Require Import Relations_1.
Require Import Ensembles.

Section Chains.

  Context {U : Type} (R : Relation U) (Ord : Order U R).

  Definition chain (X : Ensemble U) :=
    (forall (x y : U), In U X x -> In U X y -> R x y \/ R y x).

  Definition anti_chain (X : Ensemble U) :=
    (forall (x : U) (y : U), In U X x -> In U X y -> R x y -> x = y).

  Lemma chain_mono: forall (C : Ensemble U) (C' : Ensemble U),
    chain C -> Included _ C' C -> chain C'.
  Proof.
    unfold chain; intuition.
  Qed.

  Lemma anti_chain_mono: forall (C : Ensemble U) (C' : Ensemble U),
    anti_chain C -> Included _ C' C -> anti_chain C'.
  Proof.
    unfold anti_chain; intuition.
  Qed.

  Lemma chain_Empty_set: chain (Empty_set U).
  Proof.
    unfold chain; intros; destruct H.
  Qed.

  Lemma anti_chain_Empty_set: anti_chain (Empty_set U).
  Proof.
    unfold anti_chain; intros; destruct H.
  Qed.

  Lemma chain_Singleton: forall (x : U), chain (Singleton _ x).
  Proof.
    unfold chain.
    intros x y z x_y x_z.
    destruct x_y; destruct x_z.
    destruct Ord as [r _ _]; unfold Reflexive in r.
    intuition.
  Qed.

  Lemma anti_chain_Singleton: forall (x : U), anti_chain (Singleton _ x).
  Proof.
    unfold anti_chain.
    intros x y z x_y x_z.
    destruct x_y; destruct x_z.
    auto.
  Qed.

End Chains.
