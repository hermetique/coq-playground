(* Require Import List. *)

(* Require Import Orders. *)

(* Require Import Coq.Logic.FinFun. *)

Load Big_union.

Require Import Relations_1.

Require Import Ensembles.

Require Import Finite_sets.

Require Import Coq.Logic.ClassicalChoice.

Section Dilworth.

  Variable U : Type.
  Variable S : Ensemble U.
  Variable R : Relation U.

  Definition chain (X : Ensemble U) :=
    (forall (x : U) (y : U), In U X x -> In U X y -> R x y \/ R y x).

  Definition anti_chain (X : Ensemble U) :=
    (forall (x : U) (y : U), In U X x -> In U X y -> R x y -> x = y).

  Theorem dilworth_easy: forall (Cs : Ensemble (Ensemble U)) (A : Ensemble U),
    Order U R ->
    Included U A (Big_union U Cs) ->
    (forall (C : Ensemble U), In _ Cs C -> chain C) ->
    anti_chain A ->
    (exists f : U -> Ensemble U,
      (forall x : U, In _ A x -> In _ Cs (f x)) /\
      (forall x y : U, In _ A x -> In _ A y -> f x = f y -> x = y)).
  Proof.
    intros Cs A Ord Incl chn achn.
    assert (forall x : U, exists C : Ensemble U, In _ A x -> In _ Cs C /\ In _ C x).
      intros x.
      pose (T := classic (In _ A x)).
      destruct T as [A_x | not_A_x].
        unfold Included in Incl.
        pose (Cs_x := Incl x A_x).
        destruct Cs_x as [C Cs_C C_x].
        refine (ex_intro _ C _).
        split.
          exact Cs_C.
          exact C_x.

        refine (ex_intro _ (fun _ => False) _).
        intro A_x.
        case (not_A_x A_x).

    destruct (choice _ H) as [g g_prop].
    refine (ex_intro _ g _).
    split.
      intros x A_x.
      pose (g_x := g_prop x A_x).
      destruct g_x as [goal _].
      exact goal.

      intros x y A_x A_y g_x_eq_g_y.
      pose (g_x := g_prop x A_x).
      pose (g_y := g_prop y A_y).
      rewrite g_x_eq_g_y in g_x.
      destruct g_x as [Cs_g_y g_y_x].
      destruct g_y as [_ g_y_y].
      unfold anti_chain in achn.
      unfold chain in chn.
      pose (Rxyx := chn (g y) Cs_g_y x y g_y_x g_y_y).
      destruct Rxyx as [Rxy | Ryx].
        exact (achn x y A_x A_y Rxy).
        exact (eq_sym (achn y x A_y A_x Ryx)).
  Qed.

  Theorem dilworth_hard :
    Order U R -> Finite U S ->
    (exists (Cs : Ensemble (Ensemble U)) (A : Ensemble U) (f : Ensemble U -> U),
      (forall (C : Ensemble U), In _ Cs C -> chain C) /\
      anti_chain A /\
      (forall X : Ensemble U, In _ Cs X -> In _ A (f X)) /\
      (forall X Y : Ensemble U, In _ Cs X -> In _ Cs Y -> f X = f Y -> X = Y)).
  Proof.
    admit.
  Admitted.

End Dilworth.
