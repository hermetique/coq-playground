(*

playing with Dilworth's theorem,

https://en.wikipedia.org/wiki/Dilworth's_theorem

This is highly experimental...
it's somewhat unclear how to best formulate the Theorem.

*)

(* Require Import List. *)

(* Require Import Orders. *)

(* Require Import Coq.Logic.FinFun. *)

Load Big_union.

Require Import Relations_1.

Require Import Ensembles.

Require Import Finite_sets.

Require Import Finite_sets_facts.

Require Import Coq.Logic.ClassicalChoice.

Module Type Dilworth.

  Parameter U : Type.
  Parameter S : Ensemble U.
  Parameter R : Relation U.
  Axiom Ord : Order U R.

  Definition chain (X : Ensemble U) :=
    (forall (x : U) (y : U), In U X x -> In U X y -> R x y \/ R y x).

  Definition anti_chain (X : Ensemble U) :=
    (forall (x : U) (y : U), In U X x -> In U X y -> R x y -> x = y).

  Theorem dilworth_easy: forall (Cs : Ensemble (Ensemble U)) (A : Ensemble U),
    Included U A (Big_union U Cs) ->
    (forall (C : Ensemble U), In _ Cs C -> chain C) ->
    anti_chain A ->
    (exists f : U -> Ensemble U,
      (forall x : U, In _ A x -> In _ Cs (f x)) /\
      (forall x y : U, In _ A x -> In _ A y -> f x = f y -> x = y)).
  Proof.
    intros Cs A Incl chn achn.
    assert (forall x : U, exists C : Ensemble U, In _ A x -> In _ Cs C /\ In _ C x).
    * intros x.
      pose (T := classic (In _ A x)).
      destruct T as [A_x | not_A_x].
      - unfold Included in Incl.
        pose (Cs_x := Incl x A_x).
        destruct Cs_x as [C Cs_C x C_x].
        apply (ex_intro _ C); auto.

      - apply (ex_intro _ (fun _ => False)).
        intro A_x.
        case (not_A_x A_x).

    * destruct (choice _ H) as [g g_prop].
      apply (ex_intro _ g).
      split.
      - intros x A_x.
        pose (g_x := g_prop x A_x).
        destruct g_x as [goal _]; auto.

      - intros x y A_x A_y g_x_eq_g_y.
        pose (g_x := g_prop x A_x).
        pose (g_y := g_prop y A_y).
        rewrite g_x_eq_g_y in g_x.
        destruct g_x as [Cs_g_y g_y_x].
        destruct g_y as [_ g_y_y].
        unfold anti_chain in achn.
        unfold chain in chn.
        pose (Rxyx := chn (g y) Cs_g_y x y g_y_x g_y_y).
        destruct Rxyx as [Rxy | Ryx].
        + exact (achn x y A_x A_y Rxy).
        + exact (eq_sym (achn y x A_y A_x Ryx)).
  Qed.

  Lemma case_finite_set:
    forall (S : Ensemble U),
    Finite _ S -> S = Empty_set _ \/ exists (x : U), In _ S x.
  Proof.
    intros S Fin.
    case Fin.
    - auto.
    - intros.
      apply or_intror.
      apply (ex_intro _ x).
      apply Add_intro2.
  Qed.

  Lemma case_classic_set:
    forall (S : Ensemble U),
    S = Empty_set _ \/ exists (x : U), In _ S x.
  Proof.
    intros S.
    classical_left.
    apply Extensionality_Ensembles.
    split; unfold Included; intros x mem.
    - destruct H; apply (ex_intro _ x mem).
    - destruct mem.
  Qed.

  Lemma pick_min_element:
    forall (S : Ensemble U), Finite U S ->
    forall (x : U), In _ S x ->
    (exists x : U, In _ S x /\ (forall y : U, In _ S y -> R y x -> x = y)).
  Proof.
    intros S Fin.
    induction Fin as [| S Fin IH x' new].
    - intros; destruct H.
    - intros x Sx'_x.
      pose (H := case_finite_set S Fin); destruct H as [empty | elem].
      + apply (ex_intro _ x').
        rewrite empty.
        split.
        * apply Add_intro2.
        * intros; destruct H; destruct H; auto.
      + destruct elem as [x'' elem].
        pose (IH' := IH x'' elem).
        destruct IH' as [z IHz].
        clear x'' elem IH.
        destruct IHz as [S_z max_z].
        pose (H := classic (R x' z)); destruct H as [Rx'z | not_Rx'z].
        * apply (ex_intro _ x').
          split.
          -- apply Add_intro2.
          -- intros y Sx'_y Ryx'.
             destruct Sx'_y as [y S_y| y y_x'].
             ++ pose (Ord := Ord).
                destruct Ord as [Refl Trans Anti].
                unfold Transitive in Trans.
                destruct (max_z y S_y (Trans _ _ _ Ryx' Rx'z)).
                unfold Antisymmetric in Anti.
                exact (Anti _ _ Rx'z Ryx').
             ++ destruct y_x'; auto.
        * apply (ex_intro _ z).
          split.
          -- apply Add_intro1; auto.
          -- intros y Sx'_y Ryz.
             destruct Sx'_y as [y S_y| y y_x'].
             ++ exact (max_z y S_y Ryz).
             ++ destruct y_x'.
                exfalso.
                exact (not_Rx'z Ryz).
  Qed.

  Lemma split_min_element:
    forall (S : Ensemble U), Finite U S ->
    S = Empty_set _ \/
    (exists (x : U) (S' : Ensemble U), S = Add _ S' x /\ ~ In _ S' x /\  (forall y : U, In _ S' y -> ~ R y x)).
  Proof.
    intros S Fin.
    destruct (case_finite_set _ Fin) as [empty | mem].
    - apply or_introl; auto.
    - apply or_intror.
      destruct mem as [x S_x].
      destruct (pick_min_element S Fin x S_x) as [m T].
      clear x S_x.
      destruct T as [S_m m_min].
      apply (ex_intro _ m).
      apply (ex_intro _ (Subtract _ S m)).
      repeat split.
      + apply Extensionality_Ensembles.
        split; unfold Included; intros x mem.
        * destruct (classic (m = x)).
          -- destruct H.
             apply Add_intro2.
          -- apply Add_intro1.
             unfold Subtract.
             apply Setminus_intro.
             ++ exact mem.
             ++ intro m_x.
                destruct m_x.
                exact (H eq_refl).
        * destruct (classic (m = x)).
          -- destruct H.
             assumption.
          -- destruct mem as [x add1 | x add2].
             ++ destruct add1 as [S_x _]; assumption.
             ++ destruct add2; assumption.
     + intro.
       destruct H as [_ H].
       apply H.
       split.
     + intros.
       destruct H as [S_y].
       intro Rym.
       destruct H.
       apply Singleton_intro.
       exact (m_min _ S_y Rym).
  Qed.

  Lemma strict_included_add:
    forall (A : Ensemble U) (x : U),
    ~ In _ A x -> Strict_Included _ A (Add _ A x).
  Proof.
    intros A x not_A_x.
    split.
    - unfold Included.
      intros.
      apply Add_intro1.
      assumption.
    - intro.
      rewrite H in not_A_x.
      apply not_A_x.
      apply Add_intro2.
  Qed.

  Theorem dilworth_hard :
    Finite U S -> inhabited U ->
    (exists (Cs : Ensemble (Ensemble U)) (A : Ensemble U) (f : Ensemble U -> U),
      (S = Big_union U Cs) /\
      (forall (C : Ensemble U), In _ Cs C -> chain C) /\
      anti_chain A /\
      (forall X : Ensemble U, In _ Cs X -> In _ A (f X)) /\
      (forall X Y : Ensemble U, In _ Cs X -> In _ Cs Y -> f X = f Y -> X = Y)).
  Proof.
    intros Fin inh.
    destruct inh as [U_wit].
    induction Fin as [S Fin IH] using Generalized_induction_on_finite_sets.
    destruct (split_min_element _ Fin) as [empty | mem].
    - (* the empty set is decomposed into an empty set of chains and an empty antichain *)
      apply (ex_intro _ (Empty_set _)).
      apply (ex_intro _ (Empty_set _)).
      apply (ex_intro _ (fun _ => U_wit)).
      repeat split.
      + rewrite Big_union_Empty_set; auto.
      + intros; destruct H.
      + unfold anti_chain; intros; destruct H.
      + intros; destruct H.
      + intros; destruct H.
    - (* we have picked a minimum element x in S... apply the induction hypothesis to S - {x}. *)
      destruct mem as [x mem].
      destruct mem as [S' mem].
      destruct mem as [S_eq mem].
      destruct mem as [not_S'_x x_min]. (* these repeated "destruct"s look stupid. *)
      rewrite S_eq in IH.
      destruct (IH S' (strict_included_add S' x not_S'_x)) as [Cs0 IH'].
      destruct IH' as [A0 IH'].
      destruct IH' as [f0 IH'].
      destruct IH' as [U_Cs0 IH'].
      destruct IH' as [chain_Cs0 IH'].
      destruct IH' as [achain_A0 IH'].
      destruct IH' as [f0_ran f0_injective].

      (* And here, the fun begins for real. From the antichain A0 we want to construct a new
         antichain A1 where each element a in A0 is replaced by the maximum element in the chain
         in Cs0 corresponding to a (given by the inverse of f0) that allows an antichain of the
         same cardinality as A0 to be constructed. *)
  Abort All.

End Dilworth.
