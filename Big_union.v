Require Import Coq.Sets.Powerset.
Require Import Ensembles.

(* Compute union of an ensemble of ensembles. *)

Inductive Big_union (U : Type) (Xs : Ensemble (Ensemble U)) : Ensemble U :=
  in_in : forall X, In _ Xs X -> forall x, In _ X x -> In _ (Big_union U Xs) x.

(* Prove the analogue of `Union_is_Lub` for Big_union *)

Theorem Big_union_is_Lub:
  forall (U : Type) (A : Ensemble U) (Xs : Ensemble (Ensemble U)),
  (forall X, In _ Xs X -> Included U X A) ->
  Lub (Ensemble U) (Power_set_PO U A) Xs (Big_union U Xs).
Proof.
  intros U A Xs Incl.
  split. split. split.
  * unfold Included.
    intros x in_Big_union.
    destruct in_Big_union as [X Xs_X x X_x].
    unfold Included in Incl.
    exact (Incl X Xs_X x X_x).

  * simpl.
    unfold Included.
    intros X Xs_X x X_x.
    exact (in_in U Xs X Xs_X x X_x).

  * simpl.
    unfold Included.
    intros X ub x in_bu.
    destruct ub as [_ bound].
    simpl in bound.
    unfold Included in bound.
    destruct in_bu as [X' Xs_X' x X'_x].
    exact (bound X' Xs_X' x X'_x).
Qed.

Theorem Big_union_Empty_set:
  forall U : Type, Big_union _ (Empty_set _) = Empty_set U.
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; unfold Included; intros x H.
  - destruct H.
    destruct H.
  - destruct H.
Qed.

Theorem Big_union_Singleton:
  forall (U : Type) (X : Ensemble U), Big_union _ (Singleton _ X) = X.
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; unfold Included; intros x H.
  - destruct H.
    destruct H.
    exact H0.
  - refine (in_in U (Singleton _ X) X _ x H).
    split.
Qed.

Theorem Big_union_Couple:
  forall (U : Type) (X : Ensemble U) (Y : Ensemble U), Big_union _ (Couple _ X Y) = Union _ X Y.
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; unfold Included; intros x H.
  - destruct H.
    destruct H.
    + apply Union_introl; auto.
    + apply Union_intror; auto.
  - destruct H.
    + refine (in_in U (Couple _ X Y) X _ x H).
      apply Couple_l.
    + refine (in_in U (Couple _ X Y) Y _ x H).
      apply Couple_r.
Qed.
