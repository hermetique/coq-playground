Require Import Coq.Sets.Powerset_facts.
Require Import Coq.Sets.Constructive_sets.
Require Import Ensembles.

(* Compute union of an ensemble of ensembles. *)

Inductive Big_union {U} (Xs : Ensemble (Ensemble U)) : Ensemble U :=
  Big_union_def : forall X, In _ Xs X -> forall x, In _ X x -> In _ (Big_union Xs) x.

(* Prove the analogue of `Union_is_Lub` for Big_union *)

Theorem Big_union_is_Lub:
  forall {U} (A : Ensemble U) (Xs : Ensemble (Ensemble U)),
  (forall X, In _ Xs X -> Included U X A) ->
  Lub (Ensemble U) (Power_set_PO U A) Xs (Big_union Xs).
Proof.
  intros U A Xs Incl.
  split. split. split.
  - unfold Included.
    intros x in_Big_union.
    destruct in_Big_union as [X Xs_X x X_x].
    unfold Included in Incl.
    exact (Incl X Xs_X x X_x).

  - simpl.
    unfold Included.
    intros X Xs_X x X_x.
    exact (Big_union_def Xs X Xs_X x X_x).

  - simpl.
    unfold Included.
    intros X ub x in_bu.
    destruct ub as [_ bound].
    simpl in bound.
    unfold Included in bound.
    destruct in_bu as [X' Xs_X' x X'_x].
    exact (bound X' Xs_X' x X'_x).
Qed.

Theorem Big_union_Empty_set:
  forall U, Big_union (Empty_set _) = Empty_set U.
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; unfold Included; intros x H.
  - destruct H as [_ [] _ _].
  - destruct H.
Qed.

Theorem Big_union_Singleton:
  forall U (X : Ensemble U), Big_union (Singleton _ X) = X.
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; unfold Included; intros x H.
  - destruct H as [_ [] x X_c].
    assumption.
  - refine (Big_union_def (Singleton _ X) X _ x H).
    split.
Qed.

Theorem Big_union_Union:
  forall U (Xs Ys : Ensemble (Ensemble U)),
  Big_union (Union _ Xs Ys) = Union _ (Big_union Xs) (Big_union Ys).
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; unfold Included; intros x H.
  - destruct H as [X [X' Xs_X'| Y' Ys_Y'] y X_y].
    + apply Union_introl; apply (Big_union_def Xs X' Xs_X' y X_y).
    + apply Union_intror; apply (Big_union_def Ys Y' Ys_Y' y X_y).
  - destruct H as [x [X Xs_X y X_y] | x [Y Ys_Y y Y_y]].
    + apply (Big_union_def _ X); intuition.
    + apply (Big_union_def _ Y); intuition.
Qed.

Theorem Big_union_Couple:
  forall U (X : Ensemble U) (Y : Ensemble U), Big_union (Couple _ X Y) = Union _ X Y.
Proof.
  intros; rewrite <- Couple_as_union.
  rewrite Big_union_Union; repeat rewrite Big_union_Singleton; auto.
Qed.

Theorem Big_union_Add:
  forall U (Xs : Ensemble (Ensemble U)) (Y : Ensemble U),
  Big_union (Add _ Xs Y) = Union _ (Big_union Xs) Y.
Proof.
  intros; unfold Add.
  rewrite (Big_union_Union); rewrite (Big_union_Singleton); auto.
Qed.

Theorem Big_union_mono:
  forall {U} (Xs Ys : Ensemble (Ensemble U)),
  Included _ Xs Ys -> Included _ (Big_union Xs) (Big_union Ys).
Proof.
  intros U Xs Ys Xs_Ys x Xs_x.
  destruct Xs_x as [X Xs_X x X_x].
  apply (Big_union_def _ X); intuition.
Qed.

Hint Resolve Big_union_def.
Hint Extern 1 => rewrite Big_union_Empty_set.
Hint Extern 1 => rewrite Big_union_Singleton.
Hint Extern 1 => rewrite Big_union_Couple.
Hint Extern 1 => rewrite Big_union_Union.
Hint Extern 1 => rewrite Big_union_Add.
