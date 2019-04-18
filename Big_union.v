Require Import Coq.Sets.Powerset.

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
