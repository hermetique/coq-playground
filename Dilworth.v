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

Require Import Image.

Lemma included_add:
  forall (U : Type) (A : Ensemble U) (x : U),
  Included _ A (Add _ A x).
Proof.
  intuition.
Qed.

Lemma strict_included_add:
  forall (U : Type) (A : Ensemble U) (x : U),
  ~ In _ A x -> Strict_Included _ A (Add _ A x).
Proof.
  intros U A x not_A_x.
  split.
  - intuition.
  - intro.
    rewrite H in not_A_x.
    auto with sets.
Qed.

Lemma included_subtract:
  forall (U : Type) (A : Ensemble U) (x : U),
  Included _ (Subtract _ A x) A.
Proof.
  unfold Included.
  intros U A x z A_z.
  destruct A_z.
  assumption.
Qed.

Lemma add_subtract_eq:
  forall (U : Type) (A : Ensemble U) (x : U),
  In _ A x -> A = Add _ (Subtract _ A x) x.
Proof.
  intuition.
Qed.

Lemma in_add_iff:
  forall (U : Type) (A : Ensemble U) (x y : U),
  In _ (Add _ A x) y <-> x = y \/ In _ A y.
Proof.
  intros. split; intros.
  - destruct H; intuition.
  - destruct H; try (rewrite H); intuition.
Qed.

Module Type Dilworth.

  Parameter U : Type.
  Parameter S : Ensemble U.
  Parameter R : Relation U.
  Axiom Ord : Order U R.

  Definition chain (X : Ensemble U) :=
    (forall (x : U) (y : U), In U X x -> In U X y -> R x y \/ R y x).

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

  Theorem dilworth_easy: forall (Cs : Ensemble (Ensemble U)) (A : Ensemble U),
    Included U A (Big_union U Cs) ->
    (forall (C : Ensemble U), In _ Cs C -> chain C) ->
    anti_chain A ->
    (exists f : U -> Ensemble U,
      (forall x : U, In _ A x -> In _ (f x) x) /\
      (forall x : U, In _ A x -> In _ Cs (f x)) /\
      (forall x y : U, In _ A x -> In _ A y -> f x = f y -> x = y)).
  Proof.
    intros Cs A Incl chn achn.
    assert (forall x : U, exists C : Ensemble U, In _ A x -> In _ Cs C /\ In _ C x).
    {
      intros x.
      destruct (classic (In _ A x)) as [A_x | not_A_x].
      + unfold Included in Incl.
        destruct (Incl x A_x) as [C Cs_C x C_x].
        apply (ex_intro _ C); auto.

      + apply (ex_intro _ (fun _ => False)).
        intro A_x.
        case (not_A_x A_x).
    }
    destruct (choice _ H) as [g g_prop].
    apply (ex_intro _ g).
    repeat split.
    - intros x A_x.
      destruct (g_prop x A_x); auto.

    - intros x A_x.
      destruct (g_prop x A_x) as [goal _]; auto.

    - intros x y A_x A_y g_x_eq_g_y.
      pose (g_x := g_prop x A_x).
      pose (g_y := g_prop y A_y).
      rewrite g_x_eq_g_y in g_x.
      destruct g_x as [Cs_g_y g_y_x].
      destruct g_y as [_ g_y_y].
      unfold anti_chain in achn.
      unfold chain in chn.
      destruct (chn (g y) Cs_g_y x y g_y_x g_y_y) as [Rxy | Ryx].
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
      destruct (case_finite_set S Fin) as [empty | elem].
      + apply (ex_intro _ x').
        rewrite empty.
        split.
        * apply Add_intro2.
        * intros; destruct H; destruct H; auto.
      + destruct elem as [x'' elem].
        destruct (IH x'' elem) as (z & S_x & max_z).
        clear x'' elem IH.
        destruct (classic (R x' z)) as [Rx'z | not_Rx'z].
        * apply (ex_intro _ x').
          split.
          -- apply Add_intro2.
          -- intros y Sx'_y Ryx'.
             destruct Sx'_y as [y S_y| y y_x'].
             ++ destruct Ord as [Refl Trans Anti].
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
                destruct (not_Rx'z Ryz).
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

  Lemma split_min_element_chain:
    forall (C : Ensemble U), Finite U C ->
    chain C ->
    C = Empty_set _ \/
    (exists (x : U) (C' : Ensemble U), C = Add _ C' x /\ ~ In _ C' x /\ chain C' /\
      (forall y : U, In _ C' y -> ~ R y x /\ R x y)).
  Proof.
    intros C Fin chn.
    destruct (split_min_element C Fin) as [empty | min].
    - auto.
    - destruct min as (x & C' & C_eq & x_new & min).
      refine (or_intror (ex_intro _ x (ex_intro _ C' _))); repeat split.
      + auto.
      + auto.
      + apply (chain_mono C).
        * auto.
        * rewrite C_eq; intuition.
      + auto.
      + unfold chain in chn.
        assert (C_x : In U C x). { rewrite C_eq; intuition. }
        assert (C_y : In U C y). { rewrite C_eq; intuition. }
        destruct (chn x y C_x C_y).
        * auto.
        * exfalso; apply (min y); auto.
  Qed.

  Theorem dilworth_hard :
    Finite U S -> inhabited U ->
    (exists (Cs : Ensemble (Ensemble U)) (A : Ensemble U) (f : Ensemble U -> U),
      (S = Big_union U Cs) /\
      (forall (C : Ensemble U), In _ Cs C -> chain C) /\
      Finite _ A /\
      Included _ A (Big_union _ Cs) /\
      anti_chain A /\
      (forall X : Ensemble U, In _ Cs X -> In _ A (f X)) /\
      (forall X : Ensemble U, In _ Cs X -> In _ X (f X)) /\
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
      + apply Empty_is_finite.
      + intuition.
      + unfold anti_chain; intros; destruct H.
      + intros; destruct H.
      + intros; destruct H.
      + intros; destruct H.
    - (* we have picked a minimum element s in S... apply the induction hypothesis to S - {s}. *)
      destruct mem as (s & S' & S_eq & not_S'_s & s_min).
      pose (T := IH).
      rewrite S_eq in T.
      destruct (T S' (strict_included_add _ S' s not_S'_s)) as
        (Cs0 & A0 & f0 & U_Cs0 & chain_Cs0 & fin_A0 & sup_A0 & achain_A0 & f0_ran & f0_chn & f0_inj).
      clear T.

      (* Using the antichain A0 and the sets of chains Cs0, we construct an antichain A1 such that
         each element x in A0 is replaced by the maximum element in the chain in Cs0 corresponding
         to x (that chain is given by the inverse of f0) that is a member of an antichain that
         contains an element from each element of Cs0 (these antichains are characterized by the
         anti_chain0 definition). *)
      pose (anti_chain0 (A : Ensemble U) :=
        anti_chain A /\
        (forall C, In _ Cs0 C -> exists x, In _ A x /\ In _ C x) /\
        (forall (x : U), In _ A x -> exists (C : Ensemble U), In _ Cs0 C /\ In _ C x)).
      assert (ac0_A0 : anti_chain0 A0).
      {
        destruct (dilworth_easy Cs0 A0 sup_A0 chain_Cs0 achain_A0) as (g0 & g0_A0 & g0_ran & g0_inj).
        assert (g_inv : forall (x : U), In _ A0 x -> f0 (g0 x) = x).
        {
          clear IH s S_eq not_S'_s s_min anti_chain0.
          intros x A0_x.
          (* destruct (sup_A0 _ A0_x) as [C Cs0_C x C_x]. *)
          assert (A0_fg0x : In _ A0 (f0 (g0 x))). { intuition. }
          assert (g0x_x : In _ (g0 x) x). { intuition. }
          assert (g0x_fg0x : In _ (g0 x) (f0 (g0 x))). { intuition. }
          assert (Cs0_g0x : In _ Cs0 (g0 x)). { intuition. }
          assert (R x (f0 (g0 x)) \/ R (f0 (g0 x)) x).
          {
            apply (chain_Cs0 _ Cs0_g0x); intuition.
          }
          destruct H.
          - apply eq_sym; intuition.
          - intuition.
        }
        unfold anti_chain0.
        clear IH s S_eq not_S'_s s_min anti_chain0.
        repeat split.
        - assumption.
        - intros C Cs0_C.
          apply (ex_intro _ (f0 C)).
          intuition.
        - intros.
          apply (ex_intro _ (g0 x)); split.
          + intuition.
          + pose (goal := f0_ran (g0 x) (g0_ran x H)).
            rewrite g_inv in goal; auto.
      }
      assert (forall (C : Ensemble U), exists (x : U), In _ Cs0 C ->
        In _ C x /\
        (exists (A : Ensemble U), anti_chain0 A /\ In _ A x) /\
        (forall (A : Ensemble U) (z : U), anti_chain0 A -> In _ A z -> R z x -> z = x)).
      {
        assert (fin_S' : Finite _ S').
        {
          apply (Finite_downward_closed _ S).
          - assumption.
          - rewrite S_eq; intuition.
        }
        clear IH s S_eq not_S'_s s_min.
        intros.
        destruct (classic (In (Ensemble U) Cs0 C)) as [Cs0_C | not_Cs0_C].
        + intros.
          pose (D (x : U) := In _ C x /\ exists A, anti_chain0 A /\ In _ A x).
          assert (D_sub_C : Included _ D C).
          {
            unfold Included.
            unfold In.
            unfold D.
            intuition.
          }
          assert (D_chain : chain D). { apply (chain_mono C); intuition. }
          assert (D_fin : Finite _ D).
          {
            apply (Finite_downward_closed _ C).
            apply (Finite_downward_closed _ S').
            - assumption.
            - rewrite U_Cs0.
              intros z C_z.
              apply (in_in _ Cs0 _ Cs0_C _ C_z).
            - assumption.
          }
          destruct (split_min_element_chain D D_fin D_chain) as
            [empty | (x & D' & D_eq & new & D'_chain & x_min)].
          - assert (In _ D (f0 C)).
            {
              unfold D.
              split.
              * intuition.
              * apply (ex_intro _ A0); intuition.
            }
            rewrite empty in H.
            destruct H.
          - apply (ex_intro _ x).
            repeat split.
            * rewrite D_eq in D_sub_C.
              intuition.
            * assert (D_x : In _ D x). { rewrite D_eq; intuition. }
              unfold In in D_x; unfold D in D_x.
              intuition.
            * intros A z ac0_A A_z R_z_x.
              destruct (id ac0_A) as (ac_A & to_A & _).
              destruct (to_A _ Cs0_C) as (x' & A_x' & C_x').
              assert (D_x' : In _ D x').
              {
                unfold In; unfold D.
                split.
                - assumption.
                - apply (ex_intro _ A); intuition.
              }
              assert (R_z_x' : R z x').
              {
                pose Ord; destruct Ord; unfold Transitive in t; unfold Reflexive in r.
                apply (t _ _ _ R_z_x).
                rewrite D_eq in D_x'.
                destruct D_x' as [x' D'_x' | x' x_x'].
                - pose (x_min x'); intuition.
                - destruct x_x'; intuition.
              }
              destruct (ac_A _ _ A_z A_x' R_z_x').
              rewrite D_eq in D_x'.
              destruct D_x' as [z D'_x0 | z x_z].
              -- pose (x_min _ D'_x0); intuition.
              -- destruct x_z; auto.
        + apply (ex_intro _ U_wit); intuition.
      }
      destruct (choice _ H) as [f1 f1_prop]; clear H.
      pose (A1 := Im _ _ Cs0 f1).
      assert (ac0_A1 : anti_chain0 A1).
      {
        unfold A1; unfold anti_chain0.
        repeat split.
        - clear IH s S_eq not_S'_s s_min S Fin S' U_Cs0.
          unfold anti_chain.
          intros x y A_x A_y R_x_y.
          destruct A_x as [Cx Cs0_Cx x x_def]; rewrite x_def in *; clear x x_def.
          destruct A_y as [Cy Cs0_Cy y y_def]; rewrite y_def in *; clear y y_def.
          destruct (f1_prop _ Cs0_Cx) as (_ & (Ax & ac0_Ax & Ax_f1Cx) & _).
          destruct (f1_prop _ Cs0_Cy) as (_ & _ & Ay_prop).
          apply (Ay_prop Ax); auto.
        - intros C Cs0_C.
          apply (ex_intro _ (f1 C)).
          split.
          + intuition.
          + pose (f1_prop C); intuition.
        - intros y f1Cs0_y.
          destruct f1Cs0_y as [C Cs0_C y y_eq].
          pose (f1_prop C).
          rewrite y_eq.
          apply (ex_intro _ C); intuition.
      }
  clear A0 f0 fin_A0 sup_A0 achain_A0 f0_ran f0_chn f0_inj ac0_A0.
  (* Now we have a maximum size antichain A1 for S' / Cs0, such that each of the
     elements of A is maximal. We need to decide what to do with s. *)
  Abort All.

End Dilworth.
