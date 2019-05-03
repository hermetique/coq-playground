(*

playing with Dilworth's theorem,

https://en.wikipedia.org/wiki/Dilworth's_theorem

The proof is complete, but still somewhat experimental...
It would perhaps be better to state the theorem in terms of cardinalities rather than injections.
*)

(* Require Import List. *)

(* Require Import Orders. *)

(* Require Import Coq.Logic.FinFun. *)

Load Big_union.
Load Chains.
Require Import Relations_1.
Require Import Ensembles.
Require Import Finite_sets.
Require Import Finite_sets_facts.
Require Import Coq.Logic.ClassicalChoice.
Require Import Image.
Require Import Coq.Sets.Finite_sets.
Require Import Omega.

(* Hmm, need to do some more digging into foundations... we are using classical logic
   so we should be able to define a function corresponding to In _ _ _. *)
Lemma mem_ex:
  forall {U} (A : Ensemble U),
  exists mem, forall (x : U),
    (In U A x -> mem x = true) /\
    (~ In U A x -> mem x = false).
Proof.
  intros.
  assert (forall (x : U), exists b, (In U A x -> b = true) /\ (~ In U A x -> b = false)).
  {
    intros.
    destruct (classic (In U A x)).
    - apply (ex_intro _ true); intuition.
    - apply (ex_intro _ false); intuition.
  }
  destruct (choice _ H) as (mem & mem_prop).
  apply (ex_intro _ mem).
  assumption.
Qed.

Lemma included_add:
  forall {U} (A : Ensemble U) (x : U),
  Included _ A (Add _ A x).
Proof.
  intuition.
Qed.

Lemma strict_included_add:
  forall {U} (A : Ensemble U) (x : U),
  ~ In _ A x -> Strict_Included _ A (Add _ A x).
Proof.
  intros U A x not_A_x.
  split.
  - intuition.
  - intro.
    rewrite H in not_A_x.
    auto with sets.
Qed.

Lemma included_setminus:
  forall {U} (A B : Ensemble U),
  Included _ (Setminus _ A B) A.
Proof.
  unfold Included.
  intros U A B x H.
  destruct H; assumption.
Qed.

Lemma included_subtract:
  forall {U} (A : Ensemble U) (x : U),
  Included _ (Subtract _ A x) A.
Proof.
  unfold Included.
  intros U A x z A_z.
  destruct A_z.
  assumption.
Qed.

Lemma add_subtract_eq:
  forall {U} (A : Ensemble U) (x : U),
  In _ A x -> A = Add _ (Subtract _ A x) x.
Proof.
  intuition.
Qed.

Lemma in_add_iff:
  forall {U} (A : Ensemble U) (x y : U),
  In _ (Add _ A x) y <-> x = y \/ In _ A y.
Proof.
  intros. split; intros.
  - destruct H; intuition.
  - destruct H; try (rewrite H); intuition.
Qed.

Lemma in_intersection_iff:
  forall {U} (A B : Ensemble U) x,
  In _ (Intersection _ A B) x <-> In _ A x /\ In _ B x.
Proof.
  intros; split; intros; destruct H; intuition.
Qed.

Lemma subst:
  forall {U V} (f : U -> V) x y, x = y -> f x = f y.
Proof.
  intros; rewrite H; auto.
Qed.

Definition injective_on {U V} (X : Ensemble U) (f : U -> V) :=
  forall x y, In _ X x -> In _ X y -> f x = f y -> x = y.

Lemma injective_to_injective_in:
  forall {U V} X (f : U -> V), injective _ _ f -> injective_on X f.
Proof.
  unfold injective; unfold injective_on; auto.
Qed.

Lemma injective_on_mono:
  forall {U V} X Y (f : U -> V), Included _ X Y -> injective_on Y f -> injective_on X f.
Proof.
  unfold injective_on; auto.
Qed.

(* Lemma adapted from Sets.Image.injective_preserves_cardinal - Note LGPL 2.1 license! *)
Lemma injective_on_preserves_cardinal:
  forall {U V} (X : Ensemble U) (f : U -> V) (n : nat),
  injective_on X f -> cardinal U X n -> forall n' : nat, cardinal V (Im U V X f) n' -> n' = n.
Proof.
  induction 2 as [| A n H'0 H'1 x H'2]; auto with sets.
  rewrite (image_empty _ _ f).
  intros n' CE.
  apply cardinal_unicity with V (Empty_set V); auto with sets.
  intro n'.
  rewrite (Im_add _ _ A x f).
  intro H'3.
  elim cardinal_Im_intro with _ _ A f n; trivial with sets.
  intros i CI.
  assert (H' : injective_on A f).
  { apply (injective_on_mono _ (Add _ A x)); auto with sets. }
  lapply (H'1 H' i); trivial with sets.
  cut (~ In _ (Im _ _ A f) (f x)).
  intros H0 H1.
  apply cardinal_unicity with V (Add _ (Im _ _ A f) (f x)); trivial with sets.
  apply card_add; auto with sets.
  rewrite <- H1; trivial with sets.
  red; intro; apply H'2.
  destruct (Im_inv _ _ _ _ _ H0) as (z & A_z & fz_fx).
  rewrite (H x z); auto with sets.
Qed.

Lemma injective_on_preserves_cardinal2:
  forall {U V} (X : Ensemble U) (f : U -> V) (n : nat),
  injective_on X f -> cardinal _ X n -> cardinal _ (Im _ _ X f) n.
Proof.
  intros U V X f n inj X_n.
  destruct (cardinal_Im_intro _ _ X f n X_n) as [n'].
  rewrite (injective_on_preserves_cardinal X f n inj X_n n' H) in H; assumption.
Qed.

Lemma injective_on_inverse:
  forall {U} (i : inhabited U) {V} (X : Ensemble U) (f : U -> V),
  injective_on X f -> exists g, forall x, In _ X x -> g (f x) = x.
Proof.
  intros U i V X f inj.
  assert (forall y, exists x, forall z, In _ X z -> f z = y -> z = x).
  {
    intros.
    destruct (classic (exists x, In U X x /\ f x = y)).
    - destruct H as (x & X_x & fx_y).
      apply (ex_intro _ x).
      intros z X_z fz_y.
      apply inj; try assumption.
      rewrite fx_y; rewrite fz_y; auto.
    - destruct i as [u]; apply (ex_intro _ u).
      intros z X_z fz_y.
      destruct H.
      apply (ex_intro _ z); auto.
  }
  destruct (choice _ H) as [g g_prop].
  apply (ex_intro _ g).
  intros x X_x.
  rewrite <- (g_prop (f x) x); auto.
Qed.

Lemma image_compose:
  forall {U V W} (X : Ensemble U) (f : U -> V) (g : V -> W),
  Im _ _ (Im _ _ X f) g = Im _ _ X (fun x => g (f x)).
Proof.
  intros.
  apply Extensionality_Ensembles; unfold Same_set; split; intros x H.
  - destruct H as [_ [x X_x u u_eq] t t_eq]; rewrite u_eq in *; rewrite t_eq in *; clear t t_eq u u_eq.
    apply (Im_intro _ _ _ _ x); auto.
  - destruct H as [x X_x z z_eq]; rewrite z_eq in *; clear z z_eq.
    auto with sets.
Qed.

Lemma image_ident_on:
  forall {U} (X : Ensemble U) (f : U -> U),
  (forall x, In _ X x -> f x = x) -> Im _ _ X f = X.
Proof.
  intros U X f id.
  apply Extensionality_Ensembles; unfold Same_set; split; intros x H.
  - destruct H as [x X_x z z_eq]; rewrite z_eq in *; clear z z_eq.
    rewrite id; auto.
  - apply (Im_intro _ _ _ _ x); try symmetry; auto.
Qed.

Lemma injective_on_preserves_cardinal3:
  forall {U} (i : inhabited U) {V} (X : Ensemble U) (f : U -> V) (n : nat),
  injective_on X f -> cardinal _ (Im _ _ X f) n -> cardinal _ X n.
Proof.
  intros U i V X f n inj X_n.
  destruct (injective_on_inverse i X f inj) as [g g_prop].
  pose (H := injective_on_preserves_cardinal2 (Im _ _ X f) g n).
  rewrite image_compose in H.
  rewrite image_ident_on in H.
  - apply H.
    + intros x y fX_x fX_y gx_gy.
      destruct fX_x as [x X_x z z_eq]; rewrite z_eq in *; clear z z_eq.
      destruct fX_y as [y X_y z z_eq]; rewrite z_eq in *; clear z z_eq.
      rewrite g_prop in gx_gy; try assumption.
      rewrite g_prop in gx_gy; try assumption.
      rewrite gx_gy; trivial.
    + assumption.
  - assumption.
Qed.

Lemma power_set_empty_set:
  forall {U}, Power_set _ (Empty_set U) = Singleton _ (Empty_set U).
Proof.
  intros.
  apply Extensionality_Ensembles; unfold Same_set; split; intros x H.
  - destruct H; intuition.
  - destruct H; split; auto with sets.
Qed.

Lemma power_set_add:
  forall {U} (A : Ensemble U) x,
  Power_set _ (Add _ A x) = Union _ (Power_set _ A) (Im _ _ (Power_set _ A) (fun B => Add _ B x)).
Proof.
  intros U A x.
  apply Extensionality_Ensembles; unfold Same_set; split; intros z H.
  - destruct H as [B B_Ax].
    destruct (classic (In _ B x)).
    + apply Union_intror.
      apply (Im_intro _ _ _ _ (Subtract _ B x)).
      * split.
        apply (Inclusion_is_transitive _ _ (Subtract _ (Add U A x) x)).
        -- apply incl_soustr; assumption.
        -- intuition.
      * intuition.
    + apply Union_introl; split; intros y B_y.
      destruct (B_Ax y).
      * auto with sets.
      * auto with sets.
      * destruct H; destruct H0; assumption.
  - destruct H; destruct H.
    + split; intuition.
    + split; rewrite H0; destruct H; intuition.
Qed.

Lemma finite_power_set:
  forall {U} (X : Ensemble U), Finite _ X -> Finite _ (Power_set _ X).
Proof.
  induction 1.
  - rewrite power_set_empty_set; apply Singleton_is_finite.
  - rewrite power_set_add.
    apply Union_preserves_Finite.
    + assumption.
    + apply finite_image; assumption.
Qed.


Lemma big_union_power_set:
  forall {U} (Xs : Ensemble (Ensemble U)),
  Included _ Xs (Power_set _ (Big_union Xs)).
Proof.
  intros U Xs X Xs_X; split; intros x X_x.
  apply (Big_union_def _ X); assumption.
Qed.

Lemma finite_big_union:
  forall {U} (Xs : Ensemble (Ensemble U)),
  Finite _ (Big_union Xs) -> Finite _ Xs.
Proof.
  intros U Xs fin.
  apply (Finite_downward_closed _ (Power_set _ (Big_union Xs))).
  - apply finite_power_set; assumption.
  - apply big_union_power_set.
Qed.

Module Type Dilworth.

  Parameter U : Type.
  Parameter S : Ensemble U.
  Parameter R : Relation U.
  Axiom Ord : Order U R.

  Theorem dilworth_easy: forall (Cs : Ensemble (Ensemble U)) (A : Ensemble U),
    Included U A (Big_union Cs) ->
    (forall (C : Ensemble U), In _ Cs C -> chain _ R C) ->
    anti_chain _ R A ->
    (exists f : U -> Ensemble U,
      (forall x : U, In _ A x -> In _ (f x) x) /\
      (forall x : U, In _ A x -> In _ Cs (f x)) /\
      (injective_on A f)).
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
    chain _ R C ->
    C = Empty_set _ \/
    (exists (x : U) (C' : Ensemble U), C = Add _ C' x /\ ~ In _ C' x /\ chain _ R C' /\
      (forall y : U, In _ C' y -> ~ R y x /\ R x y)).
  Proof.
    intros C Fin chn.
    destruct (split_min_element C Fin) as [empty | min].
    - auto.
    - destruct min as (x & C' & C_eq & x_new & min).
      refine (or_intror (ex_intro _ x (ex_intro _ C' _))); repeat split.
      + auto.
      + auto.
      + apply (chain_mono _ _ C).
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
      (S = Big_union Cs) /\
      (forall (C : Ensemble U), In _ Cs C -> chain _ R C) /\
      Finite _ A /\
      Included _ A (Big_union Cs) /\
      anti_chain _ R A /\
      (forall X : Ensemble U, In _ Cs X -> In _ A (f X)) /\
      (forall X : Ensemble U, In _ Cs X -> In _ X (f X)) /\
      (injective_on Cs f)).
  Proof.
    intros Fin inh.
    destruct (inh) as [U_wit].
    induction Fin as [S Fin IH] using Generalized_induction_on_finite_sets.
    destruct (split_min_element _ Fin) as [empty | mem].
    - (* the empty set is decomposed into an empty set of chains and an empty antichain *)
      apply (ex_intro _ (Empty_set _)).
      apply (ex_intro _ (Empty_set _)).
      apply (ex_intro _ (fun _ => U_wit)).
      repeat split.
      + auto with sets.
      + intros; destruct H.
      + apply Empty_is_finite.
      + intuition.
      + apply anti_chain_Empty_set.
      + intros; destruct H.
      + intros; destruct H.
      + unfold injective_on; intros; destruct H.
    - (* we have picked a minimum element s in S... apply the induction hypothesis to S - {s}. *)
      destruct mem as (s & S' & S_eq & not_S'_s & s_min).
      assert (fin_S' : Finite _ S').
      {
        apply (Finite_downward_closed _ S).
        - assumption.
        - rewrite S_eq; intuition.
      }
      pose (T := IH).
      rewrite S_eq in T.
      destruct (T S' (strict_included_add S' s not_S'_s)) as
        (Cs0 & A0 & f0 & S'_eq & chain_Cs0 & fin_A0 & sup_A0 & achain_A0 & f0_ran & f0_chn & f0_inj).
      clear T.

      (* Using the antichain A0 and the sets of chains Cs0, we construct an antichain A1 such that
         each element x in A0 is replaced by the maximum element in the chain in Cs0 corresponding
         to x (that chain is given by the inverse of f0) that is a member of an antichain that
         contains an element from each element of Cs0 (these antichains are characterized by the
         anti_chain0 definition). *)
      pose (anti_chain0 (f : Ensemble U -> U) :=
        anti_chain _ R (Im _ _ Cs0 f) /\
        (forall C, In _ Cs0 C -> In _ C (f C)) /\
        (injective_on Cs0 f)).
      assert (ac0_f0 : anti_chain0 f0).
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
        - assert (Im _ _ Cs0 f0 = A0).
          {
            apply Extensionality_Ensembles; split; unfold Included; intros x H.
            - destruct H as [C Cs0_C y y_eq]; rewrite y_eq in *; clear y y_eq.
              intuition.
            - apply (Im_intro _ _ Cs0 _ (g0 x)). intuition. symmetry. intuition.
          }
          rewrite H.
          assumption.
        - intuition.
        - intros C D C_Cs0 D_Cs0. intuition.
      }
      assert (forall (C : Ensemble U), exists (x : U), In _ Cs0 C ->
        In _ C x /\
        (exists f, anti_chain0 f /\ x = f C) /\
        (forall f D, anti_chain0 f -> In _ Cs0 D -> R (f D) x -> f D = x)).
      {
        clear IH s S_eq not_S'_s s_min.
        intros.
        destruct (classic (In (Ensemble U) Cs0 C)) as [Cs0_C | not_Cs0_C].
        + intros.
          pose (D (x : U) := exists f, anti_chain0 f /\ x = f C).
          assert (D_sub_C : Included _ D C).
          {
            unfold Included; unfold D; intros x (f & ac0_f & x_fC).
            destruct ac0_f as (_ & H & _).
            rewrite x_fC; intuition.
          }
          assert (D_chain : chain _ R D). { apply (chain_mono _ _ C); intuition. }
          assert (D_fin : Finite _ D).
          {
            apply (Finite_downward_closed _ C).
            apply (Finite_downward_closed _ S').
            - assumption.
            - rewrite S'_eq.
              intros z C_z.
              apply (Big_union_def Cs0 _ Cs0_C _ C_z).
            - assumption.
          }
          destruct (split_min_element_chain D D_fin D_chain) as
            [empty | (x & D' & D_eq & new & D'_chain & x_min)].
          - assert (In _ D (f0 C)).
            {
              unfold In; unfold D; apply (ex_intro _ f0); auto.
            }
            rewrite empty in H.
            destruct H.
          - apply (ex_intro _ x).
            repeat split.
            * rewrite D_eq in D_sub_C.
              intuition.
            * assert (D_x : In _ D x). { rewrite D_eq; intuition. }
              unfold In in D_x; unfold D in D_x.
              assumption.
            * intros f E ac0_f Cs0_E R_fE_x.
              clear f0 f0_ran f0_chn f0_inj ac0_f0 A0 fin_A0 sup_A0 achain_A0.
              assert (R_x_fC : R x (f C)).
              {
                assert (D_fC : In _ D (f C)).
                {
                  unfold In; unfold D; apply (ex_intro _ f); auto.
                }
                rewrite D_eq in D_fC; rewrite in_add_iff in D_fC.
                destruct D_fC as [x_fC | D'_fC].
                - rewrite x_fC; destruct Ord as [r _ _]; unfold Reflexive in r; auto.
                - pose (x_min (f C)); intuition.
              }
              assert (fE_fC : f E = f C).
              {
                destruct Ord as [_ t _]; unfold Transitive in t.
                pose (t _ _ _ R_fE_x R_x_fC).
                destruct ac0_f as (ax_f & _).
                apply (ax_f); intuition.
              }
              rewrite fE_fC in *.
              destruct Ord as [_ _ a]; apply a; assumption.
        + apply (ex_intro _ U_wit); intuition.
      }
      destruct (choice _ H) as [f1 f1_prop]; clear H.
      assert (ac0_f1 : anti_chain0 f1).
      {
        unfold anti_chain0.
        repeat split.
        - clear IH s S_eq not_S'_s s_min S Fin S' S'_eq fin_S'.
          unfold anti_chain.
          intros x y A_x A_y R_x_y.
          destruct A_x as [Cx Cs0_Cx x x_def]; rewrite x_def in *; clear x x_def.
          destruct A_y as [Cy Cs0_Cy y y_def]; rewrite y_def in *; clear y y_def.
          destruct (f1_prop _ Cs0_Cx) as (_ & (fx & ac0_fx & fxCx_f1Cx) & _).
          destruct (f1_prop _ Cs0_Cy) as (_ & _ & fy_prop).
          rewrite fxCx_f1Cx in R_x_y.
          rewrite (fy_prop fx Cx ac0_fx Cs0_Cx R_x_y) in fxCx_f1Cx; assumption.
        - intros C Cs0_C; pose (f1_prop C); intuition.
        - intros C D Cs0_C Cs0_D f1C_f1D.
          destruct (f1_prop _ Cs0_C) as (_ & (fx & ac0_fx & fxCx_f1Cx) & _).
          destruct (id ac0_fx) as (ac_fx & C_fxC & fx_inj).
          assert (R (f1 D) (fx D)).
          {
            destruct (f1_prop D Cs0_D) as (D_f1D & _ & f1_max).
            pose (f1_max fx D ac0_fx Cs0_D).
            assert (fxD : In _ D (fx D)). { pose (C_fxC D). intuition. }
            assert (f1D : In _ D (f1 D)). { intuition. }
            assert (chD : chain _ R D). { intuition. }
            destruct (chD _ _ fxD f1D).
            - rewrite (e H); destruct Ord as [r _ _]; apply r.
            - assumption.
          }
          rewrite <- f1C_f1D in H; rewrite fxCx_f1Cx in H.
          pose (Im_intro _ _ Cs0 fx C Cs0_C (fx C) eq_refl).
          intuition.
      }
      pose (A1 := Im _ _ Cs0 f1).
      clear A0 f0 fin_A0 sup_A0 achain_A0 f0_ran f0_chn f0_inj ac0_f0.
      (* Now we have a maximum size antichain A1 for S' / Cs0, such that each of the
         elements of A is maximal. We need to decide what to do with s. *)
      assert (A1_S' : Included U A1 S').
      {
        unfold A1; rewrite S'_eq.
        intros x [C Cs0_C y y_eq]; rewrite y_eq in *; clear y y_eq.
        destruct (f1_prop C Cs0_C) as (C_f1C & _).
        apply (Big_union_def Cs0 C Cs0_C _ C_f1C).
      }
      destruct (classic (exists a, In _ A1 a /\ R s a)) as [ (a & A1_a & R_s_a) | no_a ].
      + (* This is the harder case: A0 and A1 are antichains of maximal size,
           so we need to incorporate s into a larger chain. *)
        assert (In _ S' a). { intuition. }
        rewrite S'_eq in H.
        destruct H as [Ca Cs0_Ca a C_a].
        pose (C := Add _ (Intersection _ Ca (fun x => R s x)) s). (* this will be the chain containing s *)
        assert (chain_C : chain _ R C).
        {
          assert (chain _ R Ca). { intuition. }
          unfold C; unfold chain; unfold chain in H.
          assert (R s s). { destruct Ord as [r _ _]; unfold Reflexive in r; intuition. }
          intros x y x_prop y_prop; destruct x_prop as
            [_ [x x_prop] | x []]; destruct y_prop as [_ [y y_prop] | y []]; intuition.
        }
        assert (Ca_a : In _ Ca a). { intuition. }
        pose (S2 := Setminus _ S' C).
        assert (S2_S' : Included U S2 S').
        {
          unfold S2. apply included_setminus.
        }
        destruct (IH S2) as
          [Cs2 (A2 & f2 & S2_eq & Cs2_chain & Fin_A2 & A2_Cs2 & ac_A2 & f2_dom & f2_chn & f2_inj)].
        {
          unfold Strict_Included.
          split.
          - rewrite S_eq; intuition.
          - assert (S_s : In _ S s). { rewrite S_eq. intuition. }
            intro; rewrite <- H in S_s; intuition.
        }
        clear IH.
        assert (ac_A1 : anti_chain _ R A1). { destruct ac0_f1 as [ac_f1 _]; unfold A1; assumption. }
        assert (S_eq' : S = Big_union (Add (Ensemble U) Cs2 C)).
        {
          rewrite Big_union_Add; rewrite <- S2_eq; unfold S2; rewrite S_eq.
          apply Extensionality_Ensembles; unfold Same_set; split; intros x H.
          - destruct H.
            + destruct (classic (In _ C x)); intuition.
            + destruct H; unfold C; intuition.
          - destruct H as [x [S'_x _] | ].
            + auto with sets.
            + unfold C in H; destruct H as [_ [x Ca_x _] | ].
              * rewrite S'_eq; apply Add_intro1; apply (Big_union_def _ Ca); assumption.
              * destruct H; auto with sets.
        }
        destruct (dilworth_easy (Add _ Cs2 C) A1) as (g3 & g3_mem & g3_dom & g3_inj).
        { rewrite <- S_eq'; rewrite S_eq; intuition. }
        { intros; repeat destruct H; intuition. }
        { assumption. }
        assert (forall D, exists x, In _ (Add _ Cs2 C) D -> In _ A1 x /\ g3 x = D).
        {
          assert (f1Ca_a: f1 Ca = a).
          {
            assert (In _ A1 (f1 Ca)). { unfold A1; intuition. }
            destruct (chain_Cs0 _ Cs0_Ca (f1 Ca) a).
            - pose (f1_prop Ca); intuition.
            - assumption.
            - destruct (ac_A1 (f1 Ca) a); auto.
            - destruct (ac_A1 a (f1 Ca)); auto.
          }
          destruct (dilworth_easy Cs2 A2) as (g2 & g2_mem & g2_dom & g2_inj); try assumption. (* is this useful? *)
          intros; destruct (classic (In _ (Add _ Cs2 C) D)) as [Cs2_D | not_Cs2_D].
          - (* At this point, we have:
             * S = Add _ S' s.
             * Cs0: (minimal) decomposition of S' into chains.
             * A1 = Im _ _ Cs0 f1: corresponding antichain of the same cardinality with maximal elements.
             * a in A1 with R s a.
             * Ca in Cs0 with a in Ca.
             * C: new chain consisting of s and all elements x of Ca with R s x. (In particular, a in C)
             * S2: Big_union Cs0 - C
             * Cs2: minimal decomposition of S2 into chains.
             * A2 = Im _ _ Cs2 f2: corresponding antichain of the same cardinality.
             * g2 is the inverse of f2, establishing |A2| = |Cs2|
             * g3 : A1 -> Cs2: injective mapping from A1 to Add _ Cs2 C, so |A1| <= |Cs2| + 1.
             *
             * The argument hinges on showing that |Cs2| = |A2| < |A1| = |Cs0|.
             * We get an injection A2 -> Cs0 from dilworth_easy...
             *)
            assert (A2_eq: A2 = Im _ _ Cs2 f2).
            {
              apply Extensionality_Ensembles; split; unfold Included; intros x H.
              - apply (Im_intro _ _ Cs2 f2 (g2 x)).
                + intuition.
                + assert (chn_g2x : chain _ R (g2 x)). { intuition. }
                  destruct (chn_g2x x (f2 (g2 x))). { intuition. } { intuition. }
                  * apply ac_A2; intuition.
                  * symmetry; apply ac_A2; intuition.
              - destruct H as [E Cs2_E z z_eq]; rewrite z_eq in *; clear z z_eq.
                intuition.
            }
            destruct (dilworth_easy Cs0 A2) as (g0 & g0_mem & g0_dom & g0_inj); try assumption.
            {
              apply (Inclusion_is_transitive _ _ (Big_union Cs2)).
              - assumption.
              - rewrite S'_eq in S2_S'; rewrite S2_eq in S2_S'; assumption.
            }
            destruct (classic (Cs0 = Im _ _ A2 g0)) as [Cs0_eq | nCs0_eq].
            + destruct (injective_on_inverse inh A2 g0 g0_inj) as [f0 f0_prop].
              assert (g0_prop: forall C, In _ Cs0 C -> g0 (f0 C) = C).
              {
                intros E Cs0_E; rewrite Cs0_eq in Cs0_E.
                destruct Cs0_E as [x A2_x z z_eq]; rewrite z_eq in *; clear z z_eq.
                rewrite f0_prop; auto.
              }
              assert (ac0_f0: anti_chain0 f0).
              {
                unfold anti_chain0; rewrite Cs0_eq; repeat split; intros.
                - rewrite image_compose.
                  rewrite image_ident_on; assumption.
                - destruct H as [x A2_x z z_eq]; rewrite z_eq in *; clear z z_eq.
                  rewrite f0_prop; intuition.
                - intros x y Cs0_x Cs0_y f0x_f0y.
                  destruct Cs0_x as [x A2_x z z_eq]; rewrite z_eq in *; clear z z_eq.
                  destruct Cs0_y as [y A2_y z z_eq]; rewrite z_eq in *; clear z z_eq.
                  rewrite f0_prop in f0x_f0y; try assumption.
                  rewrite f0_prop in f0x_f0y; try assumption.
                  rewrite f0x_f0y; auto.
              }
              destruct (f1_prop Ca Cs0_Ca) as (_ & _ & H).
              pose (H f0 Ca ac0_f0 Cs0_Ca); rewrite f1Ca_a in *.
              assert (Ca_f0Ca: In _ Ca (f0 Ca)).
              {
                assert (In _ A2 (f0 Ca)).
                {
                  rewrite Cs0_eq in Cs0_Ca.
                  destruct Cs0_Ca as [y A2_y z z_eq]; rewrite z_eq in *.
                  rewrite f0_prop; assumption.
                }
                pose (g0_mem (f0 Ca) H0).
                rewrite g0_prop in i; assumption.
              }
              assert (R s (f0 Ca)).
              {
                assert (R a (f0 Ca)).
                {
                  destruct (chain_Cs0 _ Cs0_Ca (f0 Ca) a); try assumption.
                  rewrite e; try assumption.
                  destruct Ord as [r _ _]; apply r.
                }
                destruct Ord as [_ t _]; apply (t s a); assumption.
              }
              assert (S2_f0Ca: In _ S2 (f0 Ca)).
              {
                rewrite S2_eq.
                assert (In U A2 (f0 Ca)).
                {
                  rewrite Cs0_eq in Cs0_Ca; destruct Cs0_Ca as [y y_A2 z z_eq]; rewrite z_eq in *.
                  rewrite f0_prop; assumption.
                }
                apply (Big_union_def _ (g2 (f0 Ca))); intuition.
              }
              unfold S2 in S2_f0Ca; destruct S2_f0Ca.
              unfold C in H2.
              destruct H2.
              apply Add_intro1.
              split.
              * assumption.
              * unfold In; assumption.
            + (* Now we know that g0 : A2 -> Cs0 is not surjective. *)
              assert (g0A2_Cs0: Strict_Included _ (Im _ _ A2 g0) Cs0).
              {
                split.
                - intros E Cs0_E; destruct Cs0_E as [y A2_y z z_eq]; rewrite z_eq in *; clear z z_eq.
                  apply g0_dom; assumption.
                - auto.
              }
              assert (Fin_Cs0: Finite _ Cs0).
              { apply finite_big_union; rewrite <- S'_eq; assumption. }
              assert (Fin_Cs2: Finite _ Cs2).
              { apply finite_big_union; rewrite <- S2_eq; apply (Finite_downward_closed _ S'); assumption. }
              destruct (finite_cardinal _ _ Fin_Cs0) as [n Cs0_n].
              assert (A1_n : cardinal _ A1 n).
              {
                unfold A1; apply injective_on_preserves_cardinal2.
                - destruct ac0_f1 as (_ & _ & inj); assumption.
                - assumption.
              }
              destruct (finite_cardinal _ _ (Add_preserves_Finite _ _ C Fin_Cs2)) as [n' Cs2C_n'].
              assert (g3A1_n : cardinal _ (Im _ _ A1 g3) n).
              { apply injective_on_preserves_cardinal2; assumption. }
              assert (g3A1_Cs2C : Included _ (Im _ _ A1 g3) (Add _ Cs2 C)).
              {
                intros y g3A2_y.
                destruct g3A2_y as [y y_eq t t_eq]; rewrite t_eq in *; clear t t_eq; auto.
              }
              assert (n_n': n = n').
              { (* we compare cardinalities. Coq.Sets.Finite_sets is very useful here. *)
                destruct (finite_cardinal _ _ Fin_A2) as [m A2_m].
                assert (g0A2_m : cardinal _ (Im _ _ A2 g0) m).
                { apply injective_on_preserves_cardinal2; assumption. }
                assert (n_gt_m : n > m).
                { apply (fun a b => incl_st_card_lt _ _ _ a _ _ b g0A2_Cs0); assumption. }
                assert (Cs2_m : cardinal _ Cs2 m).
                {
                  apply injective_on_preserves_cardinal3 with _ f2.
                  - auto.
                  - assumption.
                  - rewrite <- A2_eq; assumption.
                }
                assert (n'_le_Sm : n' <= Datatypes.S m). { apply card_Add_gen with _ Cs2 C; assumption. }
                pose (card_Add_gen _ Cs2 C m n' Cs2_m Cs2C_n').
                assert (n <= n').
                { apply incl_card_le with _ (Im _ _ A1 g3) (Add _ Cs2 C); assumption. }
                omega.
              }
              assert (A1g3_eq_Cs2C : (Im _ _ A1 g3) = (Add _ Cs2 C)).
              {
                apply NNPP; intro.
                assert (Strict_Included _ (Im _ _ A1 g3) (Add _ Cs2 C)). { intuition. }
                pose (incl_st_card_lt _ _ _ g3A1_n _ _ Cs2C_n' H0).
                omega.
              }
              rewrite <- A1g3_eq_Cs2C in *.
              destruct Cs2_D as [z z_eq t t_eq]; rewrite t_eq in *; clear t t_eq.
              apply (ex_intro _ z); auto.
          - apply (ex_intro _ U_wit); intuition.
        }
        destruct (choice _ H) as [f3 f3_prop]; clear H.
        (* Finally, we can instantiate the goal. *)
        apply (ex_intro _ (Add _ Cs2 C)).
        apply (ex_intro _ A1).
        apply (ex_intro _ f3).
        repeat split.
        * assumption.
        * intros D H; destruct H as [D Cs2_D | _ []]; intuition.
        * apply (Finite_downward_closed _ S'); assumption.
        * rewrite Big_union_Add; rewrite <- S2_eq; unfold S2.
          apply (Inclusion_is_transitive _ _ S' _ A1_S').
          intros x S'_x.
          destruct (classic (In _ C x)); intuition.
        * assumption.
        * intros; pose (f3_prop X); intuition.
        * intros; destruct (f3_prop X H) as [A1_f3X g3f3X_X]; pose (gm := g3_mem (f3 X)).
          rewrite g3f3X_X in gm; intuition.
        * intros X Y Cs3_X Cs3_Y f3X_f3Y.
          destruct (f3_prop _ Cs3_X) as [_ HX]; rewrite <- HX.
          destruct (f3_prop _ Cs3_Y) as [_ HY]; rewrite <- HY.
          rewrite f3X_f3Y; auto.
      + (* Easy case: s is incomparable to the maximal antichain *)
        apply (ex_intro _ (Add _ Cs0 (Singleton _ s))).
        apply (ex_intro _ (Add _ A1 s)).
        destruct (mem_ex Cs0) as [mem_Cs0 mem_Cs0_prop].
        pose (f C := if mem_Cs0 C then f1 C else s).
        assert (f_s : f (Singleton _ s) = s).
        {
          assert (~ In (Ensemble U) Cs0 (Singleton _ s)).
          {
            intro.
            apply not_S'_s.
            rewrite S'_eq.
            apply (Big_union_def Cs0 (Singleton _ s) H).
            split.
          }
          destruct (mem_Cs0_prop (Singleton _ s)) as [_ mem_Cs0_s].
          unfold f; rewrite (mem_Cs0_s H); auto.
        }
        assert (f_C : forall C, In _ Cs0 C -> f C = f1 C).
        {
          intros.
          destruct (mem_Cs0_prop C) as [mem_Cs0_C _].
          unfold f; rewrite (mem_Cs0_C H); auto.
        }
        apply (ex_intro _ f).
        repeat split.
        * rewrite Big_union_Add; rewrite <- S'_eq; rewrite S_eq.
          intuition.
        * intros; destruct H.
          -- intuition.
          -- destruct H; apply chain_Singleton; apply Ord.
        * apply Add_preserves_Finite.
          apply (Finite_downward_closed _ S' fin_S').
          assumption.
        * rewrite Big_union_Add.
          intros z H.
          destruct H as [x A1_x | b].
          -- rewrite <- S'_eq; intuition.
          -- intuition.
        * unfold anti_chain; intros x y A1s_x A1s_y R_x_y.
          destruct A1s_x as [x A1_x | x s_x]; destruct A1s_y as [y A1_y | y s_y].
          -- destruct ac0_f1 as [ac_f1 _].
            apply ac_f1; assumption.
          -- destruct s_y. destruct ((s_min _ (A1_S' _ A1_x)) R_x_y).
          -- destruct s_x; destruct no_a.
            apply (ex_intro _ y); intuition.
          -- destruct s_x; destruct s_y; auto.
        * intros C [C' Cs0_C' | C' s_C'].
          -- rewrite (f_C C' Cs0_C').
            apply (Add_intro1); unfold A1; intuition.
          -- destruct s_C'; rewrite f_s; intuition.
        * intros C [C' Cs0_C' | C' s_C'].
          -- rewrite (f_C C' Cs0_C').
            destruct (f1_prop C' Cs0_C') as (H & _); assumption.
          -- destruct s_C'; rewrite f_s; intuition.
        * intros C' D' [C Cs0_C | C s_C] [D Cs0_D | D s_D]; clear C' D'.
          -- rewrite (f_C C Cs0_C); rewrite (f_C D Cs0_D).
            destruct ac0_f1 as (_ & _ & f1_inj); intuition.
          -- rewrite (f_C C Cs0_C); destruct s_D; rewrite f_s; intros.
            destruct not_S'_s; unfold A1 in A1_S'.
            apply (A1_S' _ (Im_intro _ _ Cs0 f1 C Cs0_C _ (eq_sym H))).
          -- destruct s_C; rewrite f_s; rewrite (f_C D Cs0_D); intros.
            destruct not_S'_s; unfold A1 in A1_S'.
            apply (A1_S' _ (Im_intro _ _ Cs0 f1 D Cs0_D _ H)).
          -- destruct s_C; destruct s_D; auto.
Qed.

End Dilworth.
