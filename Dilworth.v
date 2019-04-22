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

  Theorem dilworth_easy: forall (Cs : Ensemble (Ensemble U)) (A : Ensemble U),
    Included U A (Big_union Cs) ->
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
      (S = Big_union Cs) /\
      (forall (C : Ensemble U), In _ Cs C -> chain C) /\
      Finite _ A /\
      Included _ A (Big_union Cs) /\
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
      + apply anti_chain_Empty_set.
      + intros; destruct H.
      + intros; destruct H.
      + intros; destruct H.
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
        anti_chain (Im _ _ Cs0 f) /\
        (forall C, In _ Cs0 C -> In _ C (f C)) /\
        (forall C D, In _ Cs0 C -> In _ Cs0 D -> f C = f D -> C = D)).
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
          assert (D_chain : chain D). { apply (chain_mono C); intuition. }
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
            assert (chD : chain D). intuition.
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
      destruct (classic (exists a, In _ A1 a /\ R s a)) as [ (a & A1_a & R_s_a) | no_a ].
      + (* This is the harder case: A0 and A1 are antichains of maximal size,
           so we need to incorporate s into a larger chain. *)
        admit.
      + apply (ex_intro _ (Add _ Cs0 (Singleton _ s))).
        apply (ex_intro _ (Add _ A1 s)).
        destruct (mem_ex Cs0) as [mem_Cs0 mem_Cs0_prop].
        assert (A1_S' : Included U A1 S').
        {
          unfold A1; rewrite S'_eq.
          intros x [C Cs0_C y y_eq]; rewrite y_eq in *; clear y y_eq.
          destruct (f1_prop C Cs0_C) as (C_f1C & _).
          apply (Big_union_def Cs0 C Cs0_C _ C_f1C).
        }
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
          -- destruct H; apply chain_Singleton.
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
  Abort All.

End Dilworth.
