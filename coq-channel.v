(* stuff from #coq discussions *)

Module Q1.

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | B m' => A (incr m')
  | A m' => B m'
  end.

Fixpoint mult_by_2 (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (mult_by_2 n'))
end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A m' => mult_by_2 (bin_to_nat m')
  | B m' => S (mult_by_2 (bin_to_nat m'))
end.

Goal
  forall b, bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  induction b.
  - trivial.
  - trivial.
  - cbn [incr bin_to_nat]; rewrite IHb; trivial.
Qed.

End Q1.

Module Q2.

Inductive Nat : Type := Z | S (pred : Nat).

Inductive Bin : Nat -> Type :=
  | BE : Bin Z
  | B0 : forall {n}, Bin n -> Bin (S n)
  | B1 : forall {n}, Bin n -> Bin (S n).

Fixpoint Incr {n : Nat} (a : Bin n) : Bin n :=
  match a with
  | BE => BE
  | B0 x => B1 x
  | B1 x => B0 (Incr x)
  end.

Definition Z_neq_S : forall {n}, Z = S n -> False.
  intros; discriminate H.
Defined.

Definition S_neq_Z : forall {n}, S n = Z -> False.
  intros; discriminate H.
Defined.

Definition pred_eq : forall {n m}, S n = S m -> n = m.
  intros. injection H. intros. assumption.
Defined.

Definition cast_Bin : forall {n m}, n = m -> Bin n -> Bin m.
  intros n m H. destruct H. intros. assumption.
Defined.

Fixpoint Add {n : Nat} (a : Bin n) (b : Bin n) : Bin (S n) :=
  match a in Bin k, b in Bin l return k = l -> Bin (S l) with
  | B0 a, B0 b => fun pf => B0 (Add (cast_Bin (pred_eq pf) a) b)
  | B0 a, B1 b => fun pf => B1 (Add (cast_Bin (pred_eq pf) a) b)
  | B1 a, B0 b => fun pf => B1 (Add (cast_Bin (pred_eq pf) a) b)
  | B1 a, B1 b => fun pf => B0 (Incr (Add (cast_Bin (pred_eq pf) a) b))
  | BE, BE => fun _ => B0 BE
  | BE, _ => fun pf => False_rect _ (Z_neq_S pf)
  | _, BE => fun pf => False_rect _ (S_neq_Z pf)
  end eq_refl (* pass in evidence that the two scrutinees have equal size *).

Compute (Add (B1 (B1 BE)) (B0 (B1 BE))).

(* TODO: there's a function definition package at https://github.com/mattam82/Coq-Equations *)

(* solution by Cypi *)
Fixpoint Add' {n : Nat} (a : Bin n) (b : Bin n) : Bin (S n)
  :=
  match a in Bin n return Bin n -> Bin (S n) with
  | BE => fun b =>
    match b with
      | BE => B0 BE
    end
  | B0 a => fun b =>
    match b with
      | B0 b => fun a => B0 (Add a b)
      | B1 b => fun a => B1 (Add a b)
    end a
  | B1 a => fun b =>
    match b with
      | B0 b => fun a => B1 (Add a b)
      | B1 b => fun a => B0 (Incr (Add a b))
    end a
  end b.

Compute (Add' (B1 (B1 BE)) (B0 (B1 BE))).

End Q2.
