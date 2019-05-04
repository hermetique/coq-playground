(* partly inspired by "Coq in a Hurry" *)

Check False.
Check (3,3).
Compute let f := fun x => (x * 3, x) in f 3.
Definition example1 := fun x : nat => x*x + 2*x + 1.
Compute example1 5.

Require Import Bool.
Require Import Arith.

Print bool.
Print pred.
Print Init.Nat.pred.

Locate "_ <= _".
Locate "_ -> _".

SearchPattern (nat -> bool).
SearchPattern (_ + _ <= _ + _).
SearchRewrite (_ + (_ + _)).

Fixpoint sum_n n :=
  match n with
    0 => 0
  | S p => p + sum_n p
  end.

Theorem sum_n_eq:
  forall n, 2 * sum_n n = n * (n - 1).
Proof.
  intro n; induction n.
  - auto.
  - pose (s := sum_n (S n)); fold s; simpl in s; unfold s; clear s. (* eww, but direct 'simpl' goes too far *)
    rewrite Nat.mul_add_distr_l. rewrite IHn.
    case n.
    + reflexivity.
    + intro n'.
      repeat (rewrite Nat.mul_succ_l || rewrite Nat.add_succ_l || rewrite Nat.mul_succ_r ||
        rewrite Nat.add_succ_r || rewrite Nat.add_0_r || rewrite Nat.add_0_l || rewrite Nat.sub_succ ||
        rewrite Nat.sub_0_r).
      ring.
Qed.

(* discriminate / injection *)
(* Open Scope Z_scope. *)
Require Import ZArith.
About Z.iter.
