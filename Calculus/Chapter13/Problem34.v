From Calculus.Chapter13 Require Import Prelude.

From Lib Require Import Rational.

Definition thomae_function (f : R -> R) : Prop :=
  (∀ x, irrational x -> f x = 0) /\
  (∀ (p : Z) (q : nat), (0 < q)%nat ->
    Z.gcd p (Z.of_nat q) = 1%Z -> f (p / q) = 1 / q).

Lemma lemma_13_34 : ∀ f,
  thomae_function f -> integrable_on 0 1 f /\ ∫ 0 1 f = 0.
Abort.
