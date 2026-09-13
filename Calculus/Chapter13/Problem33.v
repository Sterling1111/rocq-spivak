From Calculus.Chapter13 Require Import Prelude.

From Lib Require Import Rational.

Definition f_13_33 (x : R) :=
  if excluded_middle_informative (rational x) then x else 0.

Lemma lemma_13_33_a : ∀ (bf : bounded_function_R 0 1) (P : partition 0 1),
  bounded_f 0 1 bf = f_13_33 -> L(bf, P) = 0.
Abort.

Lemma lemma_13_33_b : ∀ bf : bounded_function_R 0 1,
  bounded_f 0 1 bf = f_13_33 -> smallest_upper_sum 0 1 bf = 1/2.
Abort.
