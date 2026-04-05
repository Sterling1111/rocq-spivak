From Calculus.Chapter18 Require Import Prelude.

Definition sinh (x : R) := (exp x - exp (-x)) / 2.
Definition cosh (x : R) := (exp x + exp (-x)) / 2.
Definition tanh (x : R) := sinh x / cosh x.

Lemma lemma_18_8 :
  one_to_one sinh /\ one_to_one tanh.
Admitted.
