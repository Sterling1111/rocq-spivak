From Calculus.Chapter18 Require Import Prelude.

(* Problem 7: Properties of sinh, cosh, tanh. *)
Definition sinh (x : R) := (exp x - exp (-x)) / 2.
Definition cosh (x : R) := (exp x + exp (-x)) / 2.
Definition tanh (x : R) := (exp x - exp (-x)) / (exp x + exp (-x)).

Lemma problem_18_7_a : forall x, cosh x ^ 2 - sinh x ^ 2 = 1. Admitted.
Lemma problem_18_7_b : forall x, tanh x ^ 2 + 1 / cosh x ^ 2 = 1. Admitted.
Lemma problem_18_7_c : forall x y, sinh (x + y) = sinh x * cosh y + cosh x * sinh y. Admitted.
Lemma problem_18_7_d : forall x y, cosh (x + y) = cosh x * cosh y + sinh x * sinh y. Admitted.
Lemma problem_18_7_e : ⟦ der ⟧ sinh = cosh. Admitted.
Lemma problem_18_7_f : ⟦ der ⟧ cosh = sinh. Admitted.
Lemma problem_18_7_g : ⟦ der ⟧ tanh = fun x => 1 / cosh x ^ 2. Admitted.
