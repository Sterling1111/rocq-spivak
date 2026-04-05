From Calculus.Chapter18 Require Import Prelude.

(* Problem 43: (a) Show that if f satisfies f'' - f = 0, then f(x) = ae^x + be^{-x}... *)
Lemma problem_18_43_a : forall f, ⟦ der ⟧ (⟦ der ⟧ f) = f ->
  exists a b, f = fun x => a * exp x + b * exp (-x). Admitted.
Lemma problem_18_43_b : forall f, ⟦ der ⟧ (⟦ der ⟧ f) = f ->
  exists a b, f = fun x => a * sinh x + b * cosh x. Admitted.
