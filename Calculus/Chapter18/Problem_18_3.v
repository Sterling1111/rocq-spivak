From Calculus.Chapter18 Require Import Prelude.

(* Problem 3: Find \int_a^b \frac{f'(t)}{f(t)} dt (for f > 0 on [a,b]). *)
Lemma problem_18_3 : forall f a b,
  (forall x, a <= x <= b -> 0 < f x) ->
  ∫ a b (fun t => ⟦ der ⟧ f t / f t) = log (f b) - log (f a). Admitted.
