From Calculus.Chapter18 Require Import Prelude.

(* Problem 36: Suppose f satisfies f' = f and f(x+y) = f(x)f(y) for all x and y. Prove that f = \exp or f = 0. *)
Lemma problem_18_36 : forall f, ⟦ der ⟧ f = f -> (forall x y, f (x + y) = f x * f y) ->
  f = exp \/ f = fun _ => 0. Admitted.
