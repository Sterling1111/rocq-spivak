From Calculus.Chapter18 Require Import Prelude.

(* Problem 38: Prove that if f is a continuous function defined on the positive real numbers, and f(xy) = f(x) + f(y) for all positive x and y, then f = 0 or f(x) = f(e)\log x for all x > 0. *)
Lemma problem_18_38 : forall f,
  (forall x, 0 < x -> continuous_at f x) ->
  (forall x y, 0 < x -> 0 < y -> f (x * y) = f x + f y) ->
  f = (fun _ => 0) \/ (exists c, forall x, 0 < x -> f x = c * log x). Abort.
