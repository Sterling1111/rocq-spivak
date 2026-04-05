From Calculus.Chapter18 Require Import Prelude.

(* Problem 11: Let f be a nondecreasing function on [1, \infty), and define F(x) = \int_1^x \frac{f(t)}{t} dt, x >= 1. Prove that f is bounded on [1, \infty) if and only if F/\log is bounded on [1, \infty). *)
Lemma problem_18_11 : forall f F,
  (forall x y, 1 <= x -> x <= y -> f x <= f y) ->
  (forall x, 1 <= x -> F x = ∫ 1 x (fun t => f t / t)) ->
  ((exists M, forall x, 1 <= x -> f x <= M) <->
   (exists M, forall x, 1 <= x -> F x / log x <= M)).
Admitted.
