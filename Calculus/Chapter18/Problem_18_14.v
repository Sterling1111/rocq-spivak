From Calculus.Chapter18 Require Import Prelude.

(* Problem 14: (a) Find the minimum value of f(x) = e^x/x^n for x > 0, and conclude that f(x) > e^n/n^n for x > n. 
   (b) Using the expression f'(x) = e^x(x-n)/x^{n+1}, prove that f'(x) > e^{n+1}/(n+1)^{n+1} for x > n+1 and thus obtain another proof that \lim_{x \to \infty} f(x) = \infty. *)
Lemma problem_18_14_a : forall n x, 0 < x -> exp x / x^n >= exp n / n^n. Admitted.
Lemma problem_18_14_b : forall n x, x > n + 1 -> ⟦ der ⟧ (fun x => exp x / x^n) x > exp (n+1) / (n+1)^(n+1). Admitted.
