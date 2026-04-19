From Calculus.Chapter18 Require Import Prelude.

(* Problem 15: 
   (a) Find the minimum value of f(x) = e^x/x^n for x > 0, and conclude that f(x) > e^n/n^n for x > n. 
   (b) Using the expression f'(x) = e^x(x-n)/x^{n+1}, prove that f'(x) > e^{n+1}/(n+1)^{n+1} for x > n+1 and thus obtain another proof that \lim_{x \to \infty} f(x) = \infty. *)
Lemma problem_18_15_a : forall (n:nat) x, (n > 0)%nat -> x > 0 -> exp x / x^n >= exp (INR n) / (INR n)^n. Abort.
