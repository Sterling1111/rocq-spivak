From Calculus.Chapter18 Require Import Prelude.

(* Problem 16: Find the specified limits and prove that e = \lim_{x \to \infty} (1+1/x)^x. *)
Lemma problem_18_16 : limit_at_infinity (fun x => (1 + 1/x)^x) (exp 1). Admitted.
