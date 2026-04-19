From Calculus.Chapter18 Require Import Prelude.

(* Problem 17:
   (a) Find \lim_{y \to 0} \log(1+y)/y.
   (b) Find \lim_{x \to \infty} x \log(1+1/x).
   (c) Prove that e = \lim_{x \to \infty} (1+1/x)^x.
   (d) Prove that e^a = \lim_{x \to \infty} (1+a/x)^x.
   (e) Prove that \log b = \lim_{x \to \infty} x(b^{1/x}-1). *)
Lemma problem_18_17_c : ⟦ lim pinf ⟧ (fun x => exp (x * log (1 + 1/x))) = exp 1. Abort.
