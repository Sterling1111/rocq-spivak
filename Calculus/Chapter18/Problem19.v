From Calculus.Chapter18 Require Import Prelude.

(* Problem 19: (a) Let f(x) = \log|x| for x \ne 0. Prove that f'(x) = 1/x for x \ne 0. 
   (b) If f(x) \ne 0 for all x, prove that (\log|f|)' = f'/f. *)
Lemma problem_18_19_a : forall x, x <> 0 -> ⟦ der ⟧ (fun x => log (Rabs x)) x = 1 / x. Abort.
Lemma problem_18_19_b : forall f x, f x <> 0 -> ⟦ der ⟧ (fun x => log (Rabs (f x))) x = ⟦ der ⟧ f x / f x. Abort.
