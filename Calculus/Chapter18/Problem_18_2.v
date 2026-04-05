From Calculus.Chapter18 Require Import Prelude.

(* Problem 2: (a) Check that the derivative of log ∘ f is f'/f. (b) Use logarithmic differentiation to find f'(x) for each of the following. *)
(* (a) *)
Lemma problem_18_2_a : forall f x, ⟦ der ⟧ (fun x => log (f x)) x = ⟦ der ⟧ f x / f x. Admitted.
