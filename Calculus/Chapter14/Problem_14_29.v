From Calculus.Chapter14 Require Import Prelude.

(* Problem 29 *)

(* (a) If f is continuous on [0, 1], compute lim_{x→0+} x * ∫ x 1 (f(t)/t) dt *)
Lemma lemma_14_29_a : forall f,
  continuous_on f [0, 1] ->
  ⟦ lim 0⁺ ⟧ (fun x => x * ∫ x 1 (fun t => f t / t)) = f 0.
Admitted.

(* (b) If f is integrable on [0, 1] and continuous at 0,
   compute lim_{x→0+} x * ∫ x 1 (f(t)/t^2) dt *)
Lemma lemma_14_29_b : forall f,
  integrable_on 0 1 f ->
  continuous_at f 0 ->
  ⟦ lim 0⁺ ⟧ (fun x => x * ∫ x 1 (fun t => f t / t^2)) = f 0.
Admitted.
