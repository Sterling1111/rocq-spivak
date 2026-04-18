From Calculus.Chapter15 Require Import Prelude.

(* Problem 19 *)

(* (a) ∫_0^1 1/(1+t²) dt = π/4 *)
Lemma lemma_15_19_a :
  ∫ 0 1 (fun t => 1 / (1 + t^2)) = π / 4.
Abort.

(* (b) ∫_0^∞ 1/(1+t²) dt = π/2 *)
Lemma lemma_15_19_b :
  ⟦ lim ∞ ⟧ (fun b => ∫ 0 b (fun t => 1 / (1 + t^2))) = π / 2.
Abort.
