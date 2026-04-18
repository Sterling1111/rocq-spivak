From Calculus.Chapter19 Require Import Prelude.

(* Problem 17: (a) Find ∫ sin^4 x dx in two different ways. (b) Combine for a trig identity. *)

Lemma lemma_19_17_a : forall c,
  ∫ (λ x, (sin x)^4) = (λ x, 3*x/8 - sin (2*x) / 4 + sin (4*x) / 32 + c).
Abort.

Lemma lemma_19_17_b : forall x,
  (sin x)^4 = 3/8 - cos (2*x) / 2 + cos (4*x) / 8.
Abort.
