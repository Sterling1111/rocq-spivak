From Calculus.Chapter15 Require Import Prelude.

(* Problem 13: Fourier coefficients minimize L² error *)

(* (a) Optimal coefficients for cos and sin approximation *)
Lemma lemma_15_13_a_cos : forall f (n : nat),
  integrable_on (-π) π f ->
  forall a, ∫ (-π) π (fun x => (f x - a * cos (INR n * x))^2) >=
            ∫ (-π) π (fun x => (f x - (1/π * ∫ (-π) π (fun t => f t * cos (INR n * t))) * cos (INR n * x))^2).
Abort.

Lemma lemma_15_13_a_sin : forall f (n : nat),
  integrable_on (-π) π f ->
  forall a, ∫ (-π) π (fun x => (f x - a * sin (INR n * x))^2) >=
            ∫ (-π) π (fun x => (f x - (1/π * ∫ (-π) π (fun t => f t * sin (INR n * t))) * sin (INR n * x))^2).
Abort.
