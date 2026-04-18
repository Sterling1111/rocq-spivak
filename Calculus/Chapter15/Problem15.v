From Calculus.Chapter15 Require Import Prelude.

(* Problem 15 *)

(* (a) sin²x and cos²x in terms of cos 2x *)
Lemma lemma_15_15_a_sin2 : forall x,
  (sin x)^2 = (1 - cos (2 * x)) / 2.
Abort.

Lemma lemma_15_15_a_cos2 : forall x,
  (cos x)^2 = (1 + cos (2 * x)) / 2.
Abort.

(* (b) Half-angle formulas for 0 ≤ x ≤ π/2 *)
Lemma lemma_15_15_b_cos_half : forall x,
  0 <= x <= π / 2 ->
  cos (x / 2) = √((1 + cos x) / 2).
Abort.

Lemma lemma_15_15_b_sin_half : forall x,
  0 <= x <= π / 2 ->
  sin (x / 2) = √((1 - cos x) / 2).
Abort.

(* (c) ∫ sin²x dx and ∫ cos²x dx *)
Lemma lemma_15_15_c_sin2 : forall a b,
  a < b ->
  ∫ a b (fun x => (sin x)^2) = (b - a) / 2 - (sin (2 * b) - sin (2 * a)) / 4.
Abort.

Lemma lemma_15_15_c_cos2 : forall a b,
  a < b ->
  ∫ a b (fun x => (cos x)^2) = (b - a) / 2 + (sin (2 * b) - sin (2 * a)) / 4.
Abort.
