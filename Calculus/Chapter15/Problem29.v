From Calculus.Chapter15 Require Import Prelude.

(* Problem 29: Defining trig functions via arctan *)

(* (a) α(x) = ∫_0^x 1/(1+t²) dt is odd, increasing, with limit π/2 *)
Lemma lemma_15_29_a :
  let α := fun x => ∫ 0 x (fun t => 1 / (1 + t^2)) in
  (forall x, α (-x) = - α x) /\
  increasing α /\
  ⟦ lim ∞ ⟧ α = π / 2.
Abort.

(* (b) (α⁻¹)'(x) = 1 + (α⁻¹(x))² *)
Lemma lemma_15_29_b : forall α α_inv,
  (forall x, α x = ∫ 0 x (fun t => 1 / (1 + t^2))) ->
  inverse_on α α_inv (-π / 2, π / 2) ℝ ->
  forall x, x ∈ (-π / 2, π / 2) ->
  ⟦ der x ⟧ α_inv = (fun x => 1 + (α_inv x)^2).
Abort.

(* (c) Properties of sin defined via tan *)
Lemma lemma_15_29_c_i :
  ⟦ lim (π/2)⁻ ⟧ sin = 1.
Abort.

Lemma lemma_15_29_c_ii :
  ⟦ lim (-π/2)⁺ ⟧ sin = -1.
Abort.

Lemma lemma_15_29_c_iv : forall x,
  ⟦ Der^2 x ⟧ sin = - sin x.
Abort.
