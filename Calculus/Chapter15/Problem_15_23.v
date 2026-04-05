From Calculus.Chapter15 Require Import Prelude.

(* Problem 23 *)

(* (a) π is the maximum length of an interval on which sin is one-to-one *)
Lemma lemma_15_23_a : forall a b,
  b - a > π ->
  ~ one_to_one_on sin [a, b].
Admitted.

(* (b) Derivative of g^{-1} where g = sin on (2kπ - π/2, 2kπ + π/2) *)
Lemma lemma_15_23_b : forall g g_inv (k : Z),
  (forall x, x ∈ (IZR k * 2 * π - π / 2, IZR k * 2 * π + π / 2) -> g x = sin x) ->
  inverse_on g g_inv (IZR k * 2 * π - π / 2, IZR k * 2 * π + π / 2) (-1, 1) ->
  forall y, y ∈ (-1, 1) ->
  ⟦ der y ⟧ g_inv = (fun y => 1 / √(1 - y^2)).
Admitted.
