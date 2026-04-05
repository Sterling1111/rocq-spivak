From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_1_i : forall x,
  ⟦ der x ⟧ (fun x => arctan (arctan (arctan x))) =
    (fun x => 1 / (1 + (arctan (arctan x))^2) *
              (1 / (1 + (arctan x)^2)) *
              (1 / (1 + x^2))).
Admitted.

Lemma lemma_15_1_ii : forall x,
  -1 < x < 1 ->
  ⟦ der x ⟧ (fun x => arcsin (arctan (arccos x))) =
    (fun x => 1 / √(1 - (arctan (arccos x))^2) *
              (1 / (1 + (arccos x)^2)) *
              (-1 / √(1 - x^2))).
Admitted.

Lemma lemma_15_1_iii : forall x,
  cos x <> 0 ->
  ⟦ der x ⟧ (fun x => arctan (tan x * arctan x)) =
    (fun x => 1 / (1 + (tan x * arctan x)^2) *
              (sec x^2 * arctan x + tan x * (1 / (1 + x^2)))).
Admitted.

Lemma lemma_15_1_iv : forall x,
  x > 0 ->
  ⟦ der x ⟧ (fun x => arcsin (1 / √(1 + x^2))) =
    (fun x => -1 / (1 + x^2)).
Admitted.

Lemma lemma_15_1_v : forall a b,
  a < b ->
  ⟦ der ⟧ (fun x => ∫ a b (fun t => x / (1 + t^2 + (sin t)^2))) =
    (fun x => ∫ a b (fun t => 1 / (1 + t^2 + (sin t)^2))).
Admitted.

Lemma lemma_15_1_vi : forall x,
  ⟦ der x ⟧ (fun x => sin (∫ 0 x (fun y => sin (∫ 0 y (fun t => (sin t)^3))))) =
    (fun x => cos (∫ 0 x (fun y => sin (∫ 0 y (fun t => (sin t)^3)))) *
              sin (∫ 0 x (fun t => (sin t)^3))).
Admitted.

Lemma lemma_15_1_vii : forall F F_inv,
  (forall x, x > 0 -> F x = ∫ 1 x (fun t => 1 / t)) ->
  inverse F F_inv ->
  ⟦ der ⟧ F_inv = (fun y => F_inv y).
Admitted.

Lemma lemma_15_1_viii : forall F F_inv,
  (forall x, -1 < x < 1 -> F x = ∫ 0 x (fun t => 1 / √(1 - t^2))) ->
  inverse F F_inv ->
  ⟦ der ⟧ F_inv = (fun y => √(1 - (F_inv y)^2)).
Admitted.
