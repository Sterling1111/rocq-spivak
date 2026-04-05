From Calculus.Chapter14 Require Import Prelude.

(* Problem 1: Find the derivatives of each of the following functions. *)

(* (i) F(x) = ∫ a x^3 (sin t)^3 dt *)
Lemma lemma_14_1_i : forall a x,
  ⟦ der x ⟧ (fun x => ∫ a (x^3) (fun t => (sin t)^3)) =
    (fun x => 3 * x^2 * (sin (x^3))^3).
Admitted.

(* (ii) F(x) = ∫ 3 (∫ 1 x (sin t)^3 dt) (1 / (1 + (sin t)^6 + t^2)) dt *)
Lemma lemma_14_1_ii : forall x,
  ⟦ der x ⟧ (fun x => ∫ 3 (∫ 1 x (fun t => (sin t)^3))
    (fun t => 1 / (1 + (sin t)^6 + t^2))) =
    (fun x => (sin x)^3 / (1 + (sin (∫ 1 x (fun t => (sin t)^3)))^6 + (∫ 1 x (fun t => (sin t)^3))^2)).
Admitted.

(* (iii) F(x) = ∫ 15 x (∫ 8 y (1 / (1 + t^2 + (sin t)^2)) dt) dy *)
Lemma lemma_14_1_iii : forall x,
  ⟦ der x ⟧ (fun x => ∫ 15 x (fun y => ∫ 8 y (fun t => 1 / (1 + t^2 + (sin t)^2)))) =
    (fun x => ∫ 8 x (fun t => 1 / (1 + t^2 + (sin t)^2))).
Admitted.

(* (iv) F(x) = ∫ x b (1 / (1 + t^2 + (sin t)^2)) dt *)
Lemma lemma_14_1_iv : forall b x,
  ⟦ der x ⟧ (fun x => ∫ x b (fun t => 1 / (1 + t^2 + (sin t)^2))) =
    (fun x => - (1 / (1 + x^2 + (sin x)^2))).
Admitted.

(* (v) F(x) = ∫ a b (x / (1 + t^2 + (sin t)^2)) dt *)
Lemma lemma_14_1_v : forall a b,
  a < b ->
  ⟦ der ⟧ (fun x => ∫ a b (fun t => x / (1 + t^2 + (sin t)^2))) =
    (fun x => ∫ a b (fun t => 1 / (1 + t^2 + (sin t)^2))).
Admitted.

(* (vi) F(x) = sin(∫ 0 x (sin(∫ 0 y (sin t)^3 dt)) dy) *)
Lemma lemma_14_1_vi : forall x,
  ⟦ der x ⟧ (fun x => sin (∫ 0 x (fun y => sin (∫ 0 y (fun t => (sin t)^3))))) =
    (fun x => cos (∫ 0 x (fun y => sin (∫ 0 y (fun t => (sin t)^3)))) *
              sin (∫ 0 x (fun t => (sin t)^3))).
Admitted.

(* (vii) (F^{-1})' where F(x) = ∫ 1 x (1/t) dt *)
Lemma lemma_14_1_vii : forall F F_inv,
  (forall x, x > 0 -> F x = ∫ 1 x (fun t => 1 / t)) ->
  inverse F F_inv ->
  ⟦ der ⟧ F_inv = (fun y => F_inv y).
Admitted.

(* (viii) (F^{-1})' where F(x) = ∫ 0 x (1/√(1-t^2)) dt *)
Lemma lemma_14_1_viii : forall F F_inv,
  (forall x, -1 < x < 1 -> F x = ∫ 0 x (fun t => 1 / √(1 - t^2))) ->
  inverse F F_inv ->
  ⟦ der ⟧ F_inv = (fun y => √(1 - (F_inv y)^2)).
Admitted.
