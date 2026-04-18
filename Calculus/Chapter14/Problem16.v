From Calculus.Chapter14 Require Import Prelude.

(* Problem 16 *)

(* (a) Find the derivatives of F(x) = ∫ 1 x (1/t) dt and G(x) = ∫ b (b*x) (1/t) dt. *)
Lemma lemma_14_16_a : forall x,
  x > 0 ->
  ⟦ der x ⟧ (fun x => ∫ 1 x (fun t => 1 / t)) = (fun x => 1 / x).
Abort.

Lemma lemma_14_16_a' : forall b x,
  b > 0 -> x > 0 ->
  ⟦ der x ⟧ (fun x => ∫ b (b * x) (fun t => 1 / t)) = (fun x => 1 / x).
Abort.

(* (b) New proof for Problem 13-15: ∫ 1 a (1/t) dt + ∫ 1 b (1/t) dt = ∫ 1 (a*b) (1/t) dt *)
Lemma lemma_14_16_b : forall a b,
  a > 0 -> b > 0 ->
  ∫ 1 a (fun t => 1 / t) + ∫ 1 b (fun t => 1 / t) = ∫ 1 (a * b) (fun t => 1 / t).
Abort.
