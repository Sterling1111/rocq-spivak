From Calculus.Chapter15 Require Import Prelude.

(* Problem 28: Defining trig functions via arc length *)

(* (a) 𝔉(x) = ∫_x^1 1/√(1-t²) dt is the arc length of √(1-x²) on [x,1] *)
Lemma lemma_15_28_a : forall x,
  -1 < x < 1 ->
  let F := fun x => ∫ x 1 (fun t => 1 / √(1 - t^2)) in
  F x = ∫ x 1 (fun t => √(1 + ((⟦ Der t ⟧ (fun x => √(1 - x^2)))^2))).
Admitted.

(* (b) 𝔉'(x) = -1/√(1-x²) *)
Lemma lemma_15_28_b : forall x,
  -1 < x < 1 ->
  let F := fun x => ∫ x 1 (fun t => 1 / √(1 - t^2)) in
  ⟦ der x ⟧ F = (fun x => -1 / √(1 - x^2)).
Admitted.

(* (c) cos'(x) = -sin x and sin'(x) = cos x *)
Lemma lemma_15_28_c :
  ⟦ der ⟧ cos = (fun x => - sin x) /\
  ⟦ der ⟧ sin = cos.
Admitted.
