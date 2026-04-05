From Calculus.Chapter14 Require Import Prelude.

(* Problem 3: Show that the values of the following expressions do not depend on x. *)

(* (a) ∫ 0 x (1/(1+t^2)) dt + ∫ 0 (1/x) (1/(1+t^2)) dt *)
Lemma lemma_14_3_a : forall x,
  x > 0 ->
  ⟦ der x ⟧ (fun x => ∫ 0 x (fun t => 1 / (1 + t^2)) + ∫ 0 (1/x) (fun t => 1 / (1 + t^2))) =
    (fun _ => 0).
Admitted.

(* (b) ∫ (-cos x) (sin x) (1/√(1-t^2)) dt, x in (0, π/2) *)
Lemma lemma_14_3_b : forall x,
  0 < x < PI/2 ->
  ⟦ der x ⟧ (fun x => ∫ (-(cos x)) (sin x) (fun t => 1 / √(1 - t^2))) =
    (fun _ => 0).
Admitted.
