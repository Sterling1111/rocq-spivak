From Calculus.Chapter19 Require Import Prelude.

(* Figure 14: the region under cos x, 0 <= x <= π/2, rotated about the vertical axis. *)
Lemma lemma_19_App_6_a : 2*π * ∫ 0 (π/2) (λ x, x*cos x) = π^2-2*π.
Abort.
Lemma lemma_19_App_6_b : π * ∫ 0 1 (λ y, arccos y^2) = π^2-2*π.
Abort.
