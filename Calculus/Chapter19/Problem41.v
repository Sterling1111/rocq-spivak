From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_41 : forall n,
  (n > 0)%nat ->
  ∫ 0 (π/2) (fun x => (sin x)^n) = ∫ 0 (π/2) (fun x => (cos x)^n).
Abort.
