From Calculus.Chapter19 Require Import Prelude.

Definition Gamma (x : R) := ∫ 0 ∞ (fun t => exp (-t) * t^(x - 1)).

Lemma lemma_19_40 : forall x, x > 0 -> Gamma (x + 1) = x * Gamma x.
Abort.
