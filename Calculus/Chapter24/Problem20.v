From Calculus.Chapter24 Require Import Prelude.

Definition Abel_summable (a : nat -> R) (L : R) : Prop :=
  exists f, (forall x, 0 <= x < 1 -> ∑ 0 ∞ (fun n => a n * x^n) = (f x)) /\ ⟦ lim 1⁻ ⟧ f = L.

Lemma lemma_24_20 : exists a L,
  Abel_summable a L /\ ~ series_converges a.
Abort.
