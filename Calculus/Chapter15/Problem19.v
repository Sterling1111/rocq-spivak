From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_19_a :
  ∫ 0 1 (fun t => 1 / (1 + t^2)) = π / 4.
Proof.
  auto_int.
Qed.

Lemma lemma_15_19_b :
  ⟦ lim ∞ ⟧ (fun b => ∫ 0 b (fun t => 1 / (1 + t^2))) = π / 2.
Abort.