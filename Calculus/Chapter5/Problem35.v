From Calculus.Chapter5 Require Import Prelude.

Section Problem35.

Variable α : R.
Hypothesis H1 : ⟦ lim 0 ⟧ (fun x => sin x / x) = α.

Lemma lemma_5_35_i : ⟦ lim ∞ ⟧ (fun x => sin x / x) = 0.
Proof.
Abort.

Lemma lemma_5_35_ii : ⟦ lim ∞ ⟧ (fun x => x * sin (1 / x)) = α.
Proof.
Abort.

End Problem35.