From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_17_a :
   ⟦ lim 0 ⟧ (fun y => log (1 + y) / y) = 1.
Abort.

Lemma lemma_18_17_b :
   ⟦ lim ∞ ⟧ (fun x => x * log (1 + 1 / x)) = 1.
Abort.

Lemma lemma_18_17_c :
   ⟦ lim ∞ ⟧ (fun x => exp (x * log (1 + 1 / x))) = exp 1.
Abort.

Lemma lemma_18_17_d : forall a,
   ⟦ lim ∞ ⟧ (fun x => exp (x * log (1 + a / x))) = exp a.
Abort.

Lemma lemma_18_17_e : forall b,
   b > 0 ->
   ⟦ lim ∞ ⟧ (fun x => x * (b ^^ (1 / x) - 1)) = log b.
Abort.
