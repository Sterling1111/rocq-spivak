From Calculus.Chapter22 Require Import Prelude.

From Calculus.Chapter22 Require Import Problem14.

Lemma lemma_22_15_i :
  ∃ r, 0 < r < 1 /\ tan r - cos r ^ 2 = 0 /\
    ⟦ lim ⟧ (newton_sequence (λ x, tan x - cos x ^ 2) 0) = r.
Abort.

Lemma lemma_22_15_ii :
  ∃ r, 0 < r < 1 /\ cos r - r^2 = 0 /\ cos (-r) - (-r)^2 = 0 /\
    ⟦ lim ⟧ (newton_sequence (λ x, cos x - x^2) 1) = r /\
    ⟦ lim ⟧ (newton_sequence (λ x, cos x - x^2) (-1)) = -r.
Abort.

Lemma lemma_22_15_iii :
  ∃ r, r ∈ [0, 1] /\ r^3 + r - 1 = 0 /\
    ⟦ lim ⟧ (newton_sequence (λ x, x^3 + x - 1) 1) = r.
Abort.

Lemma lemma_22_15_iv :
  ∃ r, r ∈ [0, 1] /\ r^3 - 3*r^2 + 1 = 0 /\
    ⟦ lim ⟧ (newton_sequence (λ x, x^3 - 3*x^2 + 1) (1/2)) = r.
Abort.
