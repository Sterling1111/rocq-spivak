From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_3_a : forall a L, 
  (forall n, exists k : Z, a n = IZR k) ->
  ⟦ lim ⟧ a = L ->
  exists N, forall n, (n >= N)%nat -> a n = L.
Admitted.

Lemma lemma_22_3_b : exists P, P = True.
Admitted.

Lemma lemma_22_3_c : exists P, P = True.
Admitted.

Lemma lemma_22_3_d : forall alpha,
  (exists b, subsequence b (fun _ => 0) /\ ⟦ lim ⟧ b = alpha) -> 0 <= alpha <= 1.
Admitted.
