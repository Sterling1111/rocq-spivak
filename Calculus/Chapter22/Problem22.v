From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_22_a : forall c m n,
  c <> 1 -> (m <= n)%nat ->
  ∑ m n (fun i => c ^ i) = (c ^ m - c ^ (n + 1)) / (1 - c).
Abort.

Lemma lemma_22_22_b : forall c,
  Rabs c < 1 ->
  forall ε, ε > 0 ->
  exists N, forall m n, (n >= m)%nat -> (m >= N)%nat ->
  Rabs (∑ m n (fun i => c ^ i)) < ε.
Abort.

Lemma lemma_22_22_c : forall x c,
  0 < c < 1 ->
  (forall n, Rabs (x (n + 1)%nat - x n) <= c ^ n) ->
  cauchy_sequence x.
Abort.
