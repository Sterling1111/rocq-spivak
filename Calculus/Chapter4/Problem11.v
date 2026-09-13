From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_11_i :
  ∀ f, even f -> ∀ x y, ((pair (x) (y)) ∈ graph f <-> (pair (-x) (y)) ∈ graph f).
Abort.

Lemma lemma_4_11_ii :
  ∀ f, odd f -> ∀ x y, ((pair (x) (y)) ∈ graph f <-> (pair (-x) (-y)) ∈ graph f).
Abort.

Lemma lemma_4_11_iii :
  ∀ f, nonnegative f -> ∀ x y, (pair (x) (y)) ∈ graph f -> 0 <= y.
Abort.

Lemma lemma_4_11_iv :
  ∀ f a, periodic f a -> ∀ x y, ((pair (x) (y)) ∈ graph f <-> (pair (x+a) (y)) ∈ graph f).
Abort.
