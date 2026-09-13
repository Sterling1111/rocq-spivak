From Calculus.Chapter3 Require Export Prelude.

(* Nodes and prescribed values retain the PDF's indexing 1,...,n. *)
Lemma lemma_3_6_a : ∀ (n : nat) (x : nat -> R),
  (1 <= n)%nat ->
  (∀ i j, (1 <= i <= n)%nat -> (1 <= j <= n)%nat -> x i = x j -> i = j) ->
  ∀ i, (1 <= i <= n)%nat -> ∃ l : list R,
    degree l = (n - 1)%nat /\ polynomial l (x i) = 1 /\
    (∀ j, (1 <= j <= n)%nat -> j <> i -> polynomial l (x j) = 0).
Abort.

(* PDF p.49 says degree n-1; arbitrary data only guarantee degree AT MOST n-1. *)
Lemma lemma_3_6_b : ∀ (n : nat) (x a : nat -> R),
  (1 <= n)%nat ->
  (∀ i j, (1 <= i <= n)%nat -> (1 <= j <= n)%nat -> x i = x j -> i = j) ->
  ∃ l : list R, (degree l <= n - 1)%nat /\
    (∀ i, (1 <= i <= n)%nat -> polynomial l (x i) = a i).
Abort.
