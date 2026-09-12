From Calculus.Chapter18 Require Import Prelude.

(* A list of at most m coefficients represents a polynomial of degree < m;
   the empty list represents zero, including when m=0. *)
From Lib Require Import Polynomial.

Lemma lemma_18_45_a : ∀ n f, (1 <= n)%nat ->
  ((∃ g, ⟦ der ^ (n-1) ⟧ f = g /\ ⟦ der ⟧ g = g) <->
   (∃ c l, (List.length l <= n-1)%nat /\
  ∀ x, f x = c * exp x + polynomial l x)).
Abort.

Lemma lemma_18_45_b : ∀ n f, (2 <= n)%nat ->
  ((∃ g, ⟦ der ^ (n-2) ⟧ f = g /\ ⟦ der ^ 2 ⟧ g = g) <->
   (∃ a b l, (List.length l <= n-2)%nat /\
  ∀ x, f x = a * exp x + b * exp (-x) + polynomial l x)).
Abort.
