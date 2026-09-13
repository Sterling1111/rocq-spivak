From Calculus.Chapter4 Require Import Prelude.

(* Describe the polar graph's symmetry in each case. *)
Lemma lemma_4_app3_2_i :
  ∀ f, even f -> ∀ x y,
    (pair x y ∈ polar_graph f <-> pair x (-y) ∈ polar_graph f).
Abort.

Lemma lemma_4_app3_2_ii :
  ∀ f, odd f -> ∀ x y,
    (pair x y ∈ polar_graph f <-> pair (-x) y ∈ polar_graph f).
Abort.

Lemma lemma_4_app3_2_iii :
  ∀ f, periodic f π -> ∀ x y,
    (pair x y ∈ polar_graph f <-> pair (-x) (-y) ∈ polar_graph f).
Abort.
