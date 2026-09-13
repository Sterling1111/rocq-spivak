From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_6_a :
  ∀ a b m : ℝ, line_through (pair (a) (b)) (pair (1) (m)) = graph (λ x, m*(x-a)+b).
Abort.

Lemma lemma_4_6_b :
  ∀ a b c d : ℝ, a <> c -> line_through (pair (a) (b)) (pair (c-a) (d-b)) = graph (λ x, (d-b)/(c-a)*(x-a)+b).
Abort.

Lemma lemma_4_6_c :
  ∀ m b m' b' : ℝ, (parallel (graph (λ x, m*x+b)) (graph (λ x, m'*x+b')) <-> m=m' /\ b<>b').
Abort.

(* Equal slopes with equal intercepts give coincident lines. *)
