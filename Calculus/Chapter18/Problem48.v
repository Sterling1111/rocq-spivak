From Calculus.Chapter18 Require Import Prelude.

From Calculus.Chapter18 Require Import Problem47.
Import Problem47.GrowthNotations.

(* A countable sequence, not merely a finite list. The growth hypotheses
   are those of Problem 47, under which f/g -> infinity defines growth. *)
Lemma lemma_18_48 : ∀ g : nat -> R -> R,
  (∀ n, continuous (g n)) ->
  (∀ n, limit_pinf_to_pinf (g n)) ->
  ∃ f, continuous f /\ (limit_pinf_to_pinf f) /\ ∀ n, f ≫ g n.
Abort.

(* For arbitrary continuous g_n, including zeros and negative functions,
   use magnitude domination instead of dividing by a possibly zero g_n. *)
Lemma lemma_18_48_general : ∀ g : nat -> R -> R,
  (∀ n, continuous (g n)) ->
  ∃ f, continuous f /\ (∀ x, f x > 0) /\
  ∀ n, limit_pinf_to_pinf (λ x, f x / (1 + |g n x|)).
Abort.
