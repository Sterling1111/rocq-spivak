From Calculus.Chapter21 Require Import Prelude.

(* Problem 8: Local maximum/minimum points *)

Definition local_max (f : R -> R) (x : R) : Prop :=
  exists δ : R, δ > 0 /\ forall y, |y - x| < δ -> f y <= f x.

Definition local_min (f : R -> R) (x : R) : Prop :=
  exists δ : R, δ > 0 /\ forall y, |y - x| < δ -> f y >= f x.

(* (a) It can be shown that if every point is a local max for f, then f is constant (for continuous).
   Now suppose f is not continuous. Prove f takes on only a countable set of values. *)
Lemma lemma_21_8_a : forall f,
  (forall x, local_max f x) ->
  countable (image f).
Admitted.

(* (b) Deduce the previous result for continuous functions as a corollary. *)
Lemma lemma_21_8_b : forall f,
  continuous f ->
  (forall x, local_max f x) ->
  exists c, forall x, f x = c.
Admitted.

(* (c) Prove the analogous result for local minimum points similarly. *)
Lemma lemma_21_8_c : forall f,
  (forall x, local_min f x) ->
  countable (image f).
Admitted.

Lemma lemma_21_8_c' : forall f,
  continuous f ->
  (forall x, local_min f x) ->
  exists c, forall x, f x = c.
Admitted.
