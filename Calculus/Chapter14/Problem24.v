From Calculus.Chapter14 Require Import Prelude.

(* Problem 24: Schwarzian derivative *)

(* (a) If Schwarzian derivative of f is 0, show (f'')^2 / (f')^3 is constant. *)
Lemma lemma_14_24_a : forall f f' f'' f''',
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  ⟦ der ⟧ f'' = f''' ->
  (forall x, f' x <> 0) ->
  (forall x, f''' x / f' x - 3/2 * (f'' x / f' x)^2 = 0) ->
  exists c, forall x, (f'' x)^2 / (f' x)^3 = c.
Abort.

(* (b) Show f is of the form (ax + b) / (cx + d). *)
Lemma lemma_14_24_b : forall f f' f'' f''',
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  ⟦ der ⟧ f'' = f''' ->
  (forall x, f' x <> 0) ->
  (forall x, f''' x / f' x - 3/2 * (f'' x / f' x)^2 = 0) ->
  exists a b c d, forall x, c * x + d <> 0 -> f x = (a * x + b) / (c * x + d).
Abort.
