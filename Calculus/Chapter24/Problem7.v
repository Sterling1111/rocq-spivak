From Calculus.Chapter24 Require Import Prelude.

Fixpoint choose_R (alpha : R) (n : nat) : R :=
  match n with
  | 0%nat => 1
  | S n' => choose_R alpha n' * (alpha - INR n') / INR (S n')
  end.

Lemma lemma_24_7_a : forall α x f,
  (forall y, Rabs y < 1 -> ∑ 0 ∞ (fun n => choose_R α n * y ^ n) = (f y)) ->
  Rabs x < 1 ->
  (1 + x) * ⟦ Der x ⟧ f = α * f x.
Abort.

Lemma lemma_24_7_b : forall α f,
  (forall x, Rabs x < 1 -> (1 + x) * ⟦ Der x ⟧ f = α * f x) ->
  exists c, forall x, Rabs x < 1 -> f x = c * Rpower (1 + x) α.
Abort.
