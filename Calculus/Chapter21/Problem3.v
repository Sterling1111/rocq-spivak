From Calculus.Chapter21 Require Import Prelude.

Definition Z_poly (l : list R) : Prop :=
  Forall (λ c, ∃ z : Z, c = (z : ℝ)) l.

Lemma lemma_21_3_a : ∀ α (l : list R),
  ~ (∃ q : Q, α = (q : ℝ)) ->
  Z_poly l ->
  leading_coefficient l <> 0 ->
  polynomial l α = 0 ->
  (∀ l', Z_poly l' -> leading_coefficient l' <> 0 -> polynomial l' α = 0 -> (degree l' >= degree l)%nat) ->
  ∀ p q : Z, (q <> 0)%Z -> polynomial l (p / q) <> 0.
Abort.

Lemma lemma_21_3_b : ∀ α (l : list R),
  ~ (∃ q : Q, α = (q : ℝ)) ->
  Z_poly l ->
  leading_coefficient l <> 0 ->
  polynomial l α = 0 ->
  (∀ l', Z_poly l' -> leading_coefficient l' <> 0 -> polynomial l' α = 0 -> (degree l' >= degree l)%nat) ->
  ∀ p q : Z, (q > 0)%Z -> |polynomial l (p / q)| >= 1 / (q) ^ (degree l).
Abort.

Lemma lemma_21_3_c : ∀ α (l : list R),
  ~ (∃ q : Q, α = (q : ℝ)) ->
  Z_poly l ->
  leading_coefficient l <> 0 ->
  polynomial l α = 0 ->
  (∀ l', Z_poly l' -> leading_coefficient l' <> 0 -> polynomial l' α = 0 -> (degree l' >= degree l)%nat) ->
  ∃ c : R, c > 0 /\
    (∀ p q : Z, (q > 0)%Z -> |α - (p / q)| < 1 -> |α - (p / q)| > c / (q) ^ (degree l)).
Abort.
