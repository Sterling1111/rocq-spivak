From Calculus.Chapter21 Require Import Prelude.

Lemma lemma_21_5_a : ∀ U (A B : Ensemble U),
  countable A -> countable B -> countable (A ⋃ B).
Abort.

Lemma lemma_21_5_b :
  countable (λ x : R, ∃ q : Q, x = q /\ x > 0).
Abort.

Lemma lemma_21_5_c :
  countable (Full_set (Z * Z)).
Abort.

Lemma lemma_21_5_d : ∀ U (F : nat -> Ensemble U),
  (∀ n, countable (F n)) ->
  countable (λ x, ∃ n, x ∈ F n).
Abort.

Lemma lemma_21_5_e :
  countable (Full_set (Z * Z * Z)).
Abort.

Lemma lemma_21_5_f : ∀ n : nat,
  countable (λ l : list Z, length l = n).
Abort.

Definition roots_of_degree (n : nat) : Ensemble R :=
  λ x, ∃ l : list R,
    degree l = n /\
    Forall (λ c, ∃ z : Z, c = (z : ℝ)) l /\
    leading_coefficient l <> 0 /\
    polynomial l x = 0.

Lemma lemma_21_5_g : ∀ n, countable (roots_of_degree n).
Abort.

Lemma lemma_21_5_h : countable (λ x, algebraic x).
Abort.
