From Calculus.Chapter22 Require Import Prelude.

From Calculus.Chapter22 Require Import Problem3.

Definition interval_count (s : sequence) (n : ℕ) (a b : ℝ) : ℕ :=
  List.length (List.filter
    (λ j, if Rlt_dec a (s j) then
                if Rlt_dec (s j) b then true else false
              else false)
    (List.seq 0 n)).

Definition uniformly_distributed (s : sequence) : Prop :=
  (∀ n, s n ∈ [0, 1]) /\
  ∀ a b, 0 <= a < b <= 1 ->
    ⟦ lim ⟧ (λ n, interval_count s n a b / n) = b - a.

Definition step_function_on_unit (s : ℝ -> ℝ) : Prop :=
  ∃ P : partition 0 1,
    let l := points 0 1 P in
    ∀ i : ℕ, (S i < List.length l)%nat ->
      ∃ c, ∀ x, x ∈ (l.[i], l.[S i]) -> s x = c.

Lemma lemma_22_32_a : ∀ a b,
  0 <= a < b <= 1 ->
  ⟦ lim ⟧ (λ n, interval_count fraction_rows n a b / n) = b - a.
Abort.

Lemma lemma_22_32_b : ∀ a s,
  uniformly_distributed a -> step_function_on_unit s ->
  ⟦ lim ⟧ (λ n, (∑ 0 (n - 1) (λ k, s (a k))) / n) = ∫ 0 1 s.
Abort.

Lemma lemma_22_32_c : ∀ a f,
  uniformly_distributed a -> integrable_on 0 1 f ->
  ⟦ lim ⟧ (λ n, (∑ 0 (n - 1) (λ k, f (a k))) / n) = ∫ 0 1 f.
Abort.
