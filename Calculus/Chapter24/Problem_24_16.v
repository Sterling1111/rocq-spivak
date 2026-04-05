From Calculus.Chapter24 Require Import Prelude.

Fixpoint fibonacci (n : nat) : R :=
  match n with
  | 0%nat => 0
  | S n' => match n' with
            | 0%nat => 1
            | S n'' => fibonacci n' + fibonacci n''
            end
  end.

Lemma lemma_24_16_a : forall n, (n >= 1)%nat ->
  fibonacci (n + 1) / fibonacci n <= 2.
Admitted.

Lemma lemma_24_16_b : forall x,
  Rabs x < 1/2 -> series_converges (fun n => if Nat.eq_dec n 0 then 0 else fibonacci n * x^(n-1)).
Admitted.

Lemma lemma_24_16_c : forall x,
  Rabs x < 1/2 -> ∑ 0 ∞ (fun n => fibonacci (n+1) * x^n) = -1 / (x^2 + x - 1).
Admitted.

Lemma lemma_24_16_e : forall n, (n >= 1)%nat ->
  fibonacci n = (((1 + √5)/2)^n - ((1 - √5)/2)^n) / √5.
Admitted.
