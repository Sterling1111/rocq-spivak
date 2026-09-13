From Calculus.Chapter23 Require Import Prelude.

Definition digits_exclude (d n : nat) : bool :=
  forallb (λ k,
    if (10^k <=? n)%nat then negb ((n / 10^k) mod 10 =? d)%nat else true)
    (seq 0 (S n)).

Definition does_not_have_all_digits (n : nat) : bool :=
  existsb (λ d, digits_exclude d n) (seq 0 10).

Lemma problem_23_11_a :
  series_converges (λ n, if digits_exclude 9 (S n) then 1 / (S n)%nat else 0).
Abort.

Lemma problem_23_11_b :
  series_converges (λ n, if does_not_have_all_digits (S n) then 1 / (S n)%nat else 0).
Abort.
