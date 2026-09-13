From Calculus.Chapter13 Require Import Prelude.

From Lib Require Import Rational.

Definition f_13_7_i (x : R) := if Rlt_dec x 1 then x else x - 2.

Lemma lemma_13_7_i : integrable_on 0 2 f_13_7_i /\ ∫ 0 2 f_13_7_i = 0.
Abort.

Lemma lemma_13_7_ii : ~ ∃ f : R -> R,
  (∀ x, 0 <= x <= 1 -> f x = x) /\
  (∀ x, 1 <= x <= 2 -> f x = x - 2).
Abort.

Definition f_13_7_iii (x : R) := x + (Int_part x)%Z.
Lemma lemma_13_7_iii : integrable_on 0 2 f_13_7_iii /\ ∫ 0 2 f_13_7_iii = 3.
Abort.

Definition f_13_7_iv (x : R) :=
  if excluded_middle_informative (rational x) then x + (Int_part x)%Z else 0.
Lemma lemma_13_7_iv : ~ integrable_on 0 2 f_13_7_iv.
Abort.

Definition f_13_7_v (x : R) :=
  if excluded_middle_informative
    (∃ a b, rational a /\ rational b /\ x = a + b * √2) then 1 else 0.
Lemma lemma_13_7_v : ~ integrable_on 0 2 f_13_7_v.
Abort.

Definition f_13_7_vi (x : R) :=
  if Rlt_dec 0 x then
    if Rle_dec x 1 then 1 / (Int_part (1 / x))%Z else 0
  else 0.
Lemma lemma_13_7_vi : integrable_on 0 2 f_13_7_vi.
Abort.

Lemma lemma_13_7_vii : ∀ (f : R -> R) (c : nat -> R),
  f 0 = 0 ->
  (∀ n, / 2^n < c n < 2 / 2^n) ->
  (∀ n x, / 2^n <= x <= c n ->
    f x = (x - / 2^n) / (c n - / 2^n)) ->
  (∀ n x, c n <= x <= 2 / 2^n ->
    f x = (2 / 2^n - x) / (2 / 2^n - c n)) ->
  integrable_on 0 2 f /\ ∫ 0 2 f = 1.
Abort.
