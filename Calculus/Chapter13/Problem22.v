From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_22 : ∀ f f_inv a b,
  f 0 = 0 ->
  continuous_on f [0, Rmax a (f_inv b)] ->
  increasing_on f [0, Rmax a (f_inv b)] ->
  inverse_on f f_inv [0, Rmax a (f_inv b)] [0, Rmax (f a) b] ->
  a > 0 -> b > 0 ->
  a * b <= ∫ 0 a f + ∫ 0 b f_inv /\ (a * b = ∫ 0 a f + ∫ 0 b f_inv <-> b = f a).
Abort.
