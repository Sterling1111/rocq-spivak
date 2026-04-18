From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_26_a : forall a b L,
  b 0%nat = a -> (forall n, b (S n) = exp (b n * log a)) ->
  ⟦ lim ⟧ b = L ->
  exists y, a = exp ((1 / y) * log y) /\ 0 < a <= exp (1 / exp 1).
Abort.

Lemma lemma_22_26_bc : forall a b,
  b 0%nat = a -> (forall n, b (S n) = exp (b n * log a)) ->
  1 <= a <= exp (1 / exp 1) ->
  (increasing b) /\ (forall n, b n <= exp 1) /\
  (exists L, ⟦ lim ⟧ b = L /\ exp (-1) <= L <= exp 1) /\
  exp (- exp 1) <= a <= exp (1 / exp 1).
Abort.

Lemma lemma_22_26_d : forall a,
  exp (- exp 1) <= a < 1 ->
  decreasing_on (fun x => exp (x * log a) / log x) (oo 0 1).
Abort.

Lemma lemma_22_26_e : forall a b,
  0 < a < 1 ->
  (forall x, exp (x * log a) = x <-> x = b) ->
  a < b < 1.
Abort.

(* Parts f and g are quite specific limits properties about odd/even terms *)
Lemma lemma_22_26_fg : forall a b L1 L2 s,
  0 < a < 1 ->
  exp (b * log a) = b ->
  s 0%nat = a -> (forall n, s (S n) = exp (s n * log a)) ->
  ⟦ lim ⟧ (fun n => s (2 * n + 1)%nat) = L1 /\ exp (exp (L1 * log a) * log a) = L1 /\
  ⟦ lim ⟧ (fun n => s (2 * n + 2)%nat) = L2 /\ L2 = b /\
  ⟦ lim ⟧ s = b.
Abort.
