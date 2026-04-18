From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_7 : forall f g a n (a_seq b_seq c_seq : nat -> R),
  (forall i, a_seq i = ⟦ Der ^ i a ⟧ f / INR (fact i)) ->
  (forall i, b_seq i = ⟦ Der ^ i a ⟧ g / INR (fact i)) ->
  (forall i, c_seq i = ⟦ Der ^ i a ⟧ (f ⋅ g) / INR (fact i)) ->
  forall k, (k <= n)%nat ->
  c_seq k = sum_f_R0 (fun j => a_seq j * b_seq (k - j)%nat) k.
Abort.
