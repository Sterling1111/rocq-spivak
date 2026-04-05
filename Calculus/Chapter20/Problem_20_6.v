From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_6 : forall f,
  (forall x, x <> 0 -> f x = sin x / x) ->
  f 0 = 1 ->
  forall n, ⟦ Der ^ n 0 ⟧ f =
    if Nat.Even_or_Odd n then
      (fun ev => (-1)^(n/2) / INR (n + 1)) (match Nat.Even_or_Odd n with | or_introl ev => ev | or_intror _ => False_ind _ (ltac:(admit)) end) (* Just a dummy expression structure *)
    else 0.
Admitted.
