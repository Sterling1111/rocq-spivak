From Calculus.Chapter18 Require Import Prelude.

(* One dollar, annual percentage rate a, compounded k times per year. *)
Definition compounded_amount (a : R) (k : nat) :=
  (1 + a / (100 * k)) ^ k.

Lemma lemma_18_19 : ∀ a, 0 <= a ->
  is_lub (λ y, ∃ k : nat, (0 < k)%nat /\ y = compounded_amount a k)
    (exp (a / 100)).
Abort.
