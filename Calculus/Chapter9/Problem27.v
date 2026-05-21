From Calculus.Chapter9 Require Import Prelude.

Section section_9_27.

Variable n : ℕ.

Definition S_n x := x^n.

Lemma lemma_9_27 : forall k,
  (0 <= k <= n)%nat -> ⟦ der ^ k ⟧ (S_n) = (fun x => k! * (n ∁ k) * x ^ (n - k)).
Proof.
  intros k H1. induction k as [| k IH].
  - simpl. rewrite n_choose_0. extensionality x. rewrite Nat.sub_0_r. unfold S_n. lra.
  - exists (fun x : R => k! * n ∁ k * x ^ (n - k)).
    split.
    + apply IH; lia.
    + apply derivative_ext with (f1' := fun x => (k! * n ∁ k) * ((n - k) * x ^ (n - k - 1))).
      {
        intros x. admit.
      }
      auto_diff.
Abort.

End section_9_27.