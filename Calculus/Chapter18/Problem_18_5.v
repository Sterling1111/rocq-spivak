From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_5_i : ⟦ lim 0 ⟧ (fun x => (exp x - 1 - x - x^2 / 2) / x^2) = 0.
Proof.
  apply lhopital_0_0_strong with (f' := λ x, (exp x)-1-x) (g' := λ x, 2*x);
  try solve [ auto_limit] ; try solve [ auto_diff ];
  try (exists 1; split; try lra; auto_diff).
  apply lhopital_0_0_strong with (f' := fun x => exp x - 1) (g' := fun x => 2);
  try solve [ auto_limit] ; try solve [ auto_diff ];
  try (exists 1; split; try lra; auto_diff).
Qed.

Lemma lemma_18_5_i : ⟦ lim 0 ⟧ (fun x => (exp x - 1 - x - x^2 / 2) / x^2) = 0.
Proof.
  apply lhopital.
  apply lhopital_nth with (n := 2%nat).
  - lia.
  - intros k H1. destruct k.
    + exists 1. split; [lra |]. intros x H2 H3. rewrite nth_derive_1. intros H4.

      replace 0 with ((fun x => x^2) 0) in H4 by lra.
       apply derive_at_spec in H4. admit.
    + exists 1. split; [lra |]. intros x H2 H3. admit.
  - intros k H1. admit.
  - intros k H1. admit.
  - intros k H1. destruct k; admit.
  - intros k H1. destruct k; admit.
  - admit.
Admitted.