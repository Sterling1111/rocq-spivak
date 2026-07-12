From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_8_a : ∃ (f g : R -> R) (a L1 L2 : R),
  (∀ Lf, ¬ (⟦ lim a ⟧ f = Lf)) /\ (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)) /\
  ⟦ lim a ⟧ (f + g) = L1 /\
  ⟦ lim a ⟧ (f ⋅ g) = L2.
Proof.
  exists (fun x => |x| / x), (fun x => - |x| / x), 0, 0, (-1).
  repeat split.
  - intros Lf H1. admit.
  - intros Lg H1. admit.
  - apply limit_eq with (f1 := λ _, 0); [ | auto_limit ].
    exists 1; split; solve_R.
  - apply limit_eq with (f1 := λ _, -1); [ | auto_limit ].
    exists 1; split; solve_R.
Abort.

Lemma lemma_5_8_a_2 : ∃ (f g : R -> R) (a L : R),
  (∀ Lf, ¬ (⟦ lim a ⟧ f = Lf)) /\ (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)) /\
  ⟦ lim a ⟧ (fun x => f x * g x) = L.
Proof. Abort.

Lemma lemma_5_8_b : ∀ (f g : R -> R) (a L L_sum : R),
  ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ (fun x => f x + g x) = L_sum ->
  ∃ Lg, ⟦ lim a ⟧ g = Lg.
Proof. Abort.

Lemma lemma_5_8_c : ∀ (f g : R -> R) (a L : R),
  ⟦ lim a ⟧ f = L -> (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)) ->
  ∀ L_sum, ¬ (⟦ lim a ⟧ (fun x => f x + g x) = L_sum).
Proof. Abort.

Lemma lemma_5_8_d : ∃ (f g : R -> R) (a L L_prod : R),
  ⟦ lim a ⟧ f = L /\ ⟦ lim a ⟧ (fun x => f x * g x) = L_prod /\
  (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)).
Proof. Abort.
