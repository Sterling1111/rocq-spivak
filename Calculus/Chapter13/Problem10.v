From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_10 : ∀ f g a b (P : partition a b) i m' m'' m,
  bounded_on f [a, b] -> bounded_on g [a, b] ->
  let t := points a b P in
  (i < List.length t - 1)%nat ->
  is_glb (λ y, ∃ x, x ∈ [t.[i], t.[i+1]] /\ y = f x) m' ->
  is_glb (λ y, ∃ x, x ∈ [t.[i], t.[i+1]] /\ y = g x) m'' ->
  is_glb (λ y, ∃ x, x ∈ [t.[i], t.[i+1]] /\ y = f x + g x) m ->
  is_glb (λ y, ∃ x1 x2,
    x1 ∈ [t.[i], t.[i+1]] /\ x2 ∈ [t.[i], t.[i+1]] /\
    y = f x1 + g x2) (m' + m'') /\ m' + m'' <= m.
Proof.
  intros f g a b P i m' m'' m H1 H2 t H3 H4 H5 H6.
  pose proof is_glb_sum _ _ m' m'' H4 H5 as H7.
  assert (H8 : (λ y, exists x1 x2,
    (∃ x, x ∈ [t.[i], t.[i+1]] /\ x1 = f x) /\
    (∃ x, x ∈ [t.[i], t.[i+1]] /\ x2 = g x) /\ y = x1 + x2) =
    (λ y, exists x1 x2, x1 ∈ [t.[i], t.[i+1]] /\
      x2 ∈ [t.[i], t.[i+1]] /\ y = f x1 + g x2)).
  {
    extensionality y. apply propositional_extensionality. split.
    - intros [u [v [[x [H8 H9]] [[z [H10 H11]] H12]]]].
      exists x, z. subst; auto.
    - intros [x [z [H8 [H9 H10]]]].
      exists (f x), (g z). repeat split; auto; [exists x | exists z]; auto.
  }
  cbn beta in H7. fold t in H7. rewrite H8 in H7. split; auto.
  apply Rge_le, (proj2 H6). intros y [x [H9 H10]].
  apply (proj1 H7). exists x, x. auto.
Qed.
