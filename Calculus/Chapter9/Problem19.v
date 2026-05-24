From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_19_a : ∀ f f' g h h' a,
  f a = g a = h a ->
  (∀ x, f x <= g x <= h x) ->
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ h = h' ->
  f' a = h' a ->
  differentiable_at g a /\ ∃ g', ⟦ der a ⟧ g = g' /\ g' a = f' a = h' a.
Proof.
  intros f f' g h h' a [H1 H2] H3 H4 H5 H6.

  assert (differentiable_at g a) as H7.
  {
    exists (f' a).
    unfold derivative_at in H5.
    apply limit_squeeze with (f1 := (λ h, (f (a + h) - f a) / h)) (f3 := (λ h0, (h (a + h0) - h a) / h0)) (a := -1) (b := 1); 
    try solve [solve_R].
    rewrite H6. auto.
    
  }
  
Abort.

Lemma lemma_9_19_b : ~ (forall f f' g h h' a,
  (forall x, f x <= g x /\ g x <= h x) ->
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ h = h' ->
  f' a = h' a ->
  exists g', ⟦ der a ⟧ g = g' /\ g' a = f' a).
Proof.
Abort.
