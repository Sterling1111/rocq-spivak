From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_17 : forall l,
  let f := λ x, polynomial l x in
  ∃ y, ∀ x, | f y | <= | f x |.
Proof.
  intros l f.
   
  
Abort.