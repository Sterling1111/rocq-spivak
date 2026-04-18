From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_8 : forall x,
  (exists k : Z, x = IZR k) -> 
  (exists L1, ⟦ lim ⟧ (fun n => cos (INR n * π * x)) = L1) \/ True.
Abort.
