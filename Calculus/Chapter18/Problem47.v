From Calculus.Chapter18 Require Import Prelude.

Definition grows_faster f g : Prop :=
  ⟦ lim ∞ ⟧ (f / g) = ∞.
  
Definition grows_same f g : Prop :=
  exists L, L <> 0 /\ ⟦ lim ∞ ⟧ (f / g) = L.

Fixpoint chained_grows_faster (l : list (ℝ -> ℝ)) : Prop :=
  match l with
  | nil => True
  | f :: nil => True
  | f :: (g :: _) as rest => grows_faster g f /\ chained_grows_faster rest
  end.

Module GrowthNotations.
  Notation "f ≫ g" := (grows_faster f g) (at level 70, no associativity) : function_scope.
  Notation "f ∼ g" := (grows_same f g) (at level 70, no associativity) : function_scope.
  Notation "[[ x ≪ .. ≪ y ]]" := (chained_grows_faster (cons x .. (cons y nil) ..)) (at level 0, x at level 69, y at level 69) : function_scope.
End GrowthNotations.

Section section_18_47.

  Import GrowthNotations.
  
  Variables f g : ℝ -> ℝ.

  Hypothesis H1 : continuous f.
  Hypothesis H2 : continuous g.

  Hypothesis H3 : ⟦ lim ∞ ⟧ f = ∞.
  Hypothesis H4 : ⟦ lim ∞ ⟧ g = ∞.

  Lemma lemma_18_47_a : (f = λ x, x * (2 + sin x)) -> (g = λ x, x) -> ~ (f ≫ g \/ g ≫ f \/ f ∼ g).
  Proof.
    
  Abort.

  Lemma lemma_18_47_b : f ≫ g -> f + g ∼ f.
  Proof.

  Abort.

  Lemma lemma_18_47_c : 
    (∃ c N, ∀ x, x > N -> (log (f x)) / (log (g x)) >= c > 1) -> f ≫ g.
  Proof.

  Abort.

  Lemma lemma_18_47_d : ∀ F G,
    f ≫ g -> 
    (∀ x, F x = ∫ 0 x f) ->
    (∀ x, G x = ∫ 0 x g) ->
    F ≫ G.
  Proof.

  Abort.

  Section section_18_47_e_i.

    Definition f1 := λ x, log (4 * x).
    Definition f2 := λ x, x + exp (-5 * x).
    Definition f3 := λ x, x ^ 3.
    Definition f4 := λ x, x ^ 3 * log x.
    Definition f5 := λ x, exp x.
    Definition f6 := λ x, (log x) ^^ x.
    Definition f7 := λ x, x ^^ x.
    Definition f8 := λ x, x ^ 3 + log (x ^ 3).

    Lemma lemma_18_47_e_i :
      [[ f1 ≪ f2 ≪ f3 ≪ f4 ≪ f5 ≪ f6 ≪ f7 ]] /\ f3 ∼ f8.
    Proof. 
    
    Admitted.

  End section_18_47_e_i.

  Section section_18_47_e_ii.
    
    Definition g1 := λ x, log (x ^^ x).
    Definition g2 := λ x, x * (log x) ^ 2.
    Definition g3 := λ x, x ^^ log x.
    Definition g4 := λ x, exp (5 * x).
    Definition g5 := λ x, (log x) ^^ x.
    Definition g6 := λ x, x ^^ x.
    Definition g7 := λ x, exp (x ^ 2).

    Lemma lemma_18_47_e_ii :
      [[ g1 ≪ g2 ≪ g3 ≪ g4 ≪ g5 ≪ g6 ≪ g7 ]].
    Proof. 

    Admitted.
    
  End section_18_47_e_ii.

  Section section_18_47_e_iii.

    Definition h1 := λ x, x ^^ exp 1.
    Definition h2 := λ x, exp (x / 2).
    Definition h3 := λ x, 2 ^^ x.
    Definition h4 := λ x, exp x.
    Definition h5 := λ x, (log x) ^^ (2 * x).
    Definition h6 := λ x, x ^^ x.
    Definition h7 := λ x, exp (x ^ 2).

    Lemma lemma_18_47_e_iii :
      [[ h1 ≪ h2 ≪ h3 ≪ h4 ≪ h5 ≪ h6 ≪ h7 ]].
    Proof.

    Admitted.

  End section_18_47_e_iii.

End section_18_47.