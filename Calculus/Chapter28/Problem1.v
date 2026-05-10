From Calculus.Chapter28 Require Export Prelude.

Module Problem1.

  Inductive F : Type := zero | one | two.

  Definition F_add (x y : F) : F :=
    match x, y with
    | zero, y => y
    | x, zero => x
    | one, one => two
    | one, two => zero
    | two, one => zero
    | two, two => one
    end.

  Definition F_mult (x y : F) : F :=
    match x, y with
    | zero, _ => zero
    | _, zero => zero
    | one, y => y
    | x, one => x
    | two, two => one
    end.

  Definition F_opp (x : F) : F :=
    match x with
    | zero => zero
    | one => two
    | two => one
    end.

  Definition F_inv (x : F) : F :=
    match x with
    | zero => zero
    | one => one
    | two => two
    end.

  Definition F_sub (x y : F) : F := F_add x (F_opp y).
  Definition F_div (x y : F) : F := F_mult x (F_inv y).

  Declare Scope F_scope.

  Notation "0" := zero : F_scope.
  Notation "1" := one : F_scope.
  Notation "2" := two : F_scope.
  Infix "+" := F_add : F_scope.
  Infix "*" := F_mult : F_scope.
  Notation "- x" := (F_opp x) : F_scope.
  Infix "-" := F_sub : F_scope.
  Notation "/ x" := (F_inv x) : F_scope.
  Infix "/" := F_div : F_scope.

  Open Scope F_scope.

  Instance Field_F : Field F.
  Proof.
    apply (Build_Field F F_add F_mult 0 1 F_opp F_inv); intros;
    try first [ destruct a, b, c | destruct a, b | destruct a ]; try reflexivity.
    - intros H1. discriminate H1.
    - contradiction.
  Defined.

  Lemma not_ordered_F : OrderedField F -> False.
  Proof.
    intros [P H1 H2 H3]; simpl in *.
    specialize (H1 1) as H4.
    unfold one_and_only_one_3 in H4.
    destruct H4 as [[H5 _] | [[H5 [H6 H7]] | [H5 [H6 H7]]]].
    - discriminate H5.
    - specialize (H2 1 1 H6 H6). replace (1 + 1) with 2 in H2 by reflexivity.
      replace (- (1)) with 2 in H7 by reflexivity.
      apply H7; auto.
    - assert (H8 : (- (1) + - (1)) ∈ P) by (apply H2; assumption).
      replace (- (1) + - (1)) with 1 in H8 by reflexivity.
      apply H6, H8.
  Qed.

End Problem1.