From Calculus.Chapter1 Require Import Prelude.

Module module_1_25.

  Inductive number : Type :=
    | zero
    | one.

  Definition num_plus (a b : number) : number :=
    match a, b with
    | zero, zero => zero
    | one, one => zero
    | _, _ => one
    end.

  Definition num_mult (a b : number) : number :=
    match a, b with
    | one, one => one
    | _, _ => zero
    end.

  Local Notation "x + y" := (num_plus x y).
  Local Notation "x * y" := (num_mult x y).

  Lemma lemma_1_25_P1 : ∀ a b c : number,
    a + (b + c) = (a + b) + c.
  Proof.
    destruct a, b, c; reflexivity.
  Qed.

  Lemma lemma_1_25_P2 : ∀ a : number,
    ∃ i : number, a + i = a.
  Proof.
    intros a. exists zero. destruct a; reflexivity.
  Qed.

  Lemma lemma_1_25_P3 : ∀ a : number,
    ∃ i : number, a + i = zero.
  Proof.
    intros a. destruct a.
    - exists zero. reflexivity.
    - exists one. reflexivity.
  Qed.

  Lemma lemma_1_25_P4 : ∀ a b : number,
    a + b = b + a.
  Proof.
    intros a b. destruct a, b; reflexivity.
  Qed.

  Lemma lemma_1_25_P6 : ∀ a : number,
    ∃ i : number, a * i = a.
  Proof.
    intros a. exists one. destruct a; reflexivity.
  Qed.

  Lemma lemma_1_25_P7 : ∀ a : number,
    ∃ i : number, a * i = zero.
  Proof.
    intros a. destruct a.
    - exists one. reflexivity.
    - exists zero. reflexivity.
  Qed.

  Lemma lemma_1_25_P8 : ∀ a b : number,
    a * b = b * a.
  Proof.
    intros a b. destruct a, b; reflexivity.
  Qed.

  Lemma lemma_1_25_P9 : ∀ a b c : number,
    a * (b + c) = a * b + a * c.
  Proof.
    destruct a, b, c; reflexivity.
  Qed.

End module_1_25.