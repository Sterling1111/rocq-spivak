(*
From Lib Require Import Tactics Limit Derivative Continuity.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import all_order ssralg ssrnum boolp classical_sets.
From mathcomp Require Import topology reals functions derive Rstruct Rstruct_topology.

Import LimitNotations DerivativeNotations.

Import Order.TTheory GRing.Theory Num.Theory.

Open Scope classical_set_scope.
Open Scope ring_scope.

From Stdlib Require Import Lra.

Lemma mc_limit_compat : forall f a L,
  ⟦ lim a ⟧ f = L <-> (f @ within [set~ a] (nbhs a) --> L).
Proof.
Abort.

Lemma mc_right_limit_compat : forall f a L,
  ⟦ lim a⁺ ⟧ f = L <-> (f @ within [set x | a < x] (nbhs a) --> L).
Proof.
Abort.

Lemma mc_left_limit_compat : forall f a L,
  ⟦ lim a⁻ ⟧ f = L <-> (f @ within [set x | x < a] (nbhs a) --> L).
Proof.
Abort.
*)