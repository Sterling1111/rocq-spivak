Set Warnings "-all".

Declare Scope bigQ_scope.

From Interval Require Export Tactic Plot.
From Stdlib Require Export 
  (* Real numbers *)
  Reals 
  Lra 
  
  (* Arithmetic *)
  ZArith
  QArith
  Arith.Arith
  Arith.PeanoNat
  Arith.Compare_dec
  Lia
  
  (* Logic *)
  Logic.Classical
  Logic.ClassicalFacts
  Logic.Classical_Pred_Type
  Logic.Classical_Prop
  Logic.FunctionalExtensionality
  Logic.PropExtensionality
  Logic.ClassicalChoice
  Logic.ClassicalEpsilon
  Logic.ChoiceFacts
  
  (* Utilities *)
  String
  DecimalString
  Program
  Orders
  Sorting
  Permutation
  Utf8

  (* Sets and Lists *)
  Sets.Ensembles
  Sets.Classical_sets
  Sets.Powerset
  Sets.Finite_sets
  Sets.Image
  Lists.List
  RList
  FMapPositive.
  

Export ListNotations.

Open Scope R_scope.
Open Scope nat_scope.

Global Set Bullet Behavior "Strict Subproofs".