Declare ML Module "myplug".

Require Import Arith.

Myprint plus.

Goal forall A : Prop, A -> A.
Proof.
  myintro A x.
  exact x.
Qed.