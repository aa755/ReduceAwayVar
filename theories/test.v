Require Import ReduceAwayVar.

Goal forall A, A -> A.
Proof.
  myintro A a.
  Show Proof.
  exact a.
Defined.

Myprint Unnamed_thm.