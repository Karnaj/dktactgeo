Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__axioms.
Require Export logic.
Require Export euclidean__defs.

Axiom NNPP: forall P, ~~P -> P.

Axiom Col__or__nCol : forall A B C,
  Col A B C \/ nCol A B C.

Axiom nCol__or__Col : forall A B C,
  nCol A B C \/ Col A B C.

Axiom eq__or__neq : forall A B: Point,
 A = B \/ (~(A = B)).

Axiom neq__or__eq : forall A B: Point,
 (~(A = B)) \/ A = B.

Axiom Col__nCol__False : forall A B C, nCol A B C -> Col A B C -> False.

Axiom nCol__notCol :
 forall A B C, ~ Col A B C -> nCol A B C.


Axiom not__nCol__Col : forall A B C,
  ~ nCol A B C -> Col A B C.

Axiom nCol__not__Col : forall A B C,
  nCol A B C -> ~ Col A B C.
