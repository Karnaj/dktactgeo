Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglestransitive.
Definition lemma__equalanglesreflexive : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.nCol A B C) -> (euclidean__defs.CongA A B C A B C).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (euclidean__defs.CongA A B C C B A) as H0.
- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (B) (C) H).
- assert (* Cut *) (euclidean__axioms.nCol C B A) as H1.
-- apply (@euclidean__tactics.nCol__notCol (C) (B) (A)).
---apply (@euclidean__tactics.nCol__not__Col (C) (B) (A)).
----apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (B) (C) (C) (B) (A) H0).


-- assert (* Cut *) (euclidean__defs.CongA C B A A B C) as H2.
--- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (C) (B) (A) H1).
--- assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H3.
---- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (C) (C) (B) (A) (A) (B) (C) (H0) H2).
---- exact H3.
Qed.
