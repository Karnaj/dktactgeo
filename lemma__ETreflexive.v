Require Export euclidean__axioms.
Require Export lemma__TCreflexive.
Definition lemma__ETreflexive : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> (euclidean__axioms.ET A B C A B C).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H0.
- exact H.
- assert (* Cut *) (euclidean__axioms.Cong__3 A B C A B C) as H1.
-- apply (@lemma__TCreflexive.lemma__TCreflexive (A) (B) (C) H0).
-- assert (* Cut *) (euclidean__axioms.ET A B C A B C) as H2.
--- apply (@euclidean__axioms.axiom__congruentequal (A) (B) (C) (A) (B) (C) H1).
--- exact H2.
Qed.
