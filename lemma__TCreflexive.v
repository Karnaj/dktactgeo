Require Export euclidean__axioms.
Require Export logic.
Definition lemma__TCreflexive : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> (euclidean__axioms.Cong__3 A B C A B C).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (euclidean__axioms.Cong A B A B) as H0.
- apply (@euclidean__axioms.cn__congruencereflexive (A) B).
- assert (* Cut *) (euclidean__axioms.Cong B C B C) as H1.
-- apply (@euclidean__axioms.cn__congruencereflexive (B) C).
-- assert (* Cut *) (euclidean__axioms.Cong A C A C) as H2.
--- apply (@euclidean__axioms.cn__congruencereflexive (A) C).
--- assert (* Cut *) (euclidean__axioms.Cong__3 A B C A B C) as H3.
---- split.
----- exact H0.
----- split.
------ exact H1.
------ exact H2.
---- exact H3.
Qed.
