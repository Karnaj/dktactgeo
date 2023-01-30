Require Export euclidean__axioms.
Definition lemma__congruencesymmetric : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__axioms.Cong B C A D) -> (euclidean__axioms.Cong A D B C).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (euclidean__axioms.Cong B C B C) as H0.
- apply (@euclidean__axioms.cn__congruencereflexive (B) C).
- assert (* Cut *) (euclidean__axioms.Cong A D B C) as H1.
-- apply (@euclidean__axioms.cn__congruencetransitive (A) (D) (B) (C) (B) (C) (H) H0).
-- exact H1.
Qed.
