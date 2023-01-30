Require Export euclidean__axioms.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export logic.
Definition lemma__doublereverse : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__axioms.Cong A B C D) -> ((euclidean__axioms.Cong D C B A) /\ (euclidean__axioms.Cong B A D C)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (euclidean__axioms.Cong C D D C) as H0.
- apply (@euclidean__axioms.cn__equalityreverse (C) D).
- assert (* Cut *) (euclidean__axioms.Cong A B D C) as H1.
-- apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (B) (C) (D) (D) (C) (H) H0).
-- assert (* Cut *) (euclidean__axioms.Cong B A A B) as H2.
--- apply (@euclidean__axioms.cn__equalityreverse (B) A).
--- assert (* Cut *) (euclidean__axioms.Cong B A D C) as H3.
---- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (A) (A) (B) (D) (C) (H2) H1).
---- assert (* Cut *) (euclidean__axioms.Cong D C B A) as H4.
----- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (D) (B) (A) (C) H3).
----- split.
------ exact H4.
------ exact H3.
Qed.
