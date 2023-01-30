Require Export euclidean__axioms.
Require Export lemma__congruencesymmetric.
Definition lemma__congruencetransitive : forall A B C D E F, (euclidean__axioms.Cong A B C D) -> ((euclidean__axioms.Cong C D E F) -> (euclidean__axioms.Cong A B E F)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.Cong C D A B) as H1.
- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric C A B D H).
- assert (* Cut *) (euclidean__axioms.Cong A B E F) as H2.
-- apply (@euclidean__axioms.cn__congruencetransitive A B E F C D H1 H0).
-- exact H2.
Qed.
