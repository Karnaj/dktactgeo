Require Export euclidean__axioms.
Require Export lemma__equalitysymmetric.
Definition lemma__inequalitysymmetric : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point), (euclidean__axioms.neq A B) -> (euclidean__axioms.neq B A).
Proof.
intro A.
intro B.
intro H.
assert (* Cut *) (~(B = A)) as H0.
- intro H0.
assert (* Cut *) (A = B) as H1.
-- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (A) (B) H0).
-- apply (@H H1).
- exact H0.
Qed.
