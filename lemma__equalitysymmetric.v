Require Export euclidean__axioms.
Require Export logic.
Definition lemma__equalitysymmetric : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point), (B = A) -> (A = B).
Proof.
intro A.
intro B.
intro H.
assert (* Cut *) (A = A) as H0.
- apply (@logic.eq__refl (Point) A).
- apply (@eq__ind euclidean__axioms.Point B (fun A0: euclidean__axioms.Point => (A0 = A0) -> (A0 = B))) with (y := A).
--intro H1.
assert (* Cut *) (B = B) as H2.
--- exact H1.
--- exact H2.

-- exact H.
-- exact H0.
Qed.
