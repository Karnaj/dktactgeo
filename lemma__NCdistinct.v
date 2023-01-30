Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__NCdistinct : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.nCol A B C) -> ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (~(A = B)) as H0.
- intro H0.
assert (* Cut *) (euclidean__axioms.Col A B C) as H1.
-- left.
exact H0.
-- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H1).
- assert (* Cut *) (euclidean__axioms.neq B A) as H1.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H0).
-- assert (* Cut *) (~(A = C)) as H2.
--- intro H2.
assert (* Cut *) (euclidean__axioms.Col A B C) as H3.
---- right.
left.
exact H2.
---- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H3).
--- assert (* Cut *) (euclidean__axioms.neq C A) as H3.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (C) H2).
---- assert (* Cut *) (~(B = C)) as H4.
----- intro H4.
assert (* Cut *) (euclidean__axioms.Col A B C) as H5.
------ right.
right.
left.
exact H4.
------ apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H5).
----- assert (* Cut *) (euclidean__axioms.neq C B) as H5.
------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H4).
------ split.
------- exact H0.
------- split.
-------- exact H4.
-------- split.
--------- exact H2.
--------- split.
---------- exact H1.
---------- split.
----------- exact H5.
----------- exact H3.
Qed.
