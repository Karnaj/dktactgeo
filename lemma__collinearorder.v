Require Export euclidean__axioms.
Require Export lemma__collinear1.
Require Export lemma__collinear2.
Require Export logic.
Definition lemma__collinearorder : forall A B C, (euclidean__axioms.Col A B C) -> ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (euclidean__axioms.Col B C A) as H0.
- apply (@lemma__collinear2.lemma__collinear2 A B C H).
- assert (* Cut *) (euclidean__axioms.Col C A B) as H1.
-- apply (@lemma__collinear2.lemma__collinear2 B C A H0).
-- assert (* Cut *) (euclidean__axioms.Col B A C) as H2.
--- apply (@lemma__collinear1.lemma__collinear1 A B C H).
--- assert (* Cut *) (euclidean__axioms.Col A C B) as H3.
---- apply (@lemma__collinear2.lemma__collinear2 B A C H2).
---- assert (* Cut *) (euclidean__axioms.Col C B A) as H4.
----- apply (@lemma__collinear2.lemma__collinear2 A C B H3).
----- split.
------ exact H2.
------ split.
------- exact H0.
------- split.
-------- exact H1.
-------- split.
--------- exact H3.
--------- exact H4.
Qed.
