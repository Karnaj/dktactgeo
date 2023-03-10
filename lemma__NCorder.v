Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__collinearorder.
Require Export logic.
Definition lemma__NCorder : forall A B C, (euclidean__axioms.nCol A B C) -> ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (~(euclidean__axioms.Col B A C)) as H0.
- intro H0.
assert (* Cut *) (euclidean__axioms.Col A B C) as H1.
-- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H1.
--- apply (@lemma__collinearorder.lemma__collinearorder B A C H0).
--- destruct H1 as [H2 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
exact H2.
-- apply (@euclidean__tactics.Col__nCol__False A B C H H1).
- assert (* Cut *) (~(euclidean__axioms.Col B C A)) as H1.
-- intro H1.
assert (* Cut *) (euclidean__axioms.Col A B C) as H2.
--- assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H2.
---- apply (@lemma__collinearorder.lemma__collinearorder B C A H1).
---- destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
exact H7.
--- apply (@H0).
----apply (@euclidean__tactics.not__nCol__Col B A C).
-----intro H3.
apply (@euclidean__tactics.Col__nCol__False A B C H H2).


-- assert (* Cut *) (~(euclidean__axioms.Col C A B)) as H2.
--- intro H2.
assert (* Cut *) (euclidean__axioms.Col A B C) as H3.
---- assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H3.
----- apply (@lemma__collinearorder.lemma__collinearorder C A B H2).
----- destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H6.
---- apply (@H0).
-----apply (@euclidean__tactics.not__nCol__Col B A C).
------intro H4.
apply (@euclidean__tactics.Col__nCol__False A B C H H3).


--- assert (* Cut *) (~(euclidean__axioms.Col A C B)) as H3.
---- intro H3.
assert (* Cut *) (euclidean__axioms.Col A B C) as H4.
----- assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H4.
------ apply (@lemma__collinearorder.lemma__collinearorder A C B H3).
------ destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H11.
----- apply (@H0).
------apply (@euclidean__tactics.not__nCol__Col B A C).
-------intro H5.
apply (@euclidean__tactics.Col__nCol__False A B C H H4).


---- assert (* Cut *) (~(euclidean__axioms.Col C B A)) as H4.
----- intro H4.
assert (* Cut *) (euclidean__axioms.Col A B C) as H5.
------ assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H5.
------- apply (@lemma__collinearorder.lemma__collinearorder C B A H4).
------- destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
exact H13.
------ apply (@H0).
-------apply (@euclidean__tactics.not__nCol__Col B A C).
--------intro H6.
apply (@euclidean__tactics.Col__nCol__False A B C H H5).


----- split.
------ apply (@euclidean__tactics.nCol__notCol B A C H0).
------ split.
------- apply (@euclidean__tactics.nCol__notCol B C A H1).
------- split.
-------- apply (@euclidean__tactics.nCol__notCol C A B H2).
-------- split.
--------- apply (@euclidean__tactics.nCol__notCol A C B H3).
--------- apply (@euclidean__tactics.nCol__notCol C B A H4).
Qed.
