Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__collinearorder.
Require Export logic.
Definition lemma__NCorder : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.nCol A B C) -> ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (~(euclidean__axioms.Col B A C)) as H0.
- intro H0.
assert (* Cut *) (euclidean__axioms.Col A B C) as H1.
-- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H1.
--- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H0).
--- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H2.
---- exact H1.
---- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H4.
----- exact H3.
----- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
exact H2.
-- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H1).
- assert (* Cut *) (~(euclidean__axioms.Col B C A)) as H1.
-- intro H1.
assert (* Cut *) (euclidean__axioms.Col A B C) as H2.
--- assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H2.
---- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (A) H1).
---- assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H3.
----- exact H2.
----- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
exact H7.
--- apply (@H0).
----apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
-----intro H3.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H2).


-- assert (* Cut *) (~(euclidean__axioms.Col C A B)) as H2.
--- intro H2.
assert (* Cut *) (euclidean__axioms.Col A B C) as H3.
---- assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H3.
----- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (B) H2).
----- assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H4.
------ exact H3.
------ destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
exact H6.
---- apply (@H0).
-----apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
------intro H4.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H3).


--- assert (* Cut *) (~(euclidean__axioms.Col A C B)) as H3.
---- intro H3.
assert (* Cut *) (euclidean__axioms.Col A B C) as H4.
----- assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H4.
------ apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (B) H3).
------ assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H5.
------- exact H4.
------- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)))) as H7.
-------- exact H6.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
exact H11.
----- apply (@H0).
------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
-------intro H5.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H4).


---- assert (* Cut *) (~(euclidean__axioms.Col C B A)) as H4.
----- intro H4.
assert (* Cut *) (euclidean__axioms.Col A B C) as H5.
------ assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H5.
------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (A) H4).
------- assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H6.
-------- exact H5.
-------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
exact H13.
------ apply (@H0).
-------apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
--------intro H6.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H5).


----- split.
------ apply (@euclidean__tactics.nCol__notCol (B) (A) (C) H0).
------ split.
------- apply (@euclidean__tactics.nCol__notCol (B) (C) (A) H1).
------- split.
-------- apply (@euclidean__tactics.nCol__notCol (C) (A) (B) H2).
-------- split.
--------- apply (@euclidean__tactics.nCol__notCol (A) (C) (B) H3).
--------- apply (@euclidean__tactics.nCol__notCol (C) (B) (A) H4).
Qed.
