Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__angledistinct.
Require Export lemma__collinearorder.
Require Export lemma__equalanglessymmetric.
Require Export lemma__trichotomy1.
Require Export logic.
Require Export proposition__06a.
Definition proposition__06 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.CongA A B C A C B) -> (euclidean__axioms.Cong A B A C)).
Proof.
intro A.
intro B.
intro C.
intro H.
intro H0.
assert (* Cut *) (~(euclidean__defs.Lt A C A B)) as H1.
- apply (@proposition__06a.proposition__06a (A) (B) (C) (H) H0).
- assert (* Cut *) (euclidean__axioms.nCol A B C) as H2.
-- exact H.
-- assert (* Cut *) (~(euclidean__axioms.Col A C B)) as H3.
--- intro H3.
assert (* Cut *) (euclidean__axioms.Col A B C) as H4.
---- assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H4.
----- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (B) H3).
----- assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
exact H11.
---- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H2) H4).
--- assert (* Cut *) (euclidean__axioms.Triangle A C B) as H4.
---- apply (@euclidean__tactics.nCol__notCol (A) (C) (B) H3).
---- assert (* Cut *) (euclidean__defs.CongA A C B A B C) as H5.
----- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (A) (C) (B) H0).
----- assert (* Cut *) (~(euclidean__defs.Lt A B A C)) as H6.
------ apply (@proposition__06a.proposition__06a (A) (C) (B) (H4) H5).
------ assert (* Cut *) (euclidean__axioms.neq A B) as H7.
------- assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H7.
-------- apply (@lemma__angledistinct.lemma__angledistinct (A) (C) (B) (A) (B) (C) H5).
-------- assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
exact H14.
------- assert (* Cut *) (euclidean__axioms.neq A C) as H8.
-------- assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H8.
--------- apply (@lemma__angledistinct.lemma__angledistinct (A) (C) (B) (A) (B) (C) H5).
--------- assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H9.
---------- exact H8.
---------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
exact H18.
-------- assert (* Cut *) (euclidean__axioms.Cong A B A C) as H9.
--------- apply (@lemma__trichotomy1.lemma__trichotomy1 (A) (B) (A) (C) (H6) (H1) (H7) H8).
--------- exact H9.
Qed.
