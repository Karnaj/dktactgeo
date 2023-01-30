Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__NCorder.
Require Export lemma__collinearorder.
Require Export lemma__oppositesidesymmetric.
Require Export logic.
Definition lemma__crossimpliesopposite : forall A B C D, (euclidean__defs.CR A B C D) -> ((euclidean__axioms.nCol A C D) -> ((euclidean__axioms.TS A C D B) /\ ((euclidean__axioms.TS A D C B) /\ ((euclidean__axioms.TS B C D A) /\ (euclidean__axioms.TS B D C A))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (exists M, (euclidean__axioms.BetS A M B) /\ (euclidean__axioms.BetS C M D)) as H1 by exact H.
destruct H1 as [M H2].
destruct H2 as [H3 H4].
assert (* Cut *) (euclidean__axioms.Col C M D) as H5.
- right.
right.
right.
right.
left.
exact H4.
- assert (* Cut *) (euclidean__axioms.Col C D M) as H6.
-- assert (* Cut *) ((euclidean__axioms.Col M C D) /\ ((euclidean__axioms.Col M D C) /\ ((euclidean__axioms.Col D C M) /\ ((euclidean__axioms.Col C D M) /\ (euclidean__axioms.Col D M C))))) as H6.
--- apply (@lemma__collinearorder.lemma__collinearorder C M D H5).
--- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H13.
-- assert (* Cut *) (euclidean__axioms.nCol C D A) as H7.
--- assert (* Cut *) ((euclidean__axioms.nCol C A D) /\ ((euclidean__axioms.nCol C D A) /\ ((euclidean__axioms.nCol D A C) /\ ((euclidean__axioms.nCol A D C) /\ (euclidean__axioms.nCol D C A))))) as H7.
---- apply (@lemma__NCorder.lemma__NCorder A C D H0).
---- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H10.
--- assert (* Cut *) (euclidean__axioms.nCol D C A) as H8.
---- assert (* Cut *) ((euclidean__axioms.nCol D C A) /\ ((euclidean__axioms.nCol D A C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol C A D) /\ (euclidean__axioms.nCol A D C))))) as H8.
----- apply (@lemma__NCorder.lemma__NCorder C D A H7).
----- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H9.
---- assert (* Cut *) (euclidean__axioms.TS A C D B) as H9.
----- exists M.
split.
------ exact H3.
------ split.
------- exact H6.
------- exact H7.
----- assert (* Cut *) (euclidean__axioms.Col D C M) as H10.
------ assert (* Cut *) ((euclidean__axioms.Col D C M) /\ ((euclidean__axioms.Col D M C) /\ ((euclidean__axioms.Col M C D) /\ ((euclidean__axioms.Col C M D) /\ (euclidean__axioms.Col M D C))))) as H10.
------- apply (@lemma__collinearorder.lemma__collinearorder C D M H6).
------- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H11.
------ assert (* Cut *) (euclidean__axioms.TS A D C B) as H11.
------- exists M.
split.
-------- exact H3.
-------- split.
--------- exact H10.
--------- exact H8.
------- assert (* Cut *) (euclidean__axioms.TS B C D A) as H12.
-------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric C D A B H9).
-------- assert (* Cut *) (euclidean__axioms.TS B D C A) as H13.
--------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric D C A B H11).
--------- split.
---------- exact H9.
---------- split.
----------- exact H11.
----------- split.
------------ exact H12.
------------ exact H13.
Qed.
