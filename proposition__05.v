Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export logic.
Require Export proposition__04.
Definition proposition__05 : forall A B C, (euclidean__defs.isosceles A B C) -> (euclidean__defs.CongA A B C A C B).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as H0.
- assert ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as H0 by exact H.
assert ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as __TmpHyp by exact H0.
destruct __TmpHyp as [H1 H2].
split.
-- exact H1.
-- exact H2.
- assert (* Cut *) (euclidean__axioms.Cong A C A B) as H1.
-- destruct H0 as [H1 H2].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A B C H2).
-- assert (* Cut *) (euclidean__axioms.nCol A B C) as H2.
--- destruct H0 as [H2 H3].
exact H2.
--- assert (* Cut *) (~(euclidean__axioms.Col C A B)) as H3.
---- intro H3.
assert (* Cut *) (euclidean__axioms.Col A B C) as H4.
----- destruct H0 as [H4 H5].
assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H6.
------ apply (@lemma__collinearorder.lemma__collinearorder C A B H3).
------ destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H9.
----- apply (@euclidean__tactics.Col__nCol__False A B C H2 H4).
---- assert (* Cut *) (euclidean__defs.CongA C A B B A C) as H4.
----- destruct H0 as [H4 H5].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA C A B).
------apply (@euclidean__tactics.nCol__notCol C A B H3).

----- assert (* Cut *) ((euclidean__axioms.Cong C B B C) /\ ((euclidean__defs.CongA A C B A B C) /\ (euclidean__defs.CongA A B C A C B))) as H5.
------ destruct H0 as [H5 H6].
apply (@proposition__04.proposition__04 A C B A B C H1 H6 H4).
------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA A B C A C B)).
-------intro H6.
destruct H0 as [H7 H8].
destruct H2 as [H9 H10].
destruct H5 as [H11 H12].
destruct H10 as [H13 H14].
destruct H12 as [H15 H16].
destruct H14 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
assert (* Cut *) (False) as H23.
-------- apply (@H6 H16).
-------- contradiction H23.

Qed.
