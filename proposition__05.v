Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export logic.
Require Export proposition__04.
Definition proposition__05 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__defs.isosceles A B C) -> (euclidean__defs.CongA A B C A C B).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as H0.
- assert (* Cut *) ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as H0.
-- exact H.
-- assert (* Cut *) ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as __TmpHyp.
--- exact H0.
--- assert (* AndElim *) ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as H1.
---- exact __TmpHyp.
---- destruct H1 as [H1 H2].
split.
----- exact H1.
----- exact H2.
- assert (* Cut *) (euclidean__axioms.Cong A C A B) as H1.
-- assert (* AndElim *) ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as H1.
--- exact H0.
--- destruct H1 as [H1 H2].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (A) (B) (C) H2).
-- assert (* Cut *) (euclidean__axioms.nCol A B C) as H2.
--- assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.Cong A B A C)) as H2.
---- exact H0.
---- destruct H2 as [H2 H3].
exact H2.
--- assert (* Cut *) (~(euclidean__axioms.Col C A B)) as H3.
---- intro H3.
assert (* Cut *) (euclidean__axioms.Col A B C) as H4.
----- assert (* AndElim *) ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as H4.
------ exact H0.
------ destruct H4 as [H4 H5].
assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H6.
------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (B) H3).
------- assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H7.
-------- exact H6.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)))) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
exact H9.
----- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H2) H4).
---- assert (* Cut *) (euclidean__defs.CongA C A B B A C) as H4.
----- assert (* AndElim *) ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as H4.
------ exact H0.
------ destruct H4 as [H4 H5].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (C) (A) (B)).
-------apply (@euclidean__tactics.nCol__notCol (C) (A) (B) H3).

----- assert (* Cut *) ((euclidean__axioms.Cong C B B C) /\ ((euclidean__defs.CongA A C B A B C) /\ (euclidean__defs.CongA A B C A C B))) as H5.
------ assert (* AndElim *) ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as H5.
------- exact H0.
------- destruct H5 as [H5 H6].
apply (@proposition__04.proposition__04 (A) (C) (B) (A) (B) (C) (H1) (H6) H4).
------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA A B C A C B)).
-------intro H6.
assert (* AndElim *) ((euclidean__axioms.Triangle A B C) /\ (euclidean__axioms.Cong A B A C)) as H7.
-------- exact H0.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H9.
--------- exact H2.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Cong C B B C) /\ ((euclidean__defs.CongA A C B A B C) /\ (euclidean__defs.CongA A B C A C B))) as H11.
---------- exact H5.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H13.
----------- exact H10.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.CongA A C B A B C) /\ (euclidean__defs.CongA A B C A C B)) as H15.
------------ exact H12.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H17.
------------- exact H14.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* Cut *) (False) as H23.
---------------- apply (@H6 H16).
---------------- assert False.
-----------------exact H23.
----------------- contradiction.

Qed.
