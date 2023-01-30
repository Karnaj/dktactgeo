Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCorder.
Require Export lemma__angledistinct.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__angletrichotomy.
Require Export lemma__congruencesymmetric.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__trichotomy1.
Require Export logic.
Require Export proposition__05.
Require Export proposition__18.
Definition proposition__19 : forall A B C, (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.LtA B C A A B C) -> (euclidean__defs.Lt A B A C)).
Proof.
intro A.
intro B.
intro C.
intro H.
intro H0.
assert (euclidean__axioms.nCol A B C) as H1 by exact H.
assert (* Cut *) (euclidean__axioms.nCol B C A) as H2.
- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H2.
-- apply (@lemma__NCorder.lemma__NCorder A B C H1).
-- destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
exact H5.
- assert (* Cut *) (euclidean__axioms.nCol A C B) as H3.
-- assert (* Cut *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H3.
--- apply (@lemma__NCorder.lemma__NCorder B C A H2).
--- destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H11.
-- assert (* Cut *) (~(euclidean__axioms.Cong A C A B)) as H4.
--- intro H4.
assert (* Cut *) (euclidean__axioms.Cong A B A C) as H5.
---- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A C B H4).
---- assert (* Cut *) (euclidean__defs.isosceles A B C) as H6.
----- split.
------ exact H1.
------ exact H5.
----- assert (* Cut *) (euclidean__defs.CongA A B C A C B) as H7.
------ apply (@proposition__05.proposition__05 A B C H6).
------ assert (* Cut *) (euclidean__defs.CongA A C B A B C) as H8.
------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A B C A C B H7).
------- assert (* Cut *) (euclidean__defs.CongA B C A A C B) as H9.
-------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B C A H2).
-------- assert (* Cut *) (euclidean__defs.CongA B C A A B C) as H10.
--------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive B C A A C B A B C H9 H8).
--------- assert (* Cut *) (euclidean__defs.LtA B C A B C A) as H11.
---------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence B C A A B C B C A H0 H10).
---------- assert (* Cut *) (~(euclidean__defs.LtA B C A B C A)) as H12.
----------- apply (@lemma__angletrichotomy.lemma__angletrichotomy B C A B C A H11).
----------- apply (@H12 H11).
--- assert (* Cut *) (~(euclidean__defs.Lt A C A B)) as H5.
---- intro H5.
assert (euclidean__axioms.Triangle A C B) as H6 by exact H3.
assert (* Cut *) (euclidean__defs.LtA C B A A C B) as H7.
----- apply (@proposition__18.proposition__18 A C B H6 H5).
----- assert (* Cut *) (euclidean__defs.CongA A B C C B A) as H8.
------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A B C H1).
------ assert (* Cut *) (euclidean__defs.LtA A B C A C B) as H9.
------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 C B A A C B A B C H7 H8).
------- assert (* Cut *) (euclidean__defs.CongA B C A A C B) as H10.
-------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B C A H2).
-------- assert (* Cut *) (euclidean__defs.LtA A B C B C A) as H11.
--------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence A B C A C B B C A H9 H10).
--------- assert (* Cut *) (~(euclidean__defs.LtA A B C B C A)) as H12.
---------- apply (@lemma__angletrichotomy.lemma__angletrichotomy B C A A B C H0).
---------- apply (@H12 H11).
---- assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H6.
----- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive A B C H1).
----- assert (* Cut *) (euclidean__axioms.neq A B) as H7.
------ assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H7.
------- apply (@lemma__angledistinct.lemma__angledistinct A B C A B C H6).
------- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H14.
------ assert (* Cut *) (euclidean__axioms.neq A C) as H8.
------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H8.
-------- apply (@lemma__angledistinct.lemma__angledistinct A B C A B C H6).
-------- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H18.
------- assert (* Cut *) (~(~(euclidean__defs.Lt A B A C))) as H9.
-------- intro H9.
assert (* Cut *) (euclidean__axioms.Cong A B A C) as H10.
--------- apply (@lemma__trichotomy1.lemma__trichotomy1 A B A C H9 H5 H7 H8).
--------- assert (* Cut *) (euclidean__axioms.Cong A C A B) as H11.
---------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A B C H10).
---------- apply (@H4 H11).
-------- apply (@euclidean__tactics.NNPP (euclidean__defs.Lt A B A C)).
---------intro H10.
destruct H1 as [H11 H12].
destruct H2 as [H13 H14].
destruct H3 as [H15 H16].
destruct H12 as [H17 H18].
destruct H14 as [H19 H20].
destruct H16 as [H21 H22].
destruct H18 as [H23 H24].
destruct H20 as [H25 H26].
destruct H22 as [H27 H28].
destruct H24 as [H29 H30].
destruct H26 as [H31 H32].
destruct H28 as [H33 H34].
destruct H30 as [H35 H36].
destruct H32 as [H37 H38].
destruct H34 as [H39 H40].
assert (* Cut *) (False) as H41.
---------- apply (@H9 H10).
---------- contradiction H41.

Qed.
