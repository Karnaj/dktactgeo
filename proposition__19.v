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
Definition proposition__19 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.LtA B C A A B C) -> (euclidean__defs.Lt A B A C)).
Proof.
intro A.
intro B.
intro C.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H1.
- exact H.
- assert (* Cut *) (euclidean__axioms.nCol B C A) as H2.
-- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H2.
--- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H1).
--- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
exact H5.
-- assert (* Cut *) (euclidean__axioms.nCol A C B) as H3.
--- assert (* Cut *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H3.
---- apply (@lemma__NCorder.lemma__NCorder (B) (C) (A) H2).
---- assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H4.
----- exact H3.
----- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B)))) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B)) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
exact H11.
--- assert (* Cut *) (~(euclidean__axioms.Cong A C A B)) as H4.
---- intro H4.
assert (* Cut *) (euclidean__axioms.Cong A B A C) as H5.
----- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (A) (C) (B) H4).
----- assert (* Cut *) (euclidean__defs.isosceles A B C) as H6.
------ split.
------- exact H1.
------- exact H5.
------ assert (* Cut *) (euclidean__defs.CongA A B C A C B) as H7.
------- apply (@proposition__05.proposition__05 (A) (B) (C) H6).
------- assert (* Cut *) (euclidean__defs.CongA A C B A B C) as H8.
-------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (A) (C) (B) H7).
-------- assert (* Cut *) (euclidean__defs.CongA B C A A C B) as H9.
--------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (C) (A) H2).
--------- assert (* Cut *) (euclidean__defs.CongA B C A A B C) as H10.
---------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (B) (C) (A) (A) (C) (B) (A) (B) (C) (H9) H8).
---------- assert (* Cut *) (euclidean__defs.LtA B C A B C A) as H11.
----------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (B) (C) (A) (A) (B) (C) (B) (C) (A) (H0) H10).
----------- assert (* Cut *) (~(euclidean__defs.LtA B C A B C A)) as H12.
------------ apply (@lemma__angletrichotomy.lemma__angletrichotomy (B) (C) (A) (B) (C) (A) H11).
------------ apply (@H12 H11).
---- assert (* Cut *) (~(euclidean__defs.Lt A C A B)) as H5.
----- intro H5.
assert (* Cut *) (euclidean__axioms.Triangle A C B) as H6.
------ exact H3.
------ assert (* Cut *) (euclidean__defs.LtA C B A A C B) as H7.
------- apply (@proposition__18.proposition__18 (A) (C) (B) (H6) H5).
------- assert (* Cut *) (euclidean__defs.CongA A B C C B A) as H8.
-------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (B) (C) H1).
-------- assert (* Cut *) (euclidean__defs.LtA A B C A C B) as H9.
--------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (C) (B) (A) (A) (C) (B) (A) (B) (C) (H7) H8).
--------- assert (* Cut *) (euclidean__defs.CongA B C A A C B) as H10.
---------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (C) (A) H2).
---------- assert (* Cut *) (euclidean__defs.LtA A B C B C A) as H11.
----------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (A) (B) (C) (A) (C) (B) (B) (C) (A) (H9) H10).
----------- assert (* Cut *) (~(euclidean__defs.LtA A B C B C A)) as H12.
------------ apply (@lemma__angletrichotomy.lemma__angletrichotomy (B) (C) (A) (A) (B) (C) H0).
------------ apply (@H12 H11).
----- assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H6.
------ apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (C) H1).
------ assert (* Cut *) (euclidean__axioms.neq A B) as H7.
------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H7.
-------- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (A) (B) (C) H6).
-------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))) as H12.
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
-------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H8.
--------- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (A) (B) (C) H6).
--------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))))) as H9.
---------- exact H8.
---------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq A C)) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
exact H18.
-------- assert (* Cut *) (~(~(euclidean__defs.Lt A B A C))) as H9.
--------- intro H9.
assert (* Cut *) (euclidean__axioms.Cong A B A C) as H10.
---------- apply (@lemma__trichotomy1.lemma__trichotomy1 (A) (B) (A) (C) (H9) (H5) (H7) H8).
---------- assert (* Cut *) (euclidean__axioms.Cong A C A B) as H11.
----------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (A) (B) (C) H10).
----------- apply (@H4 H11).
--------- apply (@euclidean__tactics.NNPP (euclidean__defs.Lt A B A C)).
----------intro H10.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H11.
----------- exact H1.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))))) as H13.
------------ exact H2.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))))) as H15.
------------- exact H3.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H17.
-------------- exact H12.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))))) as H19.
--------------- exact H14.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))))) as H21.
---------------- exact H16.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H23.
----------------- exact H18.
----------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))))) as H25.
------------------ exact H20.
------------------ destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))) as H27.
------------------- exact H22.
------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H29.
-------------------- exact H24.
-------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A)))) as H31.
--------------------- exact H26.
--------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))) as H33.
---------------------- exact H28.
---------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H35.
----------------------- exact H30.
----------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ (~(euclidean__axioms.BetS C B A))) as H37.
------------------------ exact H32.
------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))) as H39.
------------------------- exact H34.
------------------------- destruct H39 as [H39 H40].
assert (* Cut *) (False) as H41.
-------------------------- apply (@H9 H10).
-------------------------- assert False.
---------------------------exact H41.
--------------------------- contradiction.

Qed.
