Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angledistinct.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__angletrichotomy.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__03.
Require Export proposition__04.
Definition proposition__06a : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.CongA A B C A C B) -> (~(euclidean__defs.Lt A C A B))).
Proof.
intro A.
intro B.
intro C.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.neq A B) as H1.
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)))))) as H1.
-- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (A) (C) (B) H0).
-- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)))))) as H2.
--- exact H1.
--- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B))))) as H4.
---- exact H3.
---- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)))) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B))) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
exact H11.
- assert (* Cut *) (euclidean__axioms.neq A C) as H2.
-- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)))))) as H2.
--- apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (A) (C) (B) H0).
--- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)))))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B))))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
exact H9.
-- assert (* Cut *) (euclidean__axioms.neq B A) as H3.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H1).
--- assert (* Cut *) (euclidean__axioms.neq C A) as H4.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (C) H2).
---- assert (* Cut *) (euclidean__axioms.neq B C) as H5.
----- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)))))) as H5.
------ apply (@lemma__angledistinct.lemma__angledistinct (A) (B) (C) (A) (C) (B) H0).
------ assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)))))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B))))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq A B)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
exact H8.
----- assert (* Cut *) (euclidean__axioms.neq C B) as H6.
------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H5).
------ assert (* Cut *) (~(euclidean__defs.Lt A C A B)) as H7.
------- intro H7.
assert (* Cut *) (euclidean__axioms.Cong B A A B) as H8.
-------- apply (@euclidean__axioms.cn__equalityreverse (B) A).
-------- assert (* Cut *) (exists (D: euclidean__axioms.Point), (euclidean__axioms.BetS B D A) /\ (euclidean__axioms.Cong B D A C)) as H9.
--------- apply (@proposition__03.proposition__03 (A) (B) (A) (C) (B) (A) (H7) H8).
--------- assert (exists D: euclidean__axioms.Point, ((euclidean__axioms.BetS B D A) /\ (euclidean__axioms.Cong B D A C))) as H10.
---------- exact H9.
---------- destruct H10 as [D H10].
assert (* AndElim *) ((euclidean__axioms.BetS B D A) /\ (euclidean__axioms.Cong B D A C)) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* Cut *) (euclidean__axioms.Cong D B A C) as H13.
------------ assert (* Cut *) ((euclidean__axioms.Cong D B C A) /\ ((euclidean__axioms.Cong D B A C) /\ (euclidean__axioms.Cong B D C A))) as H13.
------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (D) (A) (C) H12).
------------- assert (* AndElim *) ((euclidean__axioms.Cong D B C A) /\ ((euclidean__axioms.Cong D B A C) /\ (euclidean__axioms.Cong B D C A))) as H14.
-------------- exact H13.
-------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Cong D B A C) /\ (euclidean__axioms.Cong B D C A)) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
exact H16.
------------ assert (* Cut *) (euclidean__axioms.Cong B C B C) as H14.
------------- apply (@euclidean__axioms.cn__congruencereflexive (B) C).
------------- assert (* Cut *) (euclidean__defs.Out B A D) as H15.
-------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (D)).
---------------left.
exact H11.

--------------- exact H3.
-------------- assert (* Cut *) (C = C) as H16.
--------------- apply (@logic.eq__refl (Point) C).
--------------- assert (* Cut *) (euclidean__defs.Out B C C) as H17.
---------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
-----------------right.
left.
exact H16.

----------------- exact H5.
---------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H18.
----------------- exact H.
----------------- assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H19.
------------------ apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (C) H18).
------------------ assert (* Cut *) (euclidean__defs.CongA A B C D B C) as H20.
------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (B) (C) (A) (B) (C) (D) (C) (H19) (H15) H17).
------------------- assert (* Cut *) (euclidean__defs.CongA D B C A B C) as H21.
-------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (D) (B) (C) H20).
-------------------- assert (* Cut *) (euclidean__defs.CongA D B C A C B) as H22.
--------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (D) (B) (C) (A) (B) (C) (A) (C) (B) (H21) H0).
--------------------- assert (* Cut *) (euclidean__axioms.Cong B D C A) as H23.
---------------------- assert (* Cut *) ((euclidean__axioms.Cong B D C A) /\ ((euclidean__axioms.Cong B D A C) /\ (euclidean__axioms.Cong D B C A))) as H23.
----------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (B) (A) (C) H13).
----------------------- assert (* AndElim *) ((euclidean__axioms.Cong B D C A) /\ ((euclidean__axioms.Cong B D A C) /\ (euclidean__axioms.Cong D B C A))) as H24.
------------------------ exact H23.
------------------------ destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Cong B D A C) /\ (euclidean__axioms.Cong D B C A)) as H26.
------------------------- exact H25.
------------------------- destruct H26 as [H26 H27].
exact H24.
---------------------- assert (* Cut *) (euclidean__axioms.Cong B C C B) as H24.
----------------------- apply (@euclidean__axioms.cn__equalityreverse (B) C).
----------------------- assert (* Cut *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H25.
------------------------ apply (@proposition__04.proposition__04 (B) (D) (C) (C) (A) (B) (H23) (H24) H22).
------------------------ assert (* Cut *) (~(euclidean__axioms.Col C B A)) as H26.
------------------------- intro H26.
assert (* Cut *) (euclidean__axioms.Col A B C) as H27.
-------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H27.
--------------------------- exact H25.
--------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H29.
---------------------------- exact H28.
---------------------------- destruct H29 as [H29 H30].
assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H31.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (A) H26).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)))) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
exact H39.
-------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H18) H27).
------------------------- assert (* Cut *) (euclidean__defs.CongA C B A A B C) as H27.
-------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H27.
--------------------------- exact H25.
--------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H29.
---------------------------- exact H28.
---------------------------- destruct H29 as [H29 H30].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (C) (B) (A)).
-----------------------------apply (@euclidean__tactics.nCol__notCol (C) (B) (A) H26).

-------------------------- assert (* Cut *) (euclidean__defs.CongA B C D A B C) as H28.
--------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H28.
---------------------------- exact H25.
---------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H30.
----------------------------- exact H29.
----------------------------- destruct H30 as [H30 H31].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (B) (C) (D) (C) (B) (A) (A) (B) (C) (H31) H27).
--------------------------- assert (* Cut *) (euclidean__defs.CongA B C D A C B) as H29.
---------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H29.
----------------------------- exact H25.
----------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H31.
------------------------------ exact H30.
------------------------------ destruct H31 as [H31 H32].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (B) (C) (D) (A) (B) (C) (A) (C) (B) (H28) H0).
---------------------------- assert (* Cut *) (~(euclidean__axioms.Col A C B)) as H30.
----------------------------- intro H30.
assert (* Cut *) (euclidean__axioms.Col A B C) as H31.
------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H31.
------------------------------- exact H25.
------------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H33.
-------------------------------- exact H32.
-------------------------------- destruct H33 as [H33 H34].
assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H35.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (B) H30).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H36.
---------------------------------- exact H35.
---------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)))) as H38.
----------------------------------- exact H37.
----------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
exact H42.
------------------------------ apply (@H26).
-------------------------------apply (@euclidean__tactics.not__nCol__Col (C) (B) (A)).
--------------------------------intro H32.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H18) H31).


----------------------------- assert (* Cut *) (euclidean__defs.CongA A C B B C A) as H31.
------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H31.
------------------------------- exact H25.
------------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H33.
-------------------------------- exact H32.
-------------------------------- destruct H33 as [H33 H34].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (A) (C) (B)).
---------------------------------apply (@euclidean__tactics.nCol__notCol (A) (C) (B) H30).

------------------------------ assert (* Cut *) (euclidean__defs.CongA B C D B C A) as H32.
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H32.
-------------------------------- exact H25.
-------------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H34.
--------------------------------- exact H33.
--------------------------------- destruct H34 as [H34 H35].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (B) (C) (D) (A) (C) (B) (B) (C) (A) (H29) H31).
------------------------------- assert (* Cut *) (euclidean__defs.CongA B C A B C D) as H33.
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H33.
--------------------------------- exact H25.
--------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H35.
---------------------------------- exact H34.
---------------------------------- destruct H35 as [H35 H36].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (B) (C) (D) (B) (C) (A) H32).
-------------------------------- assert (* Cut *) (B = B) as H34.
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H34.
---------------------------------- exact H25.
---------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H36.
----------------------------------- exact H35.
----------------------------------- destruct H36 as [H36 H37].
apply (@logic.eq__refl (Point) B).
--------------------------------- assert (* Cut *) (A = A) as H35.
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H35.
----------------------------------- exact H25.
----------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H37.
------------------------------------ exact H36.
------------------------------------ destruct H37 as [H37 H38].
apply (@logic.eq__refl (Point) A).
---------------------------------- assert (* Cut *) (euclidean__defs.Out C B B) as H36.
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H36.
------------------------------------ exact H25.
------------------------------------ destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H38.
------------------------------------- exact H37.
------------------------------------- destruct H38 as [H38 H39].
apply (@lemma__ray4.lemma__ray4 (C) (B) (B)).
--------------------------------------right.
left.
exact H34.

-------------------------------------- exact H6.
----------------------------------- assert (* Cut *) (euclidean__defs.Out C A A) as H37.
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H37.
------------------------------------- exact H25.
------------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H39.
-------------------------------------- exact H38.
-------------------------------------- destruct H39 as [H39 H40].
apply (@lemma__ray4.lemma__ray4 (C) (A) (A)).
---------------------------------------right.
left.
exact H35.

--------------------------------------- exact H4.
------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col B C D)) as H38.
------------------------------------- intro H38.
assert (* Cut *) (euclidean__axioms.Col B D A) as H39.
-------------------------------------- right.
right.
right.
right.
left.
exact H11.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B A) as H40.
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H40.
---------------------------------------- exact H25.
---------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H42.
----------------------------------------- exact H41.
----------------------------------------- destruct H42 as [H42 H43].
assert (* Cut *) ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col B A D) /\ (euclidean__axioms.Col A D B))))) as H44.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (D) (A) H39).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col B A D) /\ (euclidean__axioms.Col A D B))))) as H45.
------------------------------------------- exact H44.
------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col B A D) /\ (euclidean__axioms.Col A D B)))) as H47.
-------------------------------------------- exact H46.
-------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col B A D) /\ (euclidean__axioms.Col A D B))) as H49.
--------------------------------------------- exact H48.
--------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col B A D) /\ (euclidean__axioms.Col A D B)) as H51.
---------------------------------------------- exact H50.
---------------------------------------------- destruct H51 as [H51 H52].
exact H45.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B C) as H41.
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H41.
----------------------------------------- exact H25.
----------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H43.
------------------------------------------ exact H42.
------------------------------------------ destruct H43 as [H43 H44].
assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H45.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (D) H38).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H46.
-------------------------------------------- exact H45.
-------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)))) as H48.
--------------------------------------------- exact H47.
--------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))) as H50.
---------------------------------------------- exact H49.
---------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)) as H52.
----------------------------------------------- exact H51.
----------------------------------------------- destruct H52 as [H52 H53].
exact H50.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H42.
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H42.
------------------------------------------ exact H25.
------------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H44.
------------------------------------------- exact H43.
------------------------------------------- destruct H44 as [H44 H45].
assert (* Cut *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B A))) as H46.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (D) (A) H11).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B A))) as H47.
--------------------------------------------- exact H46.
--------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B A)) as H49.
---------------------------------------------- exact H48.
---------------------------------------------- destruct H49 as [H49 H50].
exact H49.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H43.
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H43.
------------------------------------------- exact H25.
------------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H45.
-------------------------------------------- exact H44.
-------------------------------------------- destruct H45 as [H45 H46].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (D) H42).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B A C) as H44.
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H44.
-------------------------------------------- exact H25.
-------------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H46.
--------------------------------------------- exact H45.
--------------------------------------------- destruct H46 as [H46 H47].
apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
----------------------------------------------intro H48.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (C) (H48)).
-----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (B) (A) (C) (H40) (H41) H43).


------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H45.
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H45.
--------------------------------------------- exact H25.
--------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H47.
---------------------------------------------- exact H46.
---------------------------------------------- destruct H47 as [H47 H48].
assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H49.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H44).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H50.
------------------------------------------------ exact H49.
------------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H52.
------------------------------------------------- exact H51.
------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H54.
-------------------------------------------------- exact H53.
-------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H56.
--------------------------------------------------- exact H55.
--------------------------------------------------- destruct H56 as [H56 H57].
exact H50.
-------------------------------------------- apply (@H26).
---------------------------------------------apply (@euclidean__tactics.not__nCol__Col (C) (B) (A)).
----------------------------------------------intro H46.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H18) H45).


------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C D B C D) as H39.
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H39.
--------------------------------------- exact H25.
--------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H41.
---------------------------------------- exact H40.
---------------------------------------- destruct H41 as [H41 H42].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (B) (C) (D)).
-----------------------------------------apply (@euclidean__tactics.nCol__notCol (B) (C) (D) H38).

-------------------------------------- assert (* Cut *) (euclidean__defs.LtA B C D B C A) as H40.
--------------------------------------- exists B.
exists D.
exists A.
split.
---------------------------------------- exact H11.
---------------------------------------- split.
----------------------------------------- exact H36.
----------------------------------------- split.
------------------------------------------ exact H37.
------------------------------------------ exact H39.
--------------------------------------- assert (* Cut *) (euclidean__defs.LtA B C A B C A) as H41.
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H41.
----------------------------------------- exact H25.
----------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H43.
------------------------------------------ exact H42.
------------------------------------------ destruct H43 as [H43 H44].
apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (B) (C) (D) (B) (C) (A) (B) (C) (A) (H40) H33).
---------------------------------------- assert (* Cut *) (~(euclidean__defs.LtA B C A B C A)) as H42.
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D C A B) /\ ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A))) as H42.
------------------------------------------ exact H25.
------------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.CongA B D C C A B) /\ (euclidean__defs.CongA B C D C B A)) as H44.
------------------------------------------- exact H43.
------------------------------------------- destruct H44 as [H44 H45].
apply (@lemma__angletrichotomy.lemma__angletrichotomy (B) (C) (A) (B) (C) (A) H41).
----------------------------------------- apply (@H26).
------------------------------------------apply (@euclidean__tactics.not__nCol__Col (C) (B) (A)).
-------------------------------------------intro H43.
apply (@H42 H41).


------- exact H7.
Qed.
