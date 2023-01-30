Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennesspreserved.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__differenceofparts.
Require Export lemma__doublereverse.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__interior5.
Require Export lemma__twolines.
Require Export logic.
Require Export proposition__01.
Require Export proposition__03.
Definition proposition__10 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point), (euclidean__axioms.neq A B) -> (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X B) /\ (euclidean__axioms.Cong X A X B)).
Proof.
intro A.
intro B.
intro H.
assert (* Cut *) (exists (C: euclidean__axioms.Point), (euclidean__defs.equilateral A B C) /\ (euclidean__axioms.Triangle A B C)) as H0.
- apply (@proposition__01.proposition__01 (A) (B) H).
- assert (exists C: euclidean__axioms.Point, ((euclidean__defs.equilateral A B C) /\ (euclidean__axioms.Triangle A B C))) as H1.
-- exact H0.
-- destruct H1 as [C H1].
assert (* AndElim *) ((euclidean__defs.equilateral A B C) /\ (euclidean__axioms.Triangle A B C)) as H2.
--- exact H1.
--- destruct H2 as [H2 H3].
assert (* Cut *) (euclidean__axioms.nCol A B C) as H4.
---- exact H3.
---- assert (* Cut *) ((euclidean__axioms.Cong A B B C) /\ (euclidean__axioms.Cong B C C A)) as H5.
----- assert (* Cut *) ((euclidean__axioms.Cong A B B C) /\ (euclidean__axioms.Cong B C C A)) as H5.
------ exact H2.
------ assert (* Cut *) ((euclidean__axioms.Cong A B B C) /\ (euclidean__axioms.Cong B C C A)) as __TmpHyp.
------- exact H5.
------- assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ (euclidean__axioms.Cong B C C A)) as H6.
-------- exact __TmpHyp.
-------- destruct H6 as [H6 H7].
split.
--------- exact H6.
--------- exact H7.
----- assert (* Cut *) (euclidean__axioms.Cong A C C B) as H6.
------ assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ (euclidean__axioms.Cong B C C A)) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* Cut *) ((euclidean__axioms.Cong A C C B) /\ (euclidean__axioms.Cong C B A C)) as H8.
-------- apply (@lemma__doublereverse.lemma__doublereverse (B) (C) (C) (A) H7).
-------- assert (* AndElim *) ((euclidean__axioms.Cong A C C B) /\ (euclidean__axioms.Cong C B A C)) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
exact H9.
------ assert (* Cut *) (euclidean__axioms.Cong A C B C) as H7.
------- assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ (euclidean__axioms.Cong B C C A)) as H7.
-------- exact H5.
-------- destruct H7 as [H7 H8].
assert (* Cut *) ((euclidean__axioms.Cong C A B C) /\ ((euclidean__axioms.Cong C A C B) /\ (euclidean__axioms.Cong A C B C))) as H9.
--------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (C) (C) (B) H6).
--------- assert (* AndElim *) ((euclidean__axioms.Cong C A B C) /\ ((euclidean__axioms.Cong C A C B) /\ (euclidean__axioms.Cong A C B C))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Cong C A C B) /\ (euclidean__axioms.Cong A C B C)) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
exact H13.
------- assert (* Cut *) (~(C = B)) as H8.
-------- intro H8.
assert (* Cut *) (euclidean__axioms.Col A C B) as H9.
--------- right.
right.
left.
exact H8.
--------- assert (* Cut *) (euclidean__axioms.Col A B C) as H10.
---------- assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ (euclidean__axioms.Cong B C C A)) as H10.
----------- exact H5.
----------- destruct H10 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H12.
------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (B) H9).
------------ assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H13.
------------- exact H12.
------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
exact H19.
---------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H4) H10).
-------- assert (* Cut *) (exists (D: euclidean__axioms.Point), (euclidean__axioms.BetS C B D) /\ (euclidean__axioms.Cong B D A B)) as H9.
--------- assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ (euclidean__axioms.Cong B C C A)) as H9.
---------- exact H5.
---------- destruct H9 as [H9 H10].
apply (@lemma__extension.lemma__extension (C) (B) (A) (B) (H8) H).
--------- assert (exists D: euclidean__axioms.Point, ((euclidean__axioms.BetS C B D) /\ (euclidean__axioms.Cong B D A B))) as H10.
---------- exact H9.
---------- destruct H10 as [D H10].
assert (* AndElim *) ((euclidean__axioms.BetS C B D) /\ (euclidean__axioms.Cong B D A B)) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ (euclidean__axioms.Cong B C C A)) as H13.
------------ exact H5.
------------ destruct H13 as [H13 H14].
assert (* Cut *) (~(C = A)) as H15.
------------- intro H15.
assert (* Cut *) (euclidean__axioms.Col B C A) as H16.
-------------- right.
right.
left.
exact H15.
-------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H17.
--------------- assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H17.
---------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (A) H16).
---------------- assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)))) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
exact H22.
--------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H4) H17).
------------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS C A E) /\ (euclidean__axioms.Cong A E A B)) as H16.
-------------- apply (@lemma__extension.lemma__extension (C) (A) (A) (B) (H15) H).
-------------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS C A E) /\ (euclidean__axioms.Cong A E A B))) as H17.
--------------- exact H16.
--------------- destruct H17 as [E H17].
assert (* AndElim *) ((euclidean__axioms.BetS C A E) /\ (euclidean__axioms.Cong A E A B)) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
assert (* Cut *) (euclidean__axioms.BetS D B C) as H20.
----------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (B) (D) H11).
----------------- assert (* Cut *) (euclidean__axioms.BetS E A C) as H21.
------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (A) (E) H18).
------------------ assert (* Cut *) (~(euclidean__axioms.Col D C E)) as H22.
------------------- intro H22.
assert (* Cut *) (euclidean__axioms.Col C A E) as H23.
-------------------- right.
right.
right.
right.
left.
exact H18.
-------------------- assert (* Cut *) (euclidean__axioms.Col C B D) as H24.
--------------------- right.
right.
right.
right.
left.
exact H11.
--------------------- assert (* Cut *) (euclidean__axioms.Col E C D) as H25.
---------------------- assert (* Cut *) ((euclidean__axioms.Col C D E) /\ ((euclidean__axioms.Col C E D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D E C) /\ (euclidean__axioms.Col E C D))))) as H25.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (E) H22).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col C D E) /\ ((euclidean__axioms.Col C E D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D E C) /\ (euclidean__axioms.Col E C D))))) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col C E D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D E C) /\ (euclidean__axioms.Col E C D)))) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D E C) /\ (euclidean__axioms.Col E C D))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col D E C) /\ (euclidean__axioms.Col E C D)) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
exact H33.
---------------------- assert (* Cut *) (euclidean__axioms.Col E C A) as H26.
----------------------- assert (* Cut *) ((euclidean__axioms.Col A C E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C))))) as H26.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (E) H23).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col A C E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C))))) as H27.
------------------------- exact H26.
------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C)))) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C))) as H31.
--------------------------- exact H30.
--------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C)) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
exact H31.
----------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H27.
------------------------ assert (* Cut *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E))) as H27.
------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (A) (E) H18).
------------------------- assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E))) as H28.
-------------------------- exact H27.
-------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E)) as H30.
--------------------------- exact H29.
--------------------------- destruct H30 as [H30 H31].
exact H31.
------------------------ assert (* Cut *) (euclidean__axioms.neq E C) as H28.
------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (E) H27).
------------------------- assert (* Cut *) (euclidean__axioms.Col C D A) as H29.
-------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (D) (A)).
---------------------------intro H29.
apply (@euclidean__tactics.Col__nCol__False (C) (D) (A) (H29)).
----------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (C) (D) (A) (H25) (H26) H28).


-------------------------- assert (* Cut *) (euclidean__axioms.Col D C B) as H30.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H30.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (D) H24).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H31.
----------------------------- exact H30.
----------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
exact H35.
--------------------------- assert (* Cut *) (euclidean__axioms.Col D C A) as H31.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C))))) as H31.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (A) H29).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C))))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C)))) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C)) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
exact H32.
---------------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H32.
----------------------------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H32.
------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (C) (B) (D) H11).
------------------------------ assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H33.
------------------------------- exact H32.
------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)) as H35.
-------------------------------- exact H34.
-------------------------------- destruct H35 as [H35 H36].
exact H36.
----------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H33.
------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (D) H32).
------------------------------ assert (* Cut *) (euclidean__axioms.Col C B A) as H34.
------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (B) (A)).
--------------------------------intro H34.
apply (@euclidean__tactics.Col__nCol__False (C) (B) (A) (H34)).
---------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (C) (B) (A) (H30) (H31) H33).


------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H35.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H35.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (A) H34).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H36.
---------------------------------- exact H35.
---------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)))) as H38.
----------------------------------- exact H37.
----------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
exact H43.
-------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H4) H35).
------------------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS D F A) /\ (euclidean__axioms.BetS E F B)) as H23.
-------------------- apply (@euclidean__axioms.postulate__Pasch__inner (D) (E) (C) (B) (A) (H20) (H21)).
---------------------apply (@euclidean__tactics.nCol__notCol (D) (C) (E) H22).

-------------------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS D F A) /\ (euclidean__axioms.BetS E F B))) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [F H24].
assert (* AndElim *) ((euclidean__axioms.BetS D F A) /\ (euclidean__axioms.BetS E F B)) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [H25 H26].
assert (* Cut *) (euclidean__axioms.BetS B F E) as H27.
----------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (F) (B) H26).
----------------------- assert (* Cut *) (euclidean__axioms.BetS A F D) as H28.
------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (F) (A) H25).
------------------------ assert (* Cut *) (euclidean__axioms.neq C D) as H29.
------------------------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H29.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (B) (D) H11).
-------------------------- assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H30.
--------------------------- exact H29.
--------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [H32 H33].
exact H33.
------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H30.
-------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (D) H29).
-------------------------- assert (* Cut *) (~(euclidean__axioms.Col A D C)) as H31.
--------------------------- intro H31.
assert (* Cut *) (euclidean__axioms.Col C B D) as H32.
---------------------------- right.
right.
right.
right.
left.
exact H11.
---------------------------- assert (* Cut *) (euclidean__axioms.Col D C A) as H33.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A C D) /\ (euclidean__axioms.Col C D A))))) as H33.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (C) H31).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A C D) /\ (euclidean__axioms.Col C D A))))) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A C D) /\ (euclidean__axioms.Col C D A)))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A C D) /\ (euclidean__axioms.Col C D A))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A C D) /\ (euclidean__axioms.Col C D A)) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
exact H36.
----------------------------- assert (* Cut *) (euclidean__axioms.Col D C B) as H34.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H34.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (D) H32).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H35.
-------------------------------- exact H34.
-------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)))) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)) as H41.
----------------------------------- exact H40.
----------------------------------- destruct H41 as [H41 H42].
exact H39.
------------------------------ assert (* Cut *) (euclidean__axioms.Col C A B) as H35.
------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (A) (B)).
--------------------------------intro H35.
apply (@euclidean__tactics.Col__nCol__False (C) (A) (B) (H35)).
---------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (C) (A) (B) (H33) (H34) H30).


------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H36.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H36.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (B) H35).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H37.
---------------------------------- exact H36.
---------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)))) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
exact H39.
-------------------------------- apply (@H22).
---------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (C) (E)).
----------------------------------intro H37.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H4) H36).


--------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M B) /\ (euclidean__axioms.BetS C M F)) as H32.
---------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (A) (C) (D) (F) (B) (H28) (H11)).
-----------------------------apply (@euclidean__tactics.nCol__notCol (A) (D) (C) H31).

---------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M B) /\ (euclidean__axioms.BetS C M F))) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [M H33].
assert (* AndElim *) ((euclidean__axioms.BetS A M B) /\ (euclidean__axioms.BetS C M F)) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
assert (* Cut *) (euclidean__axioms.Cong C A C B) as H36.
------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C A C B) /\ ((euclidean__axioms.Cong C A B C) /\ (euclidean__axioms.Cong A C C B))) as H36.
-------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (C) (B) (C) H7).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C A C B) /\ ((euclidean__axioms.Cong C A B C) /\ (euclidean__axioms.Cong A C C B))) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Cong C A B C) /\ (euclidean__axioms.Cong A C C B)) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [H39 H40].
exact H37.
------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A E) as H37.
-------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (A) (E) (B) H19).
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D A E) as H38.
--------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (D) (A) (B) (A) (E) (H12) H37).
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong A E B D) as H39.
---------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (B) (D) (E) H38).
---------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B B A) as H40.
----------------------------------- apply (@euclidean__axioms.cn__equalityreverse (A) B).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong C B C A) as H41.
------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (C) (A) (B) H36).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B E A D) as H42.
------------------------------------- apply (@euclidean__axioms.axiom__5__line (C) (A) (E) (B) (C) (B) (D) (A) (H39) (H41) (H40) (H18) (H11) H36).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B F B F) as H43.
-------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) F).
-------------------------------------- assert (* Cut *) (euclidean__defs.Lt B F B E) as H44.
--------------------------------------- exists F.
split.
---------------------------------------- exact H27.
---------------------------------------- exact H43.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D B E) as H45.
---------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (B) (E) (D) H42).
---------------------------------------- assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__axioms.BetS A G D) /\ (euclidean__axioms.Cong A G B F)) as H46.
----------------------------------------- apply (@proposition__03.proposition__03 (B) (E) (B) (F) (A) (D) (H44) H45).
----------------------------------------- assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.BetS A G D) /\ (euclidean__axioms.Cong A G B F))) as H47.
------------------------------------------ exact H46.
------------------------------------------ destruct H47 as [G H47].
assert (* AndElim *) ((euclidean__axioms.BetS A G D) /\ (euclidean__axioms.Cong A G B F)) as H48.
------------------------------------------- exact H47.
------------------------------------------- destruct H48 as [H48 H49].
assert (* Cut *) (euclidean__axioms.Cong G D F E) as H50.
-------------------------------------------- apply (@lemma__differenceofparts.lemma__differenceofparts (A) (G) (D) (B) (F) (E) (H49) (H45) (H48) H27).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E F D G) as H51.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E F D G) /\ (euclidean__axioms.Cong D G E F)) as H51.
---------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (G) (D) (F) (E) H50).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E F D G) /\ (euclidean__axioms.Cong D G E F)) as H52.
----------------------------------------------- exact H51.
----------------------------------------------- destruct H52 as [H52 H53].
exact H52.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F B G A) as H52.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F B G A) /\ (euclidean__axioms.Cong G A F B)) as H52.
----------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (A) (G) (B) (F) H49).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F B G A) /\ (euclidean__axioms.Cong G A F B)) as H53.
------------------------------------------------ exact H52.
------------------------------------------------ destruct H53 as [H53 H54].
exact H53.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E A D B) as H53.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E A D B) /\ ((euclidean__axioms.Cong E A B D) /\ (euclidean__axioms.Cong A E D B))) as H53.
------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (A) (E) (B) (D) H39).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong E A D B) /\ ((euclidean__axioms.Cong E A B D) /\ (euclidean__axioms.Cong A E D B))) as H54.
------------------------------------------------- exact H53.
------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Cong E A B D) /\ (euclidean__axioms.Cong A E D B)) as H56.
-------------------------------------------------- exact H55.
-------------------------------------------------- destruct H56 as [H56 H57].
exact H54.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A A B) as H54.
------------------------------------------------ apply (@euclidean__axioms.cn__equalityreverse (B) A).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS D G A) as H55.
------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (G) (D) H48).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F A G B) as H56.
-------------------------------------------------- apply (@lemma__interior5.lemma__interior5 (E) (F) (B) (A) (D) (G) (A) (B) (H26) (H55) (H51) (H52) (H53) H54).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F B G) as H57.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A F B G) /\ ((euclidean__axioms.Cong A F G B) /\ (euclidean__axioms.Cong F A B G))) as H57.
---------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (A) (G) (B) H56).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A F B G) /\ ((euclidean__axioms.Cong A F G B) /\ (euclidean__axioms.Cong F A B G))) as H58.
----------------------------------------------------- exact H57.
----------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Cong A F G B) /\ (euclidean__axioms.Cong F A B G)) as H60.
------------------------------------------------------ exact H59.
------------------------------------------------------ destruct H60 as [H60 H61].
exact H58.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E D D E) as H58.
---------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse (E) D).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F D G E) as H59.
----------------------------------------------------- apply (@lemma__interior5.lemma__interior5 (E) (F) (B) (D) (D) (G) (A) (E) (H26) (H55) (H51) (H52) (H58) H38).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B G E) as H60.
------------------------------------------------------ apply (@lemma__betweennesspreserved.lemma__betweennesspreserved (A) (F) (D) (B) (G) (E) (H57) (H45) (H59) H28).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS E G B) as H61.
------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (G) (E) H60).
------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A D E)) as H62.
-------------------------------------------------------- intro H62.
assert (* Cut *) (euclidean__axioms.Col C A E) as H63.
--------------------------------------------------------- right.
right.
right.
right.
left.
exact H18.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E D) as H64.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H64.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (E) H62).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H65.
------------------------------------------------------------ exact H64.
------------------------------------------------------------ destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)))) as H67.
------------------------------------------------------------- exact H66.
------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))) as H69.
-------------------------------------------------------------- exact H68.
-------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)) as H71.
--------------------------------------------------------------- exact H70.
--------------------------------------------------------------- destruct H71 as [H71 H72].
exact H71.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E C) as H65.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A C E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C))))) as H65.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (E) H63).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A C E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C))))) as H66.
------------------------------------------------------------- exact H65.
------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C)))) as H68.
-------------------------------------------------------------- exact H67.
-------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C))) as H70.
--------------------------------------------------------------- exact H69.
--------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C)) as H72.
---------------------------------------------------------------- exact H71.
---------------------------------------------------------------- destruct H72 as [H72 H73].
exact H68.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H66.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E))) as H66.
------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (A) (E) H18).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E))) as H67.
-------------------------------------------------------------- exact H66.
-------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E)) as H69.
--------------------------------------------------------------- exact H68.
--------------------------------------------------------------- destruct H69 as [H69 H70].
exact H67.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E D C) as H67.
------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (E) (D) (C)).
--------------------------------------------------------------intro H67.
apply (@euclidean__tactics.Col__nCol__False (E) (D) (C) (H67)).
---------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (E) (D) (C) (H64) (H65) H66).


------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C D) as H68.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D E C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C E D) /\ ((euclidean__axioms.Col E C D) /\ (euclidean__axioms.Col C D E))))) as H68.
--------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (D) (C) H67).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D E C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C E D) /\ ((euclidean__axioms.Col E C D) /\ (euclidean__axioms.Col C D E))))) as H69.
---------------------------------------------------------------- exact H68.
---------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C E D) /\ ((euclidean__axioms.Col E C D) /\ (euclidean__axioms.Col C D E)))) as H71.
----------------------------------------------------------------- exact H70.
----------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col C E D) /\ ((euclidean__axioms.Col E C D) /\ (euclidean__axioms.Col C D E))) as H73.
------------------------------------------------------------------ exact H72.
------------------------------------------------------------------ destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col E C D) /\ (euclidean__axioms.Col C D E)) as H75.
------------------------------------------------------------------- exact H74.
------------------------------------------------------------------- destruct H75 as [H75 H76].
exact H75.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C A) as H69.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H69.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (C) H65).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))))) as H70.
----------------------------------------------------------------- exact H69.
----------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)))) as H72.
------------------------------------------------------------------ exact H71.
------------------------------------------------------------------ destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col C A E) /\ ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A))) as H74.
------------------------------------------------------------------- exact H73.
------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col A C E) /\ (euclidean__axioms.Col C E A)) as H76.
-------------------------------------------------------------------- exact H75.
-------------------------------------------------------------------- destruct H76 as [H76 H77].
exact H72.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H70.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E))) as H70.
----------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (A) (E) H18).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E))) as H71.
------------------------------------------------------------------ exact H70.
------------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E)) as H73.
------------------------------------------------------------------- exact H72.
------------------------------------------------------------------- destruct H73 as [H73 H74].
exact H74.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E C) as H71.
----------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (E) H70).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D A) as H72.
------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (C) (D) (A)).
-------------------------------------------------------------------intro H72.
apply (@euclidean__tactics.Col__nCol__False (C) (D) (A) (H72)).
--------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (C) (D) (A) (H68) (H69) H71).


------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C B D) as H73.
------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H11.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C A) as H74.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C))))) as H74.
--------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (A) H72).
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C))))) as H75.
---------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C)))) as H77.
----------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C))) as H79.
------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------ destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C)) as H81.
------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H75.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C B) as H75.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H75.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (D) H73).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H76.
----------------------------------------------------------------------- exact H75.
----------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)))) as H78.
------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------ destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))) as H80.
------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)) as H82.
-------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H80.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H76.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E B))) as H76.
----------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (G) (B) H61).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E B))) as H77.
------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E B)) as H79.
------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------- destruct H79 as [H79 H80].
exact H29.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H77.
----------------------------------------------------------------------- exact H30.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C A B) as H78.
------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (C) (A) (B)).
-------------------------------------------------------------------------intro H78.
apply (@euclidean__tactics.Col__nCol__False (C) (A) (B) (H78)).
--------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (C) (A) (B) (H74) (H75) H77).


------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B C) as H79.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H79.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (B) H78).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H80.
--------------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)))) as H82.
---------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))) as H84.
----------------------------------------------------------------------------- exact H83.
----------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)) as H86.
------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------ destruct H86 as [H86 H87].
exact H82.
------------------------------------------------------------------------- apply (@H22).
--------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (C) (E)).
---------------------------------------------------------------------------intro H80.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H4) H79).


-------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A D B)) as H63.
--------------------------------------------------------- intro H63.
assert (* Cut *) (euclidean__axioms.Col D B A) as H64.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A))))) as H64.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (B) H63).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A))))) as H65.
------------------------------------------------------------ exact H64.
------------------------------------------------------------ destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A)))) as H67.
------------------------------------------------------------- exact H66.
------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A))) as H69.
-------------------------------------------------------------- exact H68.
-------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A)) as H71.
--------------------------------------------------------------- exact H70.
--------------------------------------------------------------- destruct H71 as [H71 H72].
exact H67.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B D) as H65.
----------------------------------------------------------- right.
right.
right.
right.
left.
exact H11.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B C) as H66.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H66.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (D) H65).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H67.
-------------------------------------------------------------- exact H66.
-------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)))) as H69.
--------------------------------------------------------------- exact H68.
--------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))) as H71.
---------------------------------------------------------------- exact H70.
---------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)) as H73.
----------------------------------------------------------------- exact H72.
----------------------------------------------------------------- destruct H73 as [H73 H74].
exact H74.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq B D) as H67.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H67.
-------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (B) (D) H11).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H68.
--------------------------------------------------------------- exact H67.
--------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)) as H70.
---------------------------------------------------------------- exact H69.
---------------------------------------------------------------- destruct H70 as [H70 H71].
exact H68.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H68.
-------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (D) H67).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H69.
--------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
----------------------------------------------------------------intro H69.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (C) (H69)).
-----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (B) (A) (C) (H64) (H66) H68).


--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H70.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H70.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H69).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H71.
------------------------------------------------------------------ exact H70.
------------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H73.
------------------------------------------------------------------- exact H72.
------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H75.
-------------------------------------------------------------------- exact H74.
-------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H77.
--------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------- destruct H77 as [H77 H78].
exact H71.
---------------------------------------------------------------- apply (@H22).
-----------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (C) (E)).
------------------------------------------------------------------intro H71.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H4) H70).


--------------------------------------------------------- assert (* Cut *) (euclidean__defs.Cut A D E B G) as H64.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H48.
----------------------------------------------------------- split.
------------------------------------------------------------ exact H61.
------------------------------------------------------------ split.
------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (D) (E) H62).
------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (D) (B) H63).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Cut A D E B F) as H65.
----------------------------------------------------------- split.
------------------------------------------------------------ exact H28.
------------------------------------------------------------ split.
------------------------------------------------------------- exact H26.
------------------------------------------------------------- split.
-------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (D) (E) H62).
-------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (D) (B) H63).
----------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col D E B)) as H66.
------------------------------------------------------------ intro H66.
assert (* Cut *) (euclidean__axioms.Col C B D) as H67.
------------------------------------------------------------- right.
right.
right.
right.
left.
exact H11.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B C) as H68.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H68.
--------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (D) H67).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H69.
---------------------------------------------------------------- exact H68.
---------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)))) as H71.
----------------------------------------------------------------- exact H70.
----------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))) as H73.
------------------------------------------------------------------ exact H72.
------------------------------------------------------------------ destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)) as H75.
------------------------------------------------------------------- exact H74.
------------------------------------------------------------------- destruct H75 as [H75 H76].
exact H76.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B E) as H69.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E D B) /\ ((euclidean__axioms.Col E B D) /\ ((euclidean__axioms.Col B D E) /\ ((euclidean__axioms.Col D B E) /\ (euclidean__axioms.Col B E D))))) as H69.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (E) (B) H66).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E D B) /\ ((euclidean__axioms.Col E B D) /\ ((euclidean__axioms.Col B D E) /\ ((euclidean__axioms.Col D B E) /\ (euclidean__axioms.Col B E D))))) as H70.
----------------------------------------------------------------- exact H69.
----------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col E B D) /\ ((euclidean__axioms.Col B D E) /\ ((euclidean__axioms.Col D B E) /\ (euclidean__axioms.Col B E D)))) as H72.
------------------------------------------------------------------ exact H71.
------------------------------------------------------------------ destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col B D E) /\ ((euclidean__axioms.Col D B E) /\ (euclidean__axioms.Col B E D))) as H74.
------------------------------------------------------------------- exact H73.
------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col D B E) /\ (euclidean__axioms.Col B E D)) as H76.
-------------------------------------------------------------------- exact H75.
-------------------------------------------------------------------- destruct H76 as [H76 H77].
exact H76.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H70.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H70.
----------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (B) (D) H11).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H71.
------------------------------------------------------------------ exact H70.
------------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)) as H73.
------------------------------------------------------------------- exact H72.
------------------------------------------------------------------- destruct H73 as [H73 H74].
exact H71.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H71.
----------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (D) H70).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C E) as H72.
------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (B) (C) (E)).
-------------------------------------------------------------------intro H72.
apply (@euclidean__tactics.Col__nCol__False (B) (C) (E) (H72)).
--------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (B) (C) (E) (H68) (H69) H71).


------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C A E) as H73.
------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H18.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C A) as H74.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A C E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C))))) as H74.
--------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (E) H73).
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A C E) /\ ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C))))) as H75.
---------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col A E C) /\ ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C)))) as H77.
----------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col E C A) /\ ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C))) as H79.
------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------ destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col C E A) /\ (euclidean__axioms.Col E A C)) as H81.
------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H79.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C B) as H75.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H75.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (E) H72).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H76.
----------------------------------------------------------------------- exact H75.
----------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)))) as H78.
------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------ destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))) as H80.
------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)) as H82.
-------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H83.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H76.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E))) as H76.
----------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (A) (E) H18).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E))) as H77.
------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C E)) as H79.
------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------- destruct H79 as [H79 H80].
exact H80.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E C) as H77.
----------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (E) H76).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C A B) as H78.
------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (C) (A) (B)).
-------------------------------------------------------------------------intro H78.
apply (@euclidean__tactics.Col__nCol__False (C) (A) (B) (H78)).
--------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (C) (A) (B) (H74) (H75) H77).


------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B C) as H79.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H79.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (A) (B) H78).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H80.
--------------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)))) as H82.
---------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))) as H84.
----------------------------------------------------------------------------- exact H83.
----------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C)) as H86.
------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------ destruct H86 as [H86 H87].
exact H82.
------------------------------------------------------------------------- apply (@H22).
--------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (C) (E)).
---------------------------------------------------------------------------intro H80.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H4) H79).


------------------------------------------------------------ assert (* Cut *) (G = F) as H67.
------------------------------------------------------------- apply (@lemma__twolines.lemma__twolines (A) (D) (E) (B) (G) (F) (H64) (H65)).
--------------------------------------------------------------apply (@euclidean__tactics.nCol__notCol (D) (E) (B) H66).

------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F B F) as H68.
-------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun G0: euclidean__axioms.Point => (euclidean__axioms.BetS A G0 D) -> ((euclidean__axioms.Cong A G0 B F) -> ((euclidean__axioms.Cong G0 D F E) -> ((euclidean__axioms.Cong E F D G0) -> ((euclidean__axioms.Cong F B G0 A) -> ((euclidean__axioms.BetS D G0 A) -> ((euclidean__axioms.Cong F A G0 B) -> ((euclidean__axioms.Cong A F B G0) -> ((euclidean__axioms.Cong F D G0 E) -> ((euclidean__axioms.BetS B G0 E) -> ((euclidean__axioms.BetS E G0 B) -> ((euclidean__defs.Cut A D E B G0) -> (euclidean__axioms.Cong A F B F)))))))))))))) with (x := G).
---------------------------------------------------------------intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
exact H75.

--------------------------------------------------------------- exact H67.
--------------------------------------------------------------- exact H48.
--------------------------------------------------------------- exact H49.
--------------------------------------------------------------- exact H50.
--------------------------------------------------------------- exact H51.
--------------------------------------------------------------- exact H52.
--------------------------------------------------------------- exact H55.
--------------------------------------------------------------- exact H56.
--------------------------------------------------------------- exact H57.
--------------------------------------------------------------- exact H59.
--------------------------------------------------------------- exact H60.
--------------------------------------------------------------- exact H61.
--------------------------------------------------------------- exact H64.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F A F B) as H69.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F A F B) /\ ((euclidean__axioms.Cong F A B F) /\ (euclidean__axioms.Cong A F F B))) as H69.
---------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (F) (B) (F) H68).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong F A F B) /\ ((euclidean__axioms.Cong F A B F) /\ (euclidean__axioms.Cong A F F B))) as H70.
----------------------------------------------------------------- exact H69.
----------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Cong F A B F) /\ (euclidean__axioms.Cong A F F B)) as H72.
------------------------------------------------------------------ exact H71.
------------------------------------------------------------------ destruct H72 as [H72 H73].
exact H70.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C M C M) as H70.
---------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (C) M).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M F M F) as H71.
----------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (M) F).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M A M B) as H72.
------------------------------------------------------------------ apply (@lemma__interior5.lemma__interior5 (C) (M) (F) (A) (C) (M) (F) (B) (H35) (H35) (H70) (H71) (H36) H69).
------------------------------------------------------------------ exists M.
split.
------------------------------------------------------------------- exact H34.
------------------------------------------------------------------- exact H72.
Qed.
