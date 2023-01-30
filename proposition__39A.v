Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel2.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__ray1.
Require Export lemma__ray3.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export logic.
Require Export proposition__04.
Require Export proposition__10.
Require Export proposition__15.
Require Export proposition__27B.
Require Export proposition__37.
Definition proposition__39A : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.ET A B C D B C) -> ((euclidean__axioms.BetS A M C) -> ((euclidean__defs.Out B D M) -> (euclidean__defs.Par A D B C)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro M.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H3.
- exact H.
- assert (* Cut *) (euclidean__axioms.neq A B) as H4.
-- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H4.
--- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H3).
--- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H11.
------- exact H10.
------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H13.
-------- exact H12.
-------- destruct H13 as [H13 H14].
exact H5.
-- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS A m B) /\ (euclidean__axioms.Cong m A m B)) as H5.
--- apply (@proposition__10.proposition__10 (A) (B) H4).
--- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS A m B) /\ (euclidean__axioms.Cong m A m B))) as H6.
---- exact H5.
---- destruct H6 as [m H6].
assert (* AndElim *) ((euclidean__axioms.BetS A m B) /\ (euclidean__axioms.Cong m A m B)) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* Cut *) (euclidean__axioms.Col A m B) as H9.
------ right.
right.
right.
right.
left.
exact H7.
------ assert (* Cut *) (euclidean__axioms.Col A B m) as H10.
------- assert (* Cut *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H10.
-------- apply (@lemma__collinearorder.lemma__collinearorder (A) (m) (B) H9).
-------- assert (* AndElim *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A)))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A)) as H17.
------------ exact H16.
------------ destruct H17 as [H17 H18].
exact H17.
------- assert (* Cut *) (A = A) as H11.
-------- apply (@logic.eq__refl (Point) A).
-------- assert (* Cut *) (euclidean__axioms.Col A B A) as H12.
--------- right.
left.
exact H11.
--------- assert (* Cut *) (euclidean__axioms.neq A m) as H13.
---------- assert (* Cut *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A B))) as H13.
----------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (m) (B) H7).
----------- assert (* AndElim *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A B))) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A B)) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
exact H16.
---------- assert (* Cut *) (euclidean__axioms.nCol A m C) as H14.
----------- apply (@euclidean__tactics.nCol__notCol (A) (m) (C)).
------------apply (@euclidean__tactics.nCol__not__Col (A) (m) (C)).
-------------apply (@lemma__NChelper.lemma__NChelper (A) (B) (C) (A) (m) (H3) (H12) (H10) H13).


----------- assert (* Cut *) (euclidean__axioms.neq m C) as H15.
------------ assert (* Cut *) ((euclidean__axioms.neq A m) /\ ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C A)))))) as H15.
------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (m) (C) H14).
------------- assert (* AndElim *) ((euclidean__axioms.neq A m) /\ ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C A)))))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C A))))) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C A)))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C A))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C A)) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
exact H18.
------------ assert (* Cut *) (euclidean__axioms.neq C m) as H16.
------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (m) (C) H15).
------------- assert (* Cut *) (exists (H17: euclidean__axioms.Point), (euclidean__axioms.BetS C m H17) /\ (euclidean__axioms.Cong m H17 m C)) as H17.
-------------- apply (@lemma__extension.lemma__extension (C) (m) (m) (C) (H16) H15).
-------------- assert (exists H18: euclidean__axioms.Point, ((euclidean__axioms.BetS C m H18) /\ (euclidean__axioms.Cong m H18 m C))) as H19.
--------------- exact H17.
--------------- destruct H19 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.BetS C m H18) /\ (euclidean__axioms.Cong m H18 m C)) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* Cut *) (euclidean__axioms.BetS B m A) as H22.
----------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (m) (B) H7).
----------------- assert (* Cut *) (euclidean__axioms.BetS C M A) as H23.
------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (M) (C) H1).
------------------ assert (* Cut *) (euclidean__axioms.Cong m B m A) as H24.
------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (m) (m) (A) (B) H8).
------------------- assert (* Cut *) (euclidean__axioms.Cong B m A m) as H25.
-------------------- assert (* Cut *) ((euclidean__axioms.Cong B m A m) /\ ((euclidean__axioms.Cong B m m A) /\ (euclidean__axioms.Cong m B A m))) as H25.
--------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (m) (B) (m) (A) H24).
--------------------- assert (* AndElim *) ((euclidean__axioms.Cong B m A m) /\ ((euclidean__axioms.Cong B m m A) /\ (euclidean__axioms.Cong m B A m))) as H26.
---------------------- exact H25.
---------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Cong B m m A) /\ (euclidean__axioms.Cong m B A m)) as H28.
----------------------- exact H27.
----------------------- destruct H28 as [H28 H29].
exact H26.
-------------------- assert (* Cut *) (euclidean__axioms.Cong m C m H18) as H26.
--------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (m) (m) (H18) (C) H21).
--------------------- assert (* Cut *) (~(euclidean__axioms.Col B A H18)) as H27.
---------------------- intro H27.
assert (* Cut *) (euclidean__axioms.Col A m B) as H28.
----------------------- exact H9.
----------------------- assert (* Cut *) (euclidean__axioms.Col B A m) as H29.
------------------------ assert (* Cut *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H29.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (m) (B) H28).
------------------------- assert (* AndElim *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A)))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A)) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
exact H34.
------------------------ assert (* Cut *) (euclidean__axioms.neq B A) as H30.
------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H4).
------------------------- assert (* Cut *) (euclidean__axioms.Col A H18 m) as H31.
-------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (H18) (m)).
---------------------------intro H31.
apply (@euclidean__tactics.Col__nCol__False (A) (H18) (m) (H31)).
----------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (H18) (m) (H27) (H29) H30).


-------------------------- assert (* Cut *) (euclidean__axioms.Col H18 m A) as H32.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col H18 A m) /\ ((euclidean__axioms.Col H18 m A) /\ ((euclidean__axioms.Col m A H18) /\ ((euclidean__axioms.Col A m H18) /\ (euclidean__axioms.Col m H18 A))))) as H32.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (H18) (m) H31).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Col H18 A m) /\ ((euclidean__axioms.Col H18 m A) /\ ((euclidean__axioms.Col m A H18) /\ ((euclidean__axioms.Col A m H18) /\ (euclidean__axioms.Col m H18 A))))) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col H18 m A) /\ ((euclidean__axioms.Col m A H18) /\ ((euclidean__axioms.Col A m H18) /\ (euclidean__axioms.Col m H18 A)))) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col m A H18) /\ ((euclidean__axioms.Col A m H18) /\ (euclidean__axioms.Col m H18 A))) as H37.
------------------------------- exact H36.
------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col A m H18) /\ (euclidean__axioms.Col m H18 A)) as H39.
-------------------------------- exact H38.
-------------------------------- destruct H39 as [H39 H40].
exact H35.
--------------------------- assert (* Cut *) (euclidean__axioms.Col C m H18) as H33.
---------------------------- right.
right.
right.
right.
left.
exact H20.
---------------------------- assert (* Cut *) (euclidean__axioms.Col H18 m C) as H34.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col m C H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))))) as H34.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (m) (H18) H33).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col m C H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C)))) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C)) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
exact H42.
----------------------------- assert (* Cut *) (euclidean__axioms.neq m H18) as H35.
------------------------------ assert (* Cut *) ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C H18))) as H35.
------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (m) (H18) H20).
------------------------------- assert (* AndElim *) ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C H18))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C H18)) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
exact H36.
------------------------------ assert (* Cut *) (euclidean__axioms.neq H18 m) as H36.
------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (m) (H18) H35).
------------------------------- assert (* Cut *) (euclidean__axioms.Col m A C) as H37.
-------------------------------- apply (@euclidean__tactics.not__nCol__Col (m) (A) (C)).
---------------------------------intro H37.
apply (@euclidean__tactics.Col__nCol__False (m) (A) (C) (H37)).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 (H18) (m) (A) (C) (H32) (H34) H36).


-------------------------------- assert (* Cut *) (euclidean__axioms.Col m A B) as H38.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B m) /\ ((euclidean__axioms.Col A m B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B m A) /\ (euclidean__axioms.Col m A B))))) as H38.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (m) H29).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B m) /\ ((euclidean__axioms.Col A m B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B m A) /\ (euclidean__axioms.Col m A B))))) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col A m B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B m A) /\ (euclidean__axioms.Col m A B)))) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B m A) /\ (euclidean__axioms.Col m A B))) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col B m A) /\ (euclidean__axioms.Col m A B)) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [H45 H46].
exact H46.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq A m) as H39.
---------------------------------- assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C A))) as H39.
----------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (M) (A) H23).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C A))) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C A)) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
exact H13.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq m A) as H40.
----------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (m) H39).
----------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H41.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col (A) (B) (C)).
-------------------------------------intro H41.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H41)).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 (m) (A) (B) (C) (H38) (H37) H40).


------------------------------------ apply (@euclidean__tactics.Col__nCol__False (A) (m) (C) (H14)).
-------------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (m) (C)).
--------------------------------------intro H42.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H3) H41).


---------------------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS B M E) /\ (euclidean__axioms.BetS H18 A E)) as H28.
----------------------- apply (@euclidean__axioms.postulate__Euclid5 (M) (B) (A) (C) (H18) (m) (H20) (H22) (H23) (H25) (H26)).
------------------------apply (@euclidean__tactics.nCol__notCol (B) (A) (H18) H27).

----------------------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS B M E) /\ (euclidean__axioms.BetS H18 A E))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [E H29].
assert (* AndElim *) ((euclidean__axioms.BetS B M E) /\ (euclidean__axioms.BetS H18 A E)) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
assert (* Cut *) (euclidean__axioms.BetS H18 m C) as H32.
-------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (m) (H18) H20).
-------------------------- assert (* Cut *) (euclidean__axioms.Col C m H18) as H33.
--------------------------- right.
right.
right.
right.
left.
exact H20.
--------------------------- assert (* Cut *) (euclidean__axioms.Col m C H18) as H34.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col m C H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))))) as H34.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (m) (H18) H33).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col m C H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))))) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C)))) as H37.
------------------------------- exact H36.
------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))) as H39.
-------------------------------- exact H38.
-------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C)) as H41.
--------------------------------- exact H40.
--------------------------------- destruct H41 as [H41 H42].
exact H35.
---------------------------- assert (* Cut *) (m = m) as H35.
----------------------------- apply (@logic.eq__refl (Point) m).
----------------------------- assert (* Cut *) (euclidean__axioms.Col m C m) as H36.
------------------------------ right.
left.
exact H35.
------------------------------ assert (* Cut *) (euclidean__axioms.nCol m C A) as H37.
------------------------------- assert (* Cut *) ((euclidean__axioms.nCol m A C) /\ ((euclidean__axioms.nCol m C A) /\ ((euclidean__axioms.nCol C A m) /\ ((euclidean__axioms.nCol A C m) /\ (euclidean__axioms.nCol C m A))))) as H37.
-------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (m) (C) H14).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol m A C) /\ ((euclidean__axioms.nCol m C A) /\ ((euclidean__axioms.nCol C A m) /\ ((euclidean__axioms.nCol A C m) /\ (euclidean__axioms.nCol C m A))))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.nCol m C A) /\ ((euclidean__axioms.nCol C A m) /\ ((euclidean__axioms.nCol A C m) /\ (euclidean__axioms.nCol C m A)))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.nCol C A m) /\ ((euclidean__axioms.nCol A C m) /\ (euclidean__axioms.nCol C m A))) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.nCol A C m) /\ (euclidean__axioms.nCol C m A)) as H44.
------------------------------------ exact H43.
------------------------------------ destruct H44 as [H44 H45].
exact H40.
------------------------------- assert (* Cut *) (euclidean__axioms.neq m H18) as H38.
-------------------------------- assert (* Cut *) ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C H18))) as H38.
--------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (m) (H18) H20).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C H18))) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C H18)) as H41.
----------------------------------- exact H40.
----------------------------------- destruct H41 as [H41 H42].
exact H39.
-------------------------------- assert (* Cut *) (euclidean__axioms.nCol m H18 A) as H39.
--------------------------------- apply (@euclidean__tactics.nCol__notCol (m) (H18) (A)).
----------------------------------apply (@euclidean__tactics.nCol__not__Col (m) (H18) (A)).
-----------------------------------apply (@lemma__NChelper.lemma__NChelper (m) (C) (A) (m) (H18) (H37) (H36) (H34) H38).


--------------------------------- assert (* Cut *) (euclidean__axioms.nCol A m H18) as H40.
---------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H18 m A) /\ ((euclidean__axioms.nCol H18 A m) /\ ((euclidean__axioms.nCol A m H18) /\ ((euclidean__axioms.nCol m A H18) /\ (euclidean__axioms.nCol A H18 m))))) as H40.
----------------------------------- apply (@lemma__NCorder.lemma__NCorder (m) (H18) (A) H39).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol H18 m A) /\ ((euclidean__axioms.nCol H18 A m) /\ ((euclidean__axioms.nCol A m H18) /\ ((euclidean__axioms.nCol m A H18) /\ (euclidean__axioms.nCol A H18 m))))) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.nCol H18 A m) /\ ((euclidean__axioms.nCol A m H18) /\ ((euclidean__axioms.nCol m A H18) /\ (euclidean__axioms.nCol A H18 m)))) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol A m H18) /\ ((euclidean__axioms.nCol m A H18) /\ (euclidean__axioms.nCol A H18 m))) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.nCol m A H18) /\ (euclidean__axioms.nCol A H18 m)) as H47.
--------------------------------------- exact H46.
--------------------------------------- destruct H47 as [H47 H48].
exact H45.
---------------------------------- assert (* Cut *) (euclidean__defs.CongA A m H18 C m B) as H41.
----------------------------------- apply (@proposition__15.proposition__15a (A) (B) (H18) (C) (m) (H7) (H32) H40).
----------------------------------- assert (* Cut *) (euclidean__axioms.nCol H18 m A) as H42.
------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol m A H18) /\ ((euclidean__axioms.nCol m H18 A) /\ ((euclidean__axioms.nCol H18 A m) /\ ((euclidean__axioms.nCol A H18 m) /\ (euclidean__axioms.nCol H18 m A))))) as H42.
------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (m) (H18) H40).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol m A H18) /\ ((euclidean__axioms.nCol m H18 A) /\ ((euclidean__axioms.nCol H18 A m) /\ ((euclidean__axioms.nCol A H18 m) /\ (euclidean__axioms.nCol H18 m A))))) as H43.
-------------------------------------- exact H42.
-------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol m H18 A) /\ ((euclidean__axioms.nCol H18 A m) /\ ((euclidean__axioms.nCol A H18 m) /\ (euclidean__axioms.nCol H18 m A)))) as H45.
--------------------------------------- exact H44.
--------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.nCol H18 A m) /\ ((euclidean__axioms.nCol A H18 m) /\ (euclidean__axioms.nCol H18 m A))) as H47.
---------------------------------------- exact H46.
---------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.nCol A H18 m) /\ (euclidean__axioms.nCol H18 m A)) as H49.
----------------------------------------- exact H48.
----------------------------------------- destruct H49 as [H49 H50].
exact H50.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col A m B) as H43.
------------------------------------- exact H9.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B m) as H44.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H44.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (m) (B) H43).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H45.
---------------------------------------- exact H44.
---------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A)))) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A)) as H51.
------------------------------------------- exact H50.
------------------------------------------- destruct H51 as [H51 H52].
exact H51.
-------------------------------------- assert (* Cut *) (B = B) as H45.
--------------------------------------- apply (@logic.eq__refl (Point) B).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H46.
---------------------------------------- right.
right.
left.
exact H45.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq m B) as H47.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A B))) as H47.
------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (m) (B) H7).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A B))) as H48.
------------------------------------------- exact H47.
------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A B)) as H50.
-------------------------------------------- exact H49.
-------------------------------------------- destruct H50 as [H50 H51].
exact H48.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol m B C) as H48.
------------------------------------------ apply (@euclidean__tactics.nCol__notCol (m) (B) (C)).
-------------------------------------------apply (@euclidean__tactics.nCol__not__Col (m) (B) (C)).
--------------------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (B) (C) (m) (B) (H3) (H44) (H46) H47).


------------------------------------------ assert (* Cut *) (euclidean__defs.CongA H18 m A A m H18) as H49.
------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (H18) (m) (A) H42).
------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H18 m A C m B) as H50.
-------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (H18) (m) (A) (A) (m) (H18) (C) (m) (B) (H49) H41).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong m A m B) as H51.
--------------------------------------------- exact H8.
--------------------------------------------- assert (* Cut *) (euclidean__defs.CongA m H18 A m C B) as H52.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong m H18 m C) -> ((euclidean__axioms.Cong m A m B) -> ((euclidean__defs.CongA H18 m A C m B) -> ((euclidean__defs.CongA m H18 A m C B) /\ (euclidean__defs.CongA m A H18 m B C))))) as H52.
----------------------------------------------- intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong H18 A C B) /\ ((euclidean__defs.CongA m H18 A m C B) /\ (euclidean__defs.CongA m A H18 m B C))) as __2.
------------------------------------------------ apply (@proposition__04.proposition__04 (m) (H18) (A) (m) (C) (B) (__) (__0) __1).
------------------------------------------------ destruct __2 as [__2 __3].
exact __3.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong m H18 m C) -> ((euclidean__axioms.Cong m A m B) -> ((euclidean__defs.CongA H18 m A C m B) -> (euclidean__defs.CongA m H18 A m C B)))) as H53.
------------------------------------------------ intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA m H18 A m C B) /\ (euclidean__defs.CongA m A H18 m B C)) as __2.
------------------------------------------------- apply (@H52 (__) (__0) __1).
------------------------------------------------- destruct __2 as [__2 __3].
exact __2.
------------------------------------------------ apply (@H53 (H21) (H51) H50).
---------------------------------------------- assert (* Cut *) (B = B) as H53.
----------------------------------------------- exact H45.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H54.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq B m) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C m)))))) as H54.
------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (m) (B) (C) H48).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq B m) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C m)))))) as H55.
-------------------------------------------------- exact H54.
-------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq B m) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C m))))) as H57.
--------------------------------------------------- exact H56.
--------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq B m) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C m)))) as H59.
---------------------------------------------------- exact H58.
---------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.neq B m) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C m))) as H61.
----------------------------------------------------- exact H60.
----------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C m)) as H63.
------------------------------------------------------ exact H62.
------------------------------------------------------ destruct H63 as [H63 H64].
exact H57.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C B) as H55.
------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H54).
------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C B B) as H56.
-------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (B) (B)).
---------------------------------------------------right.
left.
exact H53.

--------------------------------------------------- exact H55.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C m H18) as H57.
--------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (m) (H18)).
----------------------------------------------------right.
right.
exact H20.

---------------------------------------------------- exact H16.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA m H18 A H18 C B) as H58.
---------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (m) (H18) (A) (m) (C) (B) (H18) (B) (H52) (H57) H56).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H18 C B m H18 A) as H59.
----------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (m) (H18) (A) (H18) (C) (B) H58).
----------------------------------------------------- assert (* Cut *) (A = A) as H60.
------------------------------------------------------ exact H11.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq H18 A) as H61.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H18 m) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A H18)))))) as H61.
-------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (H18) (m) (A) H42).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H18 m) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A H18)))))) as H62.
--------------------------------------------------------- exact H61.
--------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A H18))))) as H64.
---------------------------------------------------------- exact H63.
---------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A H18)))) as H66.
----------------------------------------------------------- exact H65.
----------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A H18))) as H68.
------------------------------------------------------------ exact H67.
------------------------------------------------------------ destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A H18)) as H70.
------------------------------------------------------------- exact H69.
------------------------------------------------------------- destruct H70 as [H70 H71].
exact H66.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out H18 A A) as H62.
-------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (H18) (A) (A)).
---------------------------------------------------------right.
left.
exact H60.

--------------------------------------------------------- exact H61.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS H18 m C) as H63.
--------------------------------------------------------- exact H32.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H18 m) as H64.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq H18 m) /\ (euclidean__axioms.neq H18 C))) as H64.
----------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (H18) (m) (C) H63).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq H18 m) /\ (euclidean__axioms.neq H18 C))) as H65.
------------------------------------------------------------ exact H64.
------------------------------------------------------------ destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.neq H18 m) /\ (euclidean__axioms.neq H18 C)) as H67.
------------------------------------------------------------- exact H66.
------------------------------------------------------------- destruct H67 as [H67 H68].
exact H67.
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out H18 m C) as H65.
----------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (H18) (m) (C)).
------------------------------------------------------------right.
right.
exact H63.

------------------------------------------------------------ exact H64.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H18 C B C H18 A) as H66.
------------------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper (H18) (C) (B) (m) (H18) (A) (C) (A) (H59) (H65) H62).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C H18 A H18 C B) as H67.
------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (H18) (C) (B) (C) (H18) (A) H66).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A H18 C B C H18) as H68.
-------------------------------------------------------------- apply (@lemma__equalanglesflip.lemma__equalanglesflip (C) (H18) (A) (H18) (C) (B) H67).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C H18) as H69.
--------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (B) (C) (H18)).
----------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (B) (C) (H18)).
-----------------------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (H18) (C) (B) (C) (H18) H68).


--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C H18 H18 C B) as H70.
---------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (C) (H18) H69).
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A H18 C H18 C B) as H71.
----------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (H18) (C) (B) (C) (H18) (H18) (C) (B) (H68) H70).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C m H18) as H72.
------------------------------------------------------------------ exact H33.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H18 C m) as H73.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m C H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))))) as H73.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (m) (H18) H72).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m C H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))))) as H74.
--------------------------------------------------------------------- exact H73.
--------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C)))) as H76.
---------------------------------------------------------------------- exact H75.
---------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))) as H78.
----------------------------------------------------------------------- exact H77.
----------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C)) as H80.
------------------------------------------------------------------------ exact H79.
------------------------------------------------------------------------ destruct H80 as [H80 H81].
exact H78.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H18 m C) as H74.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C H18 m) /\ ((euclidean__axioms.Col C m H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 m C) /\ (euclidean__axioms.Col m C H18))))) as H74.
--------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H18) (C) (m) H73).
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C H18 m) /\ ((euclidean__axioms.Col C m H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 m C) /\ (euclidean__axioms.Col m C H18))))) as H75.
---------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col C m H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 m C) /\ (euclidean__axioms.Col m C H18)))) as H77.
----------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 m C) /\ (euclidean__axioms.Col m C H18))) as H79.
------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------ destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col H18 m C) /\ (euclidean__axioms.Col m C H18)) as H81.
------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H81.
-------------------------------------------------------------------- assert (* Cut *) (H18 = H18) as H75.
--------------------------------------------------------------------- apply (@logic.eq__refl (Point) H18).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H18 m H18) as H76.
---------------------------------------------------------------------- right.
left.
exact H75.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H18 C) as H77.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq H18 m) /\ (euclidean__axioms.neq H18 C))) as H77.
------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (H18) (m) (C) H63).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq H18 m) /\ (euclidean__axioms.neq H18 C))) as H78.
------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.neq H18 m) /\ (euclidean__axioms.neq H18 C)) as H80.
-------------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------------- destruct H80 as [H80 H81].
exact H81.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H18 C A) as H78.
------------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (H18) (C) (A)).
-------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (H18) (C) (A)).
--------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (H18) (m) (A) (H18) (C) (H42) (H76) (H74) H77).


------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS A H18 C B) as H79.
------------------------------------------------------------------------- exists m.
split.
-------------------------------------------------------------------------- exact H7.
-------------------------------------------------------------------------- split.
--------------------------------------------------------------------------- exact H73.
--------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A H18 C B) as H80.
-------------------------------------------------------------------------- apply (@proposition__27B.proposition__27B (A) (B) (H18) (C) (H71) H79).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H18 A E) as H81.
--------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H31.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H18 E) as H82.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A H18 E) /\ ((euclidean__axioms.Col A E H18) /\ ((euclidean__axioms.Col E H18 A) /\ ((euclidean__axioms.Col H18 E A) /\ (euclidean__axioms.Col E A H18))))) as H82.
----------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H18) (A) (E) H81).
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A H18 E) /\ ((euclidean__axioms.Col A E H18) /\ ((euclidean__axioms.Col E H18 A) /\ ((euclidean__axioms.Col H18 E A) /\ (euclidean__axioms.Col E A H18))))) as H83.
------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col A E H18) /\ ((euclidean__axioms.Col E H18 A) /\ ((euclidean__axioms.Col H18 E A) /\ (euclidean__axioms.Col E A H18)))) as H85.
------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col E H18 A) /\ ((euclidean__axioms.Col H18 E A) /\ (euclidean__axioms.Col E A H18))) as H87.
-------------------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col H18 E A) /\ (euclidean__axioms.Col E A H18)) as H89.
--------------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------------- destruct H89 as [H89 H90].
exact H83.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H18 A) as H83.
----------------------------------------------------------------------------- right.
left.
exact H60.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H84.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq H18 A) /\ (euclidean__axioms.neq H18 E))) as H84.
------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (H18) (A) (E) H31).
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq H18 A) /\ (euclidean__axioms.neq H18 E))) as H85.
-------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.neq H18 A) /\ (euclidean__axioms.neq H18 E)) as H87.
--------------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------------- destruct H87 as [H87 H88].
exact H85.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par C B A H18) as H85.
------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (H18) (C) (B) H80).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C B A E) as H86.
-------------------------------------------------------------------------------- apply (@lemma__collinearparallel2.lemma__collinearparallel2 (C) (B) (A) (H18) (A) (E) (H85) (H83) (H82) H84).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A E C B) as H87.
--------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (C) (B) (A) (E) H86).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A E B C) as H88.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par E A C B) /\ ((euclidean__defs.Par A E B C) /\ (euclidean__defs.Par E A B C))) as H88.
----------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (E) (C) (B) H87).
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E A C B) /\ ((euclidean__defs.Par A E B C) /\ (euclidean__defs.Par E A B C))) as H89.
------------------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------------------ destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__defs.Par A E B C) /\ (euclidean__defs.Par E A B C)) as H91.
------------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
exact H91.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B C E B C) as H89.
----------------------------------------------------------------------------------- apply (@proposition__37.proposition__37 (A) (B) (C) (E) H88).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D B C A B C) as H90.
------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric (A) (B) (C) (D) (B) (C) H0).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET D B C E B C) as H91.
------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETtransitive (D) (B) (C) (E) (B) (C) (A) (B) (C) (H90) H89).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B M D) as H92.
-------------------------------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (B) (D) (M) H2).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B M) as H93.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B E))) as H93.
---------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (M) (E) H30).
---------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B E))) as H94.
----------------------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B E)) as H96.
------------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------------ destruct H96 as [H96 H97].
exact H96.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B M E) as H94.
---------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (M) (E)).
-----------------------------------------------------------------------------------------right.
right.
exact H30.

----------------------------------------------------------------------------------------- exact H93.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B D E) as H95.
----------------------------------------------------------------------------------------- apply (@lemma__ray3.lemma__ray3 (B) (M) (D) (E) (H92) H94).
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS B E D) \/ ((D = E) \/ (euclidean__axioms.BetS B D E))) as H96.
------------------------------------------------------------------------------------------ apply (@lemma__ray1.lemma__ray1 (B) (D) (E) H95).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par A D B C) as H97.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS B E D) \/ ((D = E) \/ (euclidean__axioms.BetS B D E))) as H97.
-------------------------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS B E D) \/ ((D = E) \/ (euclidean__axioms.BetS B D E))) as __TmpHyp.
--------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------- assert (euclidean__axioms.BetS B E D \/ (D = E) \/ (euclidean__axioms.BetS B D E)) as H98.
---------------------------------------------------------------------------------------------- exact __TmpHyp.
---------------------------------------------------------------------------------------------- destruct H98 as [H98|H98].
----------------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Par A D B C))) as H99.
------------------------------------------------------------------------------------------------ intro H99.
assert (* Cut *) (~(euclidean__axioms.ET D B C E B C)) as H100.
------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__deZolt1 (B) (C) (D) (E) H98).
------------------------------------------------------------------------------------------------- apply (@H27).
--------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (H18)).
---------------------------------------------------------------------------------------------------intro H101.
apply (@H100 H91).


------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Par A D B C)).
-------------------------------------------------------------------------------------------------intro H100.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H101.
-------------------------------------------------------------------------------------------------- exact H3.
-------------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.neq A m) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq m C) /\ ((~(euclidean__axioms.BetS A m C)) /\ ((~(euclidean__axioms.BetS A C m)) /\ (~(euclidean__axioms.BetS m A C))))))) as H103.
--------------------------------------------------------------------------------------------------- exact H14.
--------------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS m C A)) /\ ((~(euclidean__axioms.BetS m A C)) /\ (~(euclidean__axioms.BetS C m A))))))) as H105.
---------------------------------------------------------------------------------------------------- exact H37.
---------------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq H18 A) /\ ((~(euclidean__axioms.BetS m H18 A)) /\ ((~(euclidean__axioms.BetS m A H18)) /\ (~(euclidean__axioms.BetS H18 m A))))))) as H107.
----------------------------------------------------------------------------------------------------- exact H39.
----------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.neq A m) /\ ((euclidean__axioms.neq A H18) /\ ((euclidean__axioms.neq m H18) /\ ((~(euclidean__axioms.BetS A m H18)) /\ ((~(euclidean__axioms.BetS A H18 m)) /\ (~(euclidean__axioms.BetS m A H18))))))) as H109.
------------------------------------------------------------------------------------------------------ exact H40.
------------------------------------------------------------------------------------------------------ destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq H18 m) /\ ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq m A) /\ ((~(euclidean__axioms.BetS H18 m A)) /\ ((~(euclidean__axioms.BetS H18 A m)) /\ (~(euclidean__axioms.BetS m H18 A))))))) as H111.
------------------------------------------------------------------------------------------------------- exact H42.
------------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS m B C)) /\ ((~(euclidean__axioms.BetS m C B)) /\ (~(euclidean__axioms.BetS B m C))))))) as H113.
-------------------------------------------------------------------------------------------------------- exact H48.
-------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B H18) /\ ((euclidean__axioms.neq C H18) /\ ((~(euclidean__axioms.BetS B C H18)) /\ ((~(euclidean__axioms.BetS B H18 C)) /\ (~(euclidean__axioms.BetS C B H18))))))) as H115.
--------------------------------------------------------------------------------------------------------- exact H69.
--------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.neq H18 C) /\ ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS H18 C A)) /\ ((~(euclidean__axioms.BetS H18 A C)) /\ (~(euclidean__axioms.BetS C H18 A))))))) as H117.
---------------------------------------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H119.
----------------------------------------------------------------------------------------------------------- exact H102.
----------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq m C) /\ ((~(euclidean__axioms.BetS A m C)) /\ ((~(euclidean__axioms.BetS A C m)) /\ (~(euclidean__axioms.BetS m A C)))))) as H121.
------------------------------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------------------------------ destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS m C A)) /\ ((~(euclidean__axioms.BetS m A C)) /\ (~(euclidean__axioms.BetS C m A)))))) as H123.
------------------------------------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq H18 A) /\ ((~(euclidean__axioms.BetS m H18 A)) /\ ((~(euclidean__axioms.BetS m A H18)) /\ (~(euclidean__axioms.BetS H18 m A)))))) as H125.
-------------------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.neq A H18) /\ ((euclidean__axioms.neq m H18) /\ ((~(euclidean__axioms.BetS A m H18)) /\ ((~(euclidean__axioms.BetS A H18 m)) /\ (~(euclidean__axioms.BetS m A H18)))))) as H127.
--------------------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq m A) /\ ((~(euclidean__axioms.BetS H18 m A)) /\ ((~(euclidean__axioms.BetS H18 A m)) /\ (~(euclidean__axioms.BetS m H18 A)))))) as H129.
---------------------------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS m B C)) /\ ((~(euclidean__axioms.BetS m C B)) /\ (~(euclidean__axioms.BetS B m C)))))) as H131.
----------------------------------------------------------------------------------------------------------------- exact H114.
----------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.neq B H18) /\ ((euclidean__axioms.neq C H18) /\ ((~(euclidean__axioms.BetS B C H18)) /\ ((~(euclidean__axioms.BetS B H18 C)) /\ (~(euclidean__axioms.BetS C B H18)))))) as H133.
------------------------------------------------------------------------------------------------------------------ exact H116.
------------------------------------------------------------------------------------------------------------------ destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS H18 C A)) /\ ((~(euclidean__axioms.BetS H18 A C)) /\ (~(euclidean__axioms.BetS C H18 A)))))) as H135.
------------------------------------------------------------------------------------------------------------------- exact H118.
------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H137.
-------------------------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.neq m C) /\ ((~(euclidean__axioms.BetS A m C)) /\ ((~(euclidean__axioms.BetS A C m)) /\ (~(euclidean__axioms.BetS m A C))))) as H139.
--------------------------------------------------------------------------------------------------------------------- exact H122.
--------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS m C A)) /\ ((~(euclidean__axioms.BetS m A C)) /\ (~(euclidean__axioms.BetS C m A))))) as H141.
---------------------------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.neq H18 A) /\ ((~(euclidean__axioms.BetS m H18 A)) /\ ((~(euclidean__axioms.BetS m A H18)) /\ (~(euclidean__axioms.BetS H18 m A))))) as H143.
----------------------------------------------------------------------------------------------------------------------- exact H126.
----------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.neq m H18) /\ ((~(euclidean__axioms.BetS A m H18)) /\ ((~(euclidean__axioms.BetS A H18 m)) /\ (~(euclidean__axioms.BetS m A H18))))) as H145.
------------------------------------------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------------------------------------------ destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.neq m A) /\ ((~(euclidean__axioms.BetS H18 m A)) /\ ((~(euclidean__axioms.BetS H18 A m)) /\ (~(euclidean__axioms.BetS m H18 A))))) as H147.
------------------------------------------------------------------------------------------------------------------------- exact H130.
------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS m B C)) /\ ((~(euclidean__axioms.BetS m C B)) /\ (~(euclidean__axioms.BetS B m C))))) as H149.
-------------------------------------------------------------------------------------------------------------------------- exact H132.
-------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.neq C H18) /\ ((~(euclidean__axioms.BetS B C H18)) /\ ((~(euclidean__axioms.BetS B H18 C)) /\ (~(euclidean__axioms.BetS C B H18))))) as H151.
--------------------------------------------------------------------------------------------------------------------------- exact H134.
--------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS H18 C A)) /\ ((~(euclidean__axioms.BetS H18 A C)) /\ (~(euclidean__axioms.BetS C H18 A))))) as H153.
---------------------------------------------------------------------------------------------------------------------------- exact H136.
---------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H155.
----------------------------------------------------------------------------------------------------------------------------- exact H138.
----------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((~(euclidean__axioms.BetS A m C)) /\ ((~(euclidean__axioms.BetS A C m)) /\ (~(euclidean__axioms.BetS m A C)))) as H157.
------------------------------------------------------------------------------------------------------------------------------ exact H140.
------------------------------------------------------------------------------------------------------------------------------ destruct H157 as [H157 H158].
assert (* AndElim *) ((~(euclidean__axioms.BetS m C A)) /\ ((~(euclidean__axioms.BetS m A C)) /\ (~(euclidean__axioms.BetS C m A)))) as H159.
------------------------------------------------------------------------------------------------------------------------------- exact H142.
------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((~(euclidean__axioms.BetS m H18 A)) /\ ((~(euclidean__axioms.BetS m A H18)) /\ (~(euclidean__axioms.BetS H18 m A)))) as H161.
-------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((~(euclidean__axioms.BetS A m H18)) /\ ((~(euclidean__axioms.BetS A H18 m)) /\ (~(euclidean__axioms.BetS m A H18)))) as H163.
--------------------------------------------------------------------------------------------------------------------------------- exact H146.
--------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
assert (* AndElim *) ((~(euclidean__axioms.BetS H18 m A)) /\ ((~(euclidean__axioms.BetS H18 A m)) /\ (~(euclidean__axioms.BetS m H18 A)))) as H165.
---------------------------------------------------------------------------------------------------------------------------------- exact H148.
---------------------------------------------------------------------------------------------------------------------------------- destruct H165 as [H165 H166].
assert (* AndElim *) ((~(euclidean__axioms.BetS m B C)) /\ ((~(euclidean__axioms.BetS m C B)) /\ (~(euclidean__axioms.BetS B m C)))) as H167.
----------------------------------------------------------------------------------------------------------------------------------- exact H150.
----------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C H18)) /\ ((~(euclidean__axioms.BetS B H18 C)) /\ (~(euclidean__axioms.BetS C B H18)))) as H169.
------------------------------------------------------------------------------------------------------------------------------------ exact H152.
------------------------------------------------------------------------------------------------------------------------------------ destruct H169 as [H169 H170].
assert (* AndElim *) ((~(euclidean__axioms.BetS H18 C A)) /\ ((~(euclidean__axioms.BetS H18 A C)) /\ (~(euclidean__axioms.BetS C H18 A)))) as H171.
------------------------------------------------------------------------------------------------------------------------------------- exact H154.
------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H173.
-------------------------------------------------------------------------------------------------------------------------------------- exact H156.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C m)) /\ (~(euclidean__axioms.BetS m A C))) as H175.
--------------------------------------------------------------------------------------------------------------------------------------- exact H158.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((~(euclidean__axioms.BetS m A C)) /\ (~(euclidean__axioms.BetS C m A))) as H177.
---------------------------------------------------------------------------------------------------------------------------------------- exact H160.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H177 H178].
assert (* AndElim *) ((~(euclidean__axioms.BetS m A H18)) /\ (~(euclidean__axioms.BetS H18 m A))) as H179.
----------------------------------------------------------------------------------------------------------------------------------------- exact H162.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((~(euclidean__axioms.BetS A H18 m)) /\ (~(euclidean__axioms.BetS m A H18))) as H181.
------------------------------------------------------------------------------------------------------------------------------------------ exact H164.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H181 as [H181 H182].
assert (* AndElim *) ((~(euclidean__axioms.BetS H18 A m)) /\ (~(euclidean__axioms.BetS m H18 A))) as H183.
------------------------------------------------------------------------------------------------------------------------------------------- exact H166.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* AndElim *) ((~(euclidean__axioms.BetS m C B)) /\ (~(euclidean__axioms.BetS B m C))) as H185.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H168.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((~(euclidean__axioms.BetS B H18 C)) /\ (~(euclidean__axioms.BetS C B H18))) as H187.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H170.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((~(euclidean__axioms.BetS H18 A C)) /\ (~(euclidean__axioms.BetS C H18 A))) as H189.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* Cut *) (False) as H191.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@H99 H100).
----------------------------------------------------------------------------------------------------------------------------------------------- assert False.
------------------------------------------------------------------------------------------------------------------------------------------------exact H191.
------------------------------------------------------------------------------------------------------------------------------------------------ contradiction.

----------------------------------------------------------------------------------------------- assert (D = E \/ euclidean__axioms.BetS B D E) as H99.
------------------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------------------ destruct H99 as [H99|H99].
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A D B C) as H100.
-------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0: euclidean__axioms.Point => (euclidean__axioms.ET A B C D0 B C) -> ((euclidean__defs.Out B D0 M) -> ((euclidean__axioms.ET D0 B C A B C) -> ((euclidean__axioms.ET D0 B C E B C) -> ((euclidean__defs.Out B M D0) -> ((euclidean__defs.Out B D0 E) -> (euclidean__defs.Par A D0 B C)))))))) with (x := D).
---------------------------------------------------------------------------------------------------intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
exact H88.

--------------------------------------------------------------------------------------------------- exact H99.
--------------------------------------------------------------------------------------------------- exact H0.
--------------------------------------------------------------------------------------------------- exact H2.
--------------------------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Par A D B C))) as H100.
-------------------------------------------------------------------------------------------------- intro H100.
assert (* Cut *) (~(euclidean__axioms.ET E B C D B C)) as H101.
--------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__deZolt1 (B) (C) (E) (D) H99).
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET E B C D B C) as H102.
---------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (D) (B) (C) (E) (B) (C) H91).
---------------------------------------------------------------------------------------------------- apply (@H27).
-----------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (B) (A) (H18)).
------------------------------------------------------------------------------------------------------intro H103.
apply (@H101 H102).


-------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Par A D B C)).
---------------------------------------------------------------------------------------------------intro H101.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H102.
---------------------------------------------------------------------------------------------------- exact H3.
---------------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.neq A m) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq m C) /\ ((~(euclidean__axioms.BetS A m C)) /\ ((~(euclidean__axioms.BetS A C m)) /\ (~(euclidean__axioms.BetS m A C))))))) as H104.
----------------------------------------------------------------------------------------------------- exact H14.
----------------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS m C A)) /\ ((~(euclidean__axioms.BetS m A C)) /\ (~(euclidean__axioms.BetS C m A))))))) as H106.
------------------------------------------------------------------------------------------------------ exact H37.
------------------------------------------------------------------------------------------------------ destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq H18 A) /\ ((~(euclidean__axioms.BetS m H18 A)) /\ ((~(euclidean__axioms.BetS m A H18)) /\ (~(euclidean__axioms.BetS H18 m A))))))) as H108.
------------------------------------------------------------------------------------------------------- exact H39.
------------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.neq A m) /\ ((euclidean__axioms.neq A H18) /\ ((euclidean__axioms.neq m H18) /\ ((~(euclidean__axioms.BetS A m H18)) /\ ((~(euclidean__axioms.BetS A H18 m)) /\ (~(euclidean__axioms.BetS m A H18))))))) as H110.
-------------------------------------------------------------------------------------------------------- exact H40.
-------------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.neq H18 m) /\ ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq m A) /\ ((~(euclidean__axioms.BetS H18 m A)) /\ ((~(euclidean__axioms.BetS H18 A m)) /\ (~(euclidean__axioms.BetS m H18 A))))))) as H112.
--------------------------------------------------------------------------------------------------------- exact H42.
--------------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS m B C)) /\ ((~(euclidean__axioms.BetS m C B)) /\ (~(euclidean__axioms.BetS B m C))))))) as H114.
---------------------------------------------------------------------------------------------------------- exact H48.
---------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B H18) /\ ((euclidean__axioms.neq C H18) /\ ((~(euclidean__axioms.BetS B C H18)) /\ ((~(euclidean__axioms.BetS B H18 C)) /\ (~(euclidean__axioms.BetS C B H18))))))) as H116.
----------------------------------------------------------------------------------------------------------- exact H69.
----------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.neq H18 C) /\ ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS H18 C A)) /\ ((~(euclidean__axioms.BetS H18 A C)) /\ (~(euclidean__axioms.BetS C H18 A))))))) as H118.
------------------------------------------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------------------------------------------ destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H120.
------------------------------------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq m C) /\ ((~(euclidean__axioms.BetS A m C)) /\ ((~(euclidean__axioms.BetS A C m)) /\ (~(euclidean__axioms.BetS m A C)))))) as H122.
-------------------------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS m C A)) /\ ((~(euclidean__axioms.BetS m A C)) /\ (~(euclidean__axioms.BetS C m A)))))) as H124.
--------------------------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq H18 A) /\ ((~(euclidean__axioms.BetS m H18 A)) /\ ((~(euclidean__axioms.BetS m A H18)) /\ (~(euclidean__axioms.BetS H18 m A)))))) as H126.
---------------------------------------------------------------------------------------------------------------- exact H109.
---------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.neq A H18) /\ ((euclidean__axioms.neq m H18) /\ ((~(euclidean__axioms.BetS A m H18)) /\ ((~(euclidean__axioms.BetS A H18 m)) /\ (~(euclidean__axioms.BetS m A H18)))))) as H128.
----------------------------------------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq m A) /\ ((~(euclidean__axioms.BetS H18 m A)) /\ ((~(euclidean__axioms.BetS H18 A m)) /\ (~(euclidean__axioms.BetS m H18 A)))))) as H130.
------------------------------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------------------------------ destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS m B C)) /\ ((~(euclidean__axioms.BetS m C B)) /\ (~(euclidean__axioms.BetS B m C)))))) as H132.
------------------------------------------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.neq B H18) /\ ((euclidean__axioms.neq C H18) /\ ((~(euclidean__axioms.BetS B C H18)) /\ ((~(euclidean__axioms.BetS B H18 C)) /\ (~(euclidean__axioms.BetS C B H18)))))) as H134.
-------------------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS H18 C A)) /\ ((~(euclidean__axioms.BetS H18 A C)) /\ (~(euclidean__axioms.BetS C H18 A)))))) as H136.
--------------------------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H138.
---------------------------------------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.neq m C) /\ ((~(euclidean__axioms.BetS A m C)) /\ ((~(euclidean__axioms.BetS A C m)) /\ (~(euclidean__axioms.BetS m A C))))) as H140.
----------------------------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS m C A)) /\ ((~(euclidean__axioms.BetS m A C)) /\ (~(euclidean__axioms.BetS C m A))))) as H142.
------------------------------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------------------------------ destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.neq H18 A) /\ ((~(euclidean__axioms.BetS m H18 A)) /\ ((~(euclidean__axioms.BetS m A H18)) /\ (~(euclidean__axioms.BetS H18 m A))))) as H144.
------------------------------------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.neq m H18) /\ ((~(euclidean__axioms.BetS A m H18)) /\ ((~(euclidean__axioms.BetS A H18 m)) /\ (~(euclidean__axioms.BetS m A H18))))) as H146.
-------------------------------------------------------------------------------------------------------------------------- exact H129.
-------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.neq m A) /\ ((~(euclidean__axioms.BetS H18 m A)) /\ ((~(euclidean__axioms.BetS H18 A m)) /\ (~(euclidean__axioms.BetS m H18 A))))) as H148.
--------------------------------------------------------------------------------------------------------------------------- exact H131.
--------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS m B C)) /\ ((~(euclidean__axioms.BetS m C B)) /\ (~(euclidean__axioms.BetS B m C))))) as H150.
---------------------------------------------------------------------------------------------------------------------------- exact H133.
---------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.neq C H18) /\ ((~(euclidean__axioms.BetS B C H18)) /\ ((~(euclidean__axioms.BetS B H18 C)) /\ (~(euclidean__axioms.BetS C B H18))))) as H152.
----------------------------------------------------------------------------------------------------------------------------- exact H135.
----------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((~(euclidean__axioms.BetS H18 C A)) /\ ((~(euclidean__axioms.BetS H18 A C)) /\ (~(euclidean__axioms.BetS C H18 A))))) as H154.
------------------------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------------------------ destruct H154 as [H154 H155].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H156.
------------------------------------------------------------------------------------------------------------------------------- exact H139.
------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((~(euclidean__axioms.BetS A m C)) /\ ((~(euclidean__axioms.BetS A C m)) /\ (~(euclidean__axioms.BetS m A C)))) as H158.
-------------------------------------------------------------------------------------------------------------------------------- exact H141.
-------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((~(euclidean__axioms.BetS m C A)) /\ ((~(euclidean__axioms.BetS m A C)) /\ (~(euclidean__axioms.BetS C m A)))) as H160.
--------------------------------------------------------------------------------------------------------------------------------- exact H143.
--------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((~(euclidean__axioms.BetS m H18 A)) /\ ((~(euclidean__axioms.BetS m A H18)) /\ (~(euclidean__axioms.BetS H18 m A)))) as H162.
---------------------------------------------------------------------------------------------------------------------------------- exact H145.
---------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((~(euclidean__axioms.BetS A m H18)) /\ ((~(euclidean__axioms.BetS A H18 m)) /\ (~(euclidean__axioms.BetS m A H18)))) as H164.
----------------------------------------------------------------------------------------------------------------------------------- exact H147.
----------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((~(euclidean__axioms.BetS H18 m A)) /\ ((~(euclidean__axioms.BetS H18 A m)) /\ (~(euclidean__axioms.BetS m H18 A)))) as H166.
------------------------------------------------------------------------------------------------------------------------------------ exact H149.
------------------------------------------------------------------------------------------------------------------------------------ destruct H166 as [H166 H167].
assert (* AndElim *) ((~(euclidean__axioms.BetS m B C)) /\ ((~(euclidean__axioms.BetS m C B)) /\ (~(euclidean__axioms.BetS B m C)))) as H168.
------------------------------------------------------------------------------------------------------------------------------------- exact H151.
------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C H18)) /\ ((~(euclidean__axioms.BetS B H18 C)) /\ (~(euclidean__axioms.BetS C B H18)))) as H170.
-------------------------------------------------------------------------------------------------------------------------------------- exact H153.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((~(euclidean__axioms.BetS H18 C A)) /\ ((~(euclidean__axioms.BetS H18 A C)) /\ (~(euclidean__axioms.BetS C H18 A)))) as H172.
--------------------------------------------------------------------------------------------------------------------------------------- exact H155.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H174.
---------------------------------------------------------------------------------------------------------------------------------------- exact H157.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C m)) /\ (~(euclidean__axioms.BetS m A C))) as H176.
----------------------------------------------------------------------------------------------------------------------------------------- exact H159.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((~(euclidean__axioms.BetS m A C)) /\ (~(euclidean__axioms.BetS C m A))) as H178.
------------------------------------------------------------------------------------------------------------------------------------------ exact H161.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H178 as [H178 H179].
assert (* AndElim *) ((~(euclidean__axioms.BetS m A H18)) /\ (~(euclidean__axioms.BetS H18 m A))) as H180.
------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H180 H181].
assert (* AndElim *) ((~(euclidean__axioms.BetS A H18 m)) /\ (~(euclidean__axioms.BetS m A H18))) as H182.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H165.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H182 H183].
assert (* AndElim *) ((~(euclidean__axioms.BetS H18 A m)) /\ (~(euclidean__axioms.BetS m H18 A))) as H184.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H184 H185].
assert (* AndElim *) ((~(euclidean__axioms.BetS m C B)) /\ (~(euclidean__axioms.BetS B m C))) as H186.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H169.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H186 H187].
assert (* AndElim *) ((~(euclidean__axioms.BetS B H18 C)) /\ (~(euclidean__axioms.BetS C B H18))) as H188.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H171.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((~(euclidean__axioms.BetS H18 A C)) /\ (~(euclidean__axioms.BetS C H18 A))) as H190.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H173.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H190 as [H190 H191].
assert (* Cut *) (False) as H192.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H100 H101).
------------------------------------------------------------------------------------------------------------------------------------------------- assert False.
--------------------------------------------------------------------------------------------------------------------------------------------------exact H192.
-------------------------------------------------------------------------------------------------------------------------------------------------- contradiction.

------------------------------------------------------------------------------------------- exact H97.
Qed.
