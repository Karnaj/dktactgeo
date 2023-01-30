Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__doublereverse.
Require Export lemma__equalanglessymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export lemma__ray4.
Require Export lemma__rightangleNC.
Require Export logic.
Require Export proposition__16.
Require Export proposition__19.
Definition lemma__legsmallerhypotenuse : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__defs.Per A B C) -> ((euclidean__defs.Lt A B A C) /\ (euclidean__defs.Lt B C A C)).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (euclidean__defs.Per C B A) as H0.
- apply (@lemma__8__2.lemma__8__2 (A) (B) (C) H).
- assert (* Cut *) (exists (D: euclidean__axioms.Point), (euclidean__axioms.BetS C B D) /\ ((euclidean__axioms.Cong C B D B) /\ ((euclidean__axioms.Cong C A D A) /\ (euclidean__axioms.neq B A)))) as H1.
-- exact H0.
-- assert (exists D: euclidean__axioms.Point, ((euclidean__axioms.BetS C B D) /\ ((euclidean__axioms.Cong C B D B) /\ ((euclidean__axioms.Cong C A D A) /\ (euclidean__axioms.neq B A))))) as H2.
--- exact H1.
--- destruct H2 as [D H2].
assert (* AndElim *) ((euclidean__axioms.BetS C B D) /\ ((euclidean__axioms.Cong C B D B) /\ ((euclidean__axioms.Cong C A D A) /\ (euclidean__axioms.neq B A)))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.Cong C B D B) /\ ((euclidean__axioms.Cong C A D A) /\ (euclidean__axioms.neq B A))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Cong C A D A) /\ (euclidean__axioms.neq B A)) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* Cut *) (euclidean__axioms.nCol A B C) as H9.
------- apply (@lemma__rightangleNC.lemma__rightangleNC (A) (B) (C) H).
------- assert (* Cut *) (euclidean__axioms.Triangle A B C) as H10.
-------- exact H9.
-------- assert (* Cut *) (~(euclidean__axioms.Col A C B)) as H11.
--------- intro H11.
assert (* Cut *) (euclidean__axioms.Col A B C) as H12.
---------- assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H12.
----------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (B) H11).
----------- assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A)) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
exact H19.
---------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H10) H12).
--------- assert (* Cut *) (euclidean__axioms.Triangle A C B) as H12.
---------- apply (@euclidean__tactics.nCol__notCol (A) (C) (B) H11).
---------- assert (* Cut *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H13.
----------- apply (@proposition__16.proposition__16 (A) (C) (B) (D) (H12) H3).
----------- assert (* Cut *) (A = A) as H14.
------------ assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
apply (@logic.eq__refl (Point) A).
------------ assert (* Cut *) (C = C) as H15.
------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H15.
-------------- exact H13.
-------------- destruct H15 as [H15 H16].
apply (@logic.eq__refl (Point) C).
------------- assert (* Cut *) (D = D) as H16.
-------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H16.
--------------- exact H13.
--------------- destruct H16 as [H16 H17].
apply (@logic.eq__refl (Point) D).
-------------- assert (* Cut *) (~(B = C)) as H17.
--------------- intro H17.
assert (* Cut *) (euclidean__axioms.Col A B C) as H18.
---------------- right.
right.
left.
exact H17.
---------------- apply (@H11).
-----------------apply (@euclidean__tactics.not__nCol__Col (A) (C) (B)).
------------------intro H19.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H10) H18).


--------------- assert (* Cut *) (euclidean__axioms.neq B D) as H18.
---------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H18.
----------------- exact H13.
----------------- destruct H18 as [H18 H19].
assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H20.
------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (C) (B) (D) H3).
------------------ assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H21.
------------------- exact H20.
------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)) as H23.
-------------------- exact H22.
-------------------- destruct H23 as [H23 H24].
exact H21.
---------------- assert (* Cut *) (euclidean__defs.Out B A A) as H19.
----------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H19.
------------------ exact H13.
------------------ destruct H19 as [H19 H20].
apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
-------------------right.
left.
exact H14.

------------------- exact H8.
----------------- assert (* Cut *) (euclidean__defs.Out B C C) as H20.
------------------ assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H20.
------------------- exact H13.
------------------- destruct H20 as [H20 H21].
apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
--------------------right.
left.
exact H15.

-------------------- exact H17.
------------------ assert (* Cut *) (euclidean__defs.Out B D D) as H21.
------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H21.
-------------------- exact H13.
-------------------- destruct H21 as [H21 H22].
apply (@lemma__ray4.lemma__ray4 (B) (D) (D)).
---------------------right.
left.
exact H16.

--------------------- exact H18.
------------------- assert (* Cut *) (euclidean__axioms.Cong B A B A) as H22.
-------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H22.
--------------------- exact H13.
--------------------- destruct H22 as [H22 H23].
apply (@euclidean__axioms.cn__congruencereflexive (B) A).
-------------------- assert (* Cut *) (euclidean__axioms.Cong B D B C) as H23.
--------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H23.
---------------------- exact H13.
---------------------- destruct H23 as [H23 H24].
assert (* Cut *) ((euclidean__axioms.Cong B D B C) /\ (euclidean__axioms.Cong B C B D)) as H25.
----------------------- apply (@lemma__doublereverse.lemma__doublereverse (C) (B) (D) (B) H5).
----------------------- assert (* AndElim *) ((euclidean__axioms.Cong B D B C) /\ (euclidean__axioms.Cong B C B D)) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [H26 H27].
exact H26.
--------------------- assert (* Cut *) (euclidean__axioms.Cong A D A C) as H24.
---------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H24.
----------------------- exact H13.
----------------------- destruct H24 as [H24 H25].
assert (* Cut *) ((euclidean__axioms.Cong A D A C) /\ (euclidean__axioms.Cong A C A D)) as H26.
------------------------ apply (@lemma__doublereverse.lemma__doublereverse (C) (A) (D) (A) H7).
------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A D A C) /\ (euclidean__axioms.Cong A C A D)) as H27.
------------------------- exact H26.
------------------------- destruct H27 as [H27 H28].
exact H27.
---------------------- assert (* Cut *) (~(euclidean__axioms.Col A B D)) as H25.
----------------------- intro H25.
assert (* Cut *) (euclidean__axioms.Col C B D) as H26.
------------------------ right.
right.
right.
right.
left.
exact H3.
------------------------ assert (* Cut *) (euclidean__axioms.Col D B C) as H27.
------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H27.
-------------------------- exact H13.
-------------------------- destruct H27 as [H27 H28].
assert (* Cut *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H29.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (D) H26).
--------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H30.
---------------------------- exact H29.
---------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)))) as H32.
----------------------------- exact H31.
----------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
exact H37.
------------------------- assert (* Cut *) (euclidean__axioms.Col D B A) as H28.
-------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H28.
--------------------------- exact H13.
--------------------------- destruct H28 as [H28 H29].
assert (* Cut *) ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A))))) as H30.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (D) H25).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A))))) as H31.
----------------------------- exact H30.
----------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A)))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A)) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
exact H38.
-------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H29.
--------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H29.
---------------------------- exact H13.
---------------------------- destruct H29 as [H29 H30].
assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H31.
----------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (B) (D) H3).
----------------------------- assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
exact H18.
--------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H30.
---------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H30.
----------------------------- exact H13.
----------------------------- destruct H30 as [H30 H31].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (D) H29).
---------------------------- assert (* Cut *) (euclidean__axioms.Col B C A) as H31.
----------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H31.
------------------------------ exact H13.
------------------------------ destruct H31 as [H31 H32].
apply (@euclidean__tactics.not__nCol__Col (B) (C) (A)).
-------------------------------intro H33.
apply (@euclidean__tactics.Col__nCol__False (B) (C) (A) (H33)).
--------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (B) (C) (A) (H27) (H28) H30).


----------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H32.
------------------------------ assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H32.
------------------------------- exact H13.
------------------------------- destruct H32 as [H32 H33].
assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H34.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (A) H31).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H35.
--------------------------------- exact H34.
--------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)))) as H37.
---------------------------------- exact H36.
---------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [H41 H42].
exact H39.
------------------------------ apply (@H11).
-------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (C) (B)).
--------------------------------intro H33.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H10) H32).


----------------------- assert (* Cut *) (euclidean__defs.CongA A B D A B C) as H26.
------------------------ exists A.
exists D.
exists A.
exists C.
split.
------------------------- exact H19.
------------------------- split.
-------------------------- exact H21.
-------------------------- split.
--------------------------- exact H19.
--------------------------- split.
---------------------------- exact H20.
---------------------------- split.
----------------------------- exact H22.
----------------------------- split.
------------------------------ exact H23.
------------------------------ split.
------------------------------- exact H24.
------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (D) H25).
------------------------ assert (* Cut *) (euclidean__defs.CongA A B C A B D) as H27.
------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H27.
-------------------------- exact H13.
-------------------------- destruct H27 as [H27 H28].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (D) (A) (B) (C) H26).
------------------------- assert (* Cut *) (euclidean__defs.LtA B C A A B C) as H28.
-------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H28.
--------------------------- exact H13.
--------------------------- destruct H28 as [H28 H29].
apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (B) (C) (A) (A) (B) (D) (A) (B) (C) (H29) H27).
-------------------------- assert (* Cut *) (euclidean__defs.Lt A B A C) as H29.
--------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H29.
---------------------------- exact H13.
---------------------------- destruct H29 as [H29 H30].
apply (@proposition__19.proposition__19 (A) (B) (C) (H10) H28).
--------------------------- assert (* Cut *) (euclidean__defs.LtA C A B A B C) as H30.
---------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H30.
----------------------------- exact H13.
----------------------------- destruct H30 as [H30 H31].
apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (C) (A) (B) (A) (B) (D) (A) (B) (C) (H30) H27).
---------------------------- assert (* Cut *) (~(euclidean__axioms.Col B A C)) as H31.
----------------------------- intro H31.
assert (* Cut *) (euclidean__axioms.Col A B C) as H32.
------------------------------ assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H32.
------------------------------- exact H13.
------------------------------- destruct H32 as [H32 H33].
assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H34.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H31).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H35.
--------------------------------- exact H34.
--------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H37.
---------------------------------- exact H36.
---------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [H41 H42].
exact H35.
------------------------------ apply (@H11).
-------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (C) (B)).
--------------------------------intro H33.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H10) H32).


----------------------------- assert (* Cut *) (euclidean__defs.CongA B A C C A B) as H32.
------------------------------ assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H32.
------------------------------- exact H13.
------------------------------- destruct H32 as [H32 H33].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (B) (A) (C)).
--------------------------------apply (@euclidean__tactics.nCol__notCol (B) (A) (C) H31).

------------------------------ assert (* Cut *) (euclidean__defs.LtA B A C A B C) as H33.
------------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H33.
-------------------------------- exact H13.
-------------------------------- destruct H33 as [H33 H34].
apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (C) (A) (B) (A) (B) (C) (B) (A) (C) (H30) H32).
------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C B A)) as H34.
-------------------------------- intro H34.
assert (* Cut *) (euclidean__axioms.Col A B C) as H35.
--------------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H35.
---------------------------------- exact H13.
---------------------------------- destruct H35 as [H35 H36].
assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H37.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (A) H34).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H38.
------------------------------------ exact H37.
------------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)))) as H40.
------------------------------------- exact H39.
------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))) as H42.
-------------------------------------- exact H41.
-------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)) as H44.
--------------------------------------- exact H43.
--------------------------------------- destruct H44 as [H44 H45].
exact H45.
--------------------------------- apply (@H11).
----------------------------------apply (@euclidean__tactics.not__nCol__Col (A) (C) (B)).
-----------------------------------intro H36.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H10) H35).


-------------------------------- assert (* Cut *) (euclidean__axioms.Triangle C B A) as H35.
--------------------------------- apply (@euclidean__tactics.nCol__notCol (C) (B) (A) H34).
--------------------------------- assert (* Cut *) (euclidean__defs.CongA C B A A B C) as H36.
---------------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H36.
----------------------------------- exact H13.
----------------------------------- destruct H36 as [H36 H37].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (C) (B) (A) H35).
---------------------------------- assert (* Cut *) (euclidean__defs.LtA B A C C B A) as H37.
----------------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H37.
------------------------------------ exact H13.
------------------------------------ destruct H37 as [H37 H38].
apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (B) (A) (C) (A) (B) (C) (C) (B) (A) (H33) H36).
----------------------------------- assert (* Cut *) (euclidean__defs.Lt C B C A) as H38.
------------------------------------ assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H38.
------------------------------------- exact H13.
------------------------------------- destruct H38 as [H38 H39].
apply (@proposition__19.proposition__19 (C) (B) (A) (H35) H37).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong C B B C) as H39.
------------------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H39.
-------------------------------------- exact H13.
-------------------------------------- destruct H39 as [H39 H40].
apply (@euclidean__axioms.cn__equalityreverse (C) B).
------------------------------------- assert (* Cut *) (euclidean__defs.Lt B C C A) as H40.
-------------------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H40.
--------------------------------------- exact H13.
--------------------------------------- destruct H40 as [H40 H41].
apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (C) (B) (C) (A) (B) (C) (H38) H39).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C A A C) as H41.
--------------------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H41.
---------------------------------------- exact H13.
---------------------------------------- destruct H41 as [H41 H42].
apply (@euclidean__axioms.cn__equalityreverse (C) A).
--------------------------------------- assert (* Cut *) (euclidean__defs.Lt B C A C) as H42.
---------------------------------------- assert (* AndElim *) ((euclidean__defs.LtA C A B A B D) /\ (euclidean__defs.LtA B C A A B D)) as H42.
----------------------------------------- exact H13.
----------------------------------------- destruct H42 as [H42 H43].
apply (@lemma__lessthancongruence.lemma__lessthancongruence (B) (C) (C) (A) (A) (C) (H40) H41).
---------------------------------------- split.
----------------------------------------- exact H29.
----------------------------------------- exact H42.
Qed.
