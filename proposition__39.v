Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__angletrichotomy2.
Require Export lemma__crossbar2.
Require Export lemma__equalanglesflip.
Require Export lemma__equalanglessymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelflip.
Require Export lemma__ray4.
Require Export lemma__samesideflip.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__07.
Require Export proposition__26A.
Require Export proposition__39A.
Definition proposition__39 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.Triangle D B C) -> ((euclidean__defs.OS A D B C) -> ((euclidean__axioms.ET A B C D B C) -> ((euclidean__axioms.neq A D) -> (euclidean__defs.Par A D B C))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
assert (* Cut *) (euclidean__defs.OS D A B C) as H4.
- assert (* Cut *) ((euclidean__defs.OS D A B C) /\ ((euclidean__defs.OS A D C B) /\ (euclidean__defs.OS D A C B))) as H4.
-- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (B) (C) (A) (D) H1).
-- assert (* AndElim *) ((euclidean__defs.OS D A B C) /\ ((euclidean__defs.OS A D C B) /\ (euclidean__defs.OS D A C B))) as H5.
--- exact H4.
--- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.OS A D C B) /\ (euclidean__defs.OS D A C B)) as H7.
---- exact H6.
---- destruct H7 as [H7 H8].
exact H5.
- assert (* Cut *) (euclidean__defs.OS A D C B) as H5.
-- apply (@lemma__samesideflip.lemma__samesideflip (B) (C) (A) (D) H1).
-- assert (* Cut *) (euclidean__defs.OS D A C B) as H6.
--- assert (* Cut *) ((euclidean__defs.OS D A C B) /\ ((euclidean__defs.OS A D B C) /\ (euclidean__defs.OS D A B C))) as H6.
---- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (C) (B) (A) (D) H5).
---- assert (* AndElim *) ((euclidean__defs.OS D A C B) /\ ((euclidean__defs.OS A D B C) /\ (euclidean__defs.OS D A B C))) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.OS A D B C) /\ (euclidean__defs.OS D A B C)) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
exact H7.
--- assert (* Cut *) (euclidean__axioms.nCol A B C) as H7.
---- exact H.
---- assert (* Cut *) (euclidean__axioms.nCol D B C) as H8.
----- exact H0.
----- assert (* Cut *) (euclidean__axioms.neq A B) as H9.
------ assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H9.
------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H7).
------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
exact H10.
------ assert (* Cut *) (euclidean__axioms.neq B D) as H10.
------- assert (* Cut *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))))) as H10.
-------- apply (@lemma__NCdistinct.lemma__NCdistinct (D) (B) (C) H8).
-------- assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H17.
------------ exact H16.
------------ destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)) as H19.
------------- exact H18.
------------- destruct H19 as [H19 H20].
exact H17.
------- assert (* Cut *) (euclidean__axioms.neq B A) as H11.
-------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H9).
-------- assert (* Cut *) (euclidean__axioms.neq B C) as H12.
--------- assert (* Cut *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))))) as H12.
---------- apply (@lemma__NCdistinct.lemma__NCdistinct (D) (B) (C) H8).
---------- assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))))) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
exact H15.
--------- assert (* Cut *) (euclidean__axioms.neq C A) as H13.
---------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H13.
----------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H7).
----------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H18.
-------------- exact H17.
-------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H20.
--------------- exact H19.
--------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H22.
---------------- exact H21.
---------------- destruct H22 as [H22 H23].
exact H23.
---------- assert (* Cut *) (euclidean__axioms.neq C B) as H14.
----------- assert (* Cut *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))))) as H14.
------------ apply (@lemma__NCdistinct.lemma__NCdistinct (D) (B) (C) H8).
------------ assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))))) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
exact H23.
----------- assert (* Cut *) (euclidean__axioms.neq C D) as H15.
------------ assert (* Cut *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))))) as H15.
------------- apply (@lemma__NCdistinct.lemma__NCdistinct (D) (B) (C) H8).
------------- assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))))) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C D)) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
exact H25.
------------ assert (* Cut *) (A = A) as H16.
------------- apply (@logic.eq__refl (Point) A).
------------- assert (* Cut *) (C = C) as H17.
-------------- apply (@logic.eq__refl (Point) C).
-------------- assert (* Cut *) (D = D) as H18.
--------------- apply (@logic.eq__refl (Point) D).
--------------- assert (* Cut *) (B = B) as H19.
---------------- apply (@logic.eq__refl (Point) B).
---------------- assert (* Cut *) (euclidean__defs.Out B C C) as H20.
----------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (C)).
------------------right.
left.
exact H17.

------------------ exact H12.
----------------- assert (* Cut *) (euclidean__defs.Out B A A) as H21.
------------------ apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
-------------------right.
left.
exact H16.

------------------- exact H11.
------------------ assert (* Cut *) (euclidean__defs.Out B D D) as H22.
------------------- apply (@lemma__ray4.lemma__ray4 (B) (D) (D)).
--------------------right.
left.
exact H18.

-------------------- exact H10.
------------------- assert (* Cut *) (euclidean__defs.Out C B B) as H23.
-------------------- apply (@lemma__ray4.lemma__ray4 (C) (B) (B)).
---------------------right.
left.
exact H19.

--------------------- exact H14.
-------------------- assert (* Cut *) (euclidean__defs.Out C A A) as H24.
--------------------- apply (@lemma__ray4.lemma__ray4 (C) (A) (A)).
----------------------right.
left.
exact H16.

---------------------- exact H13.
--------------------- assert (* Cut *) (euclidean__defs.Out C D D) as H25.
---------------------- apply (@lemma__ray4.lemma__ray4 (C) (D) (D)).
-----------------------right.
left.
exact H18.

----------------------- exact H15.
---------------------- assert (* Cut *) (~(~(euclidean__defs.Par A D B C))) as H26.
----------------------- intro H26.
assert (* Cut *) (~(euclidean__defs.LtA C B D C B A)) as H27.
------------------------ intro H27.
assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M C) /\ (euclidean__defs.Out B D M)) as H28.
------------------------- apply (@lemma__crossbar2.lemma__crossbar2 (D) (B) (C) (A) (C) (A) (H27) (H4) (H20) H21).
------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M C) /\ (euclidean__defs.Out B D M))) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [M H29].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__defs.Out B D M)) as H30.
--------------------------- exact H29.
--------------------------- destruct H30 as [H30 H31].
assert (* Cut *) (euclidean__defs.Par A D B C) as H32.
---------------------------- apply (@proposition__39A.proposition__39A (A) (B) (C) (D) (M) (H7) (H2) (H30) H31).
---------------------------- apply (@H26 H32).
------------------------ assert (* Cut *) (~(euclidean__defs.LtA C B A C B D)) as H28.
------------------------- intro H28.
assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS D M C) /\ (euclidean__defs.Out B A M)) as H29.
-------------------------- apply (@lemma__crossbar2.lemma__crossbar2 (A) (B) (C) (D) (C) (D) (H28) (H1) (H20) H22).
-------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS D M C) /\ (euclidean__defs.Out B A M))) as H30.
--------------------------- exact H29.
--------------------------- destruct H30 as [M H30].
assert (* AndElim *) ((euclidean__axioms.BetS D M C) /\ (euclidean__defs.Out B A M)) as H31.
---------------------------- exact H30.
---------------------------- destruct H31 as [H31 H32].
assert (* Cut *) (euclidean__axioms.ET D B C A B C) as H33.
----------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (A) (B) (C) (D) (B) (C) H2).
----------------------------- assert (* Cut *) (euclidean__defs.Par D A B C) as H34.
------------------------------ apply (@proposition__39A.proposition__39A (D) (B) (C) (A) (M) (H8) (H33) (H31) H32).
------------------------------ assert (* Cut *) (euclidean__defs.Par A D B C) as H35.
------------------------------- assert (* Cut *) ((euclidean__defs.Par A D B C) /\ ((euclidean__defs.Par D A C B) /\ (euclidean__defs.Par A D C B))) as H35.
-------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (D) (A) (B) (C) H34).
-------------------------------- assert (* AndElim *) ((euclidean__defs.Par A D B C) /\ ((euclidean__defs.Par D A C B) /\ (euclidean__defs.Par A D C B))) as H36.
--------------------------------- exact H35.
--------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.Par D A C B) /\ (euclidean__defs.Par A D C B)) as H38.
---------------------------------- exact H37.
---------------------------------- destruct H38 as [H38 H39].
exact H36.
------------------------------- apply (@H26 H35).
------------------------- assert (* Cut *) (~(~(euclidean__defs.CongA C B D C B A))) as H29.
-------------------------- intro H29.
assert (* Cut *) (euclidean__axioms.nCol C B A) as H30.
--------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H30.
---------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H7).
---------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H31.
----------------------------- exact H30.
----------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
exact H38.
--------------------------- assert (* Cut *) (euclidean__axioms.nCol C B D) as H31.
---------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))))) as H31.
----------------------------- apply (@lemma__NCorder.lemma__NCorder (D) (B) (C) H8).
----------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D)))) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D)) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
exact H39.
---------------------------- assert (* Cut *) (euclidean__defs.LtA C B D C B A) as H32.
----------------------------- apply (@lemma__angletrichotomy2.lemma__angletrichotomy2 (C) (B) (D) (C) (B) (A) (H31) (H30) (H29) H28).
----------------------------- apply (@H27 H32).
-------------------------- assert (* Cut *) (euclidean__axioms.nCol A C B) as H30.
--------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H30.
---------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H7).
---------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H31.
----------------------------- exact H30.
----------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
exact H37.
--------------------------- assert (* Cut *) (euclidean__axioms.Triangle A C B) as H31.
---------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H31.
----------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
----------------------------- exact H30.
---------------------------- assert (* Cut *) (euclidean__axioms.nCol D C B) as H32.
----------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))))) as H32.
------------------------------ apply (@lemma__NCorder.lemma__NCorder (D) (B) (C) H8).
------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))))) as H33.
------------------------------- exact H32.
------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D)))) as H35.
-------------------------------- exact H34.
-------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D)) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [H39 H40].
exact H39.
----------------------------- assert (* Cut *) (euclidean__axioms.Triangle D C B) as H33.
------------------------------ assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H33.
------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
------------------------------- exact H32.
------------------------------ assert (* Cut *) (euclidean__defs.OS A D C B) as H34.
------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H34.
-------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
-------------------------------- exact H5.
------------------------------- assert (* Cut *) (euclidean__axioms.ET A B C D C B) as H35.
-------------------------------- assert (* Cut *) ((euclidean__axioms.ET A B C B C D) /\ ((euclidean__axioms.ET A B C D C B) /\ ((euclidean__axioms.ET A B C B D C) /\ ((euclidean__axioms.ET A B C C B D) /\ (euclidean__axioms.ET A B C C D B))))) as H35.
--------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (A) (B) (C) (D) (B) (C) H2).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.ET A B C B C D) /\ ((euclidean__axioms.ET A B C D C B) /\ ((euclidean__axioms.ET A B C B D C) /\ ((euclidean__axioms.ET A B C C B D) /\ (euclidean__axioms.ET A B C C D B))))) as H36.
---------------------------------- exact H35.
---------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.ET A B C D C B) /\ ((euclidean__axioms.ET A B C B D C) /\ ((euclidean__axioms.ET A B C C B D) /\ (euclidean__axioms.ET A B C C D B)))) as H38.
----------------------------------- exact H37.
----------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.ET A B C B D C) /\ ((euclidean__axioms.ET A B C C B D) /\ (euclidean__axioms.ET A B C C D B))) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.ET A B C C B D) /\ (euclidean__axioms.ET A B C C D B)) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
exact H38.
-------------------------------- assert (* Cut *) (euclidean__axioms.ET D C B A B C) as H36.
--------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H36.
---------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
---------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (A) (B) (C) (D) (C) (B) H35).
--------------------------------- assert (* Cut *) (euclidean__axioms.ET D C B A C B) as H37.
---------------------------------- assert (* Cut *) ((euclidean__axioms.ET D C B B C A) /\ ((euclidean__axioms.ET D C B A C B) /\ ((euclidean__axioms.ET D C B B A C) /\ ((euclidean__axioms.ET D C B C B A) /\ (euclidean__axioms.ET D C B C A B))))) as H37.
----------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (D) (C) (B) (A) (B) (C) H36).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.ET D C B B C A) /\ ((euclidean__axioms.ET D C B A C B) /\ ((euclidean__axioms.ET D C B B A C) /\ ((euclidean__axioms.ET D C B C B A) /\ (euclidean__axioms.ET D C B C A B))))) as H38.
------------------------------------ exact H37.
------------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.ET D C B A C B) /\ ((euclidean__axioms.ET D C B B A C) /\ ((euclidean__axioms.ET D C B C B A) /\ (euclidean__axioms.ET D C B C A B)))) as H40.
------------------------------------- exact H39.
------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.ET D C B B A C) /\ ((euclidean__axioms.ET D C B C B A) /\ (euclidean__axioms.ET D C B C A B))) as H42.
-------------------------------------- exact H41.
-------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.ET D C B C B A) /\ (euclidean__axioms.ET D C B C A B)) as H44.
--------------------------------------- exact H43.
--------------------------------------- destruct H44 as [H44 H45].
exact H40.
---------------------------------- assert (* Cut *) (euclidean__axioms.ET A C B D C B) as H38.
----------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H38.
------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric (D) (C) (B) (A) (C) (B) H37).
----------------------------------- assert (* Cut *) (~(euclidean__defs.LtA B C D B C A)) as H39.
------------------------------------ intro H39.
assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M B) /\ (euclidean__defs.Out C D M)) as H40.
------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H40.
-------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
-------------------------------------- apply (@lemma__crossbar2.lemma__crossbar2 (D) (C) (B) (A) (B) (A) (H39) (H6) (H23) H24).
------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M B) /\ (euclidean__defs.Out C D M))) as H41.
-------------------------------------- exact H40.
-------------------------------------- destruct H41 as [M H41].
assert (* AndElim *) ((euclidean__axioms.BetS A M B) /\ (euclidean__defs.Out C D M)) as H42.
--------------------------------------- exact H41.
--------------------------------------- destruct H42 as [H42 H43].
assert (* Cut *) (euclidean__defs.Par A D C B) as H44.
---------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H44.
----------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
----------------------------------------- apply (@proposition__39A.proposition__39A (A) (C) (B) (D) (M) (H31) (H38) (H42) H43).
---------------------------------------- assert (* Cut *) (euclidean__defs.Par A D B C) as H45.
----------------------------------------- assert (* Cut *) ((euclidean__defs.Par D A C B) /\ ((euclidean__defs.Par A D B C) /\ (euclidean__defs.Par D A B C))) as H45.
------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip (A) (D) (C) (B) H44).
------------------------------------------ assert (* AndElim *) ((euclidean__defs.Par D A C B) /\ ((euclidean__defs.Par A D B C) /\ (euclidean__defs.Par D A B C))) as H46.
------------------------------------------- exact H45.
------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.Par A D B C) /\ (euclidean__defs.Par D A B C)) as H48.
-------------------------------------------- exact H47.
-------------------------------------------- destruct H48 as [H48 H49].
exact H48.
----------------------------------------- apply (@H26 H45).
------------------------------------ assert (* Cut *) (~(euclidean__defs.LtA B C A B C D)) as H40.
------------------------------------- intro H40.
assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS D M B) /\ (euclidean__defs.Out C A M)) as H41.
-------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H41.
--------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
--------------------------------------- apply (@lemma__crossbar2.lemma__crossbar2 (A) (C) (B) (D) (B) (D) (H40) (H34) (H23) H25).
-------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS D M B) /\ (euclidean__defs.Out C A M))) as H42.
--------------------------------------- exact H41.
--------------------------------------- destruct H42 as [M H42].
assert (* AndElim *) ((euclidean__axioms.BetS D M B) /\ (euclidean__defs.Out C A M)) as H43.
---------------------------------------- exact H42.
---------------------------------------- destruct H43 as [H43 H44].
assert (* Cut *) (euclidean__axioms.ET D C B A C B) as H45.
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H45.
------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
------------------------------------------ exact H37.
----------------------------------------- assert (* Cut *) (euclidean__defs.Par D A C B) as H46.
------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H46.
------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
------------------------------------------- apply (@proposition__39A.proposition__39A (D) (C) (B) (A) (M) (H33) (H45) (H43) H44).
------------------------------------------ assert (* Cut *) (euclidean__defs.Par A D B C) as H47.
------------------------------------------- assert (* Cut *) ((euclidean__defs.Par A D C B) /\ ((euclidean__defs.Par D A B C) /\ (euclidean__defs.Par A D B C))) as H47.
-------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (D) (A) (C) (B) H46).
-------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par A D C B) /\ ((euclidean__defs.Par D A B C) /\ (euclidean__defs.Par A D B C))) as H48.
--------------------------------------------- exact H47.
--------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Par D A B C) /\ (euclidean__defs.Par A D B C)) as H50.
---------------------------------------------- exact H49.
---------------------------------------------- destruct H50 as [H50 H51].
exact H51.
------------------------------------------- apply (@H26 H47).
------------------------------------- assert (* Cut *) (~(~(euclidean__defs.CongA B C D B C A))) as H41.
-------------------------------------- intro H41.
assert (* Cut *) (euclidean__axioms.nCol B C A) as H42.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H42.
---------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (C) (B) H31).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H43.
----------------------------------------- exact H42.
----------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)))) as H45.
------------------------------------------ exact H44.
------------------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))) as H47.
------------------------------------------- exact H46.
------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)) as H49.
-------------------------------------------- exact H48.
-------------------------------------------- destruct H49 as [H49 H50].
exact H50.
--------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C D) as H43.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol B C D))))) as H43.
----------------------------------------- apply (@lemma__NCorder.lemma__NCorder (D) (C) (B) H33).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol B C D))))) as H44.
------------------------------------------ exact H43.
------------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol B C D)))) as H46.
------------------------------------------- exact H45.
------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol B C D))) as H48.
-------------------------------------------- exact H47.
-------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol B C D)) as H50.
--------------------------------------------- exact H49.
--------------------------------------------- destruct H50 as [H50 H51].
exact H51.
---------------------------------------- assert (* Cut *) (euclidean__defs.LtA B C D B C A) as H44.
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H44.
------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
------------------------------------------ apply (@lemma__angletrichotomy2.lemma__angletrichotomy2 (B) (C) (D) (B) (C) (A) (H43) (H42) (H41) H40).
----------------------------------------- apply (@H29).
------------------------------------------intro H45.
apply (@H39 H44).

-------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C A B C D) as H42.
--------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C D B C A) as H42.
---------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA B C D B C A) H41).
---------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H43.
----------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
----------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (B) (C) (D) (B) (C) (A) H42).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C B C) as H43.
---------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C D B C A) as H43.
----------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA B C D B C A) H41).
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H44.
------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
------------------------------------------ apply (@euclidean__axioms.cn__congruencereflexive (B) C).
---------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B C A B C) as H44.
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C D B C A) as H44.
------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA B C D B C A) H41).
------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H45.
------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
------------------------------------------- apply (@lemma__equalanglesflip.lemma__equalanglesflip (C) (B) (D) (C) (B) (A) H45).
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C D B C) as H45.
------------------------------------------ assert (* Cut *) (euclidean__defs.CongA B C D B C A) as H45.
------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA B C D B C A) H41).
------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H46.
-------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
-------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (B) (C) (A) (B) (C) H44).
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__defs.CongA B A C B D C))) as H46.
------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C D B C A) as H46.
-------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA B C D B C A) H41).
-------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H47.
--------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
--------------------------------------------- apply (@proposition__26A.proposition__26A (A) (B) (C) (D) (B) (C) (H7) (H8) (H45) (H42) H43).
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H47.
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__defs.CongA B A C B D C))) as H47.
--------------------------------------------- exact H46.
--------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Cong A C D C) /\ (euclidean__defs.CongA B A C B D C)) as H49.
---------------------------------------------- exact H48.
---------------------------------------------- destruct H49 as [H49 H50].
assert (* Cut *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D)))))) as H51.
----------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (D) (C) (B) H33).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D)))))) as H52.
------------------------------------------------ exact H51.
------------------------------------------------ destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D))))) as H54.
------------------------------------------------- exact H53.
------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D)))) as H56.
-------------------------------------------------- exact H55.
-------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D))) as H58.
--------------------------------------------------- exact H57.
--------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D)) as H60.
---------------------------------------------------- exact H59.
---------------------------------------------------- destruct H60 as [H60 H61].
exact H60.
-------------------------------------------- assert (* Cut *) (A = D) as H48.
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__defs.CongA B A C B D C))) as H48.
---------------------------------------------- exact H46.
---------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Cong A C D C) /\ (euclidean__defs.CongA B A C B D C)) as H50.
----------------------------------------------- exact H49.
----------------------------------------------- destruct H50 as [H50 H51].
assert (* Cut *) (euclidean__defs.CongA B C D B C A) as H52.
------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA B C D B C A) H41).
------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C B D C B A) as H53.
------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C B D C B A) H29).
------------------------------------------------- apply (@proposition__07.proposition__07 (B) (C) (A) (D) (H47) (H48) (H50) H1).
--------------------------------------------- apply (@H3 H48).
----------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Par A D B C)).
------------------------intro H27.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H28.
------------------------- exact H7.
------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS D B C)) /\ ((~(euclidean__axioms.BetS D C B)) /\ (~(euclidean__axioms.BetS B D C))))))) as H30.
-------------------------- exact H8.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H32.
--------------------------- exact H29.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS D B C)) /\ ((~(euclidean__axioms.BetS D C B)) /\ (~(euclidean__axioms.BetS B D C)))))) as H34.
---------------------------- exact H31.
---------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H36.
----------------------------- exact H33.
----------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS D B C)) /\ ((~(euclidean__axioms.BetS D C B)) /\ (~(euclidean__axioms.BetS B D C))))) as H38.
------------------------------ exact H35.
------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H40.
------------------------------- exact H37.
------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((~(euclidean__axioms.BetS D B C)) /\ ((~(euclidean__axioms.BetS D C B)) /\ (~(euclidean__axioms.BetS B D C)))) as H42.
-------------------------------- exact H39.
-------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H44.
--------------------------------- exact H41.
--------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((~(euclidean__axioms.BetS D C B)) /\ (~(euclidean__axioms.BetS B D C))) as H46.
---------------------------------- exact H43.
---------------------------------- destruct H46 as [H46 H47].
assert (* Cut *) (False) as H48.
----------------------------------- apply (@H26 H27).
----------------------------------- assert False.
------------------------------------exact H48.
------------------------------------ contradiction.

Qed.
