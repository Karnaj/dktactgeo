Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export lemma__sameside2.
Require Export lemma__samesidereflexive.
Require Export lemma__samesidetransitive.
Require Export logic.
Require Export proposition__04.
Require Export proposition__07.
Require Export proposition__29B.
Definition lemma__Playfairhelper : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__defs.Par A B C D) -> ((euclidean__defs.Par A B C E) -> ((euclidean__defs.CR A D B C) -> ((euclidean__defs.CR A E B C) -> (euclidean__axioms.Col C D E)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS B M C)) as H3.
- exact H1.
- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS B M C))) as H4.
-- exact H3.
-- destruct H4 as [M H4].
assert (* AndElim *) ((euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS B M C)) as H5.
--- exact H4.
--- destruct H5 as [H5 H6].
assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS A m E) /\ (euclidean__axioms.BetS B m C)) as H7.
---- exact H2.
---- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS A m E) /\ (euclidean__axioms.BetS B m C))) as H8.
----- exact H7.
----- destruct H8 as [m H8].
assert (* AndElim *) ((euclidean__axioms.BetS A m E) /\ (euclidean__axioms.BetS B m C)) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
assert (* Cut *) (euclidean__axioms.neq B C) as H11.
------- assert (* Cut *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq B m) /\ (euclidean__axioms.neq B C))) as H11.
-------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (m) (C) H10).
-------- assert (* AndElim *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq B m) /\ (euclidean__axioms.neq B C))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq B m) /\ (euclidean__axioms.neq B C)) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
exact H15.
------- assert (* Cut *) (euclidean__axioms.BetS E m A) as H12.
-------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (m) (E) H9).
-------- assert (* Cut *) (euclidean__axioms.BetS D M A) as H13.
--------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (M) (D) H5).
--------- assert (* Cut *) (euclidean__axioms.Col B M C) as H14.
---------- right.
right.
right.
right.
left.
exact H6.
---------- assert (* Cut *) (euclidean__axioms.Col B m C) as H15.
----------- right.
right.
right.
right.
left.
exact H10.
----------- assert (* Cut *) (euclidean__axioms.Col C B M) as H16.
------------ assert (* Cut *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H16.
------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (M) (C) H14).
------------- assert (* AndElim *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B)))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B)) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
exact H21.
------------ assert (* Cut *) (euclidean__axioms.Col C B m) as H17.
------------- assert (* Cut *) ((euclidean__axioms.Col m B C) /\ ((euclidean__axioms.Col m C B) /\ ((euclidean__axioms.Col C B m) /\ ((euclidean__axioms.Col B C m) /\ (euclidean__axioms.Col C m B))))) as H17.
-------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (m) (C) H15).
-------------- assert (* AndElim *) ((euclidean__axioms.Col m B C) /\ ((euclidean__axioms.Col m C B) /\ ((euclidean__axioms.Col C B m) /\ ((euclidean__axioms.Col B C m) /\ (euclidean__axioms.Col C m B))))) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col m C B) /\ ((euclidean__axioms.Col C B m) /\ ((euclidean__axioms.Col B C m) /\ (euclidean__axioms.Col C m B)))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col C B m) /\ ((euclidean__axioms.Col B C m) /\ (euclidean__axioms.Col C m B))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col B C m) /\ (euclidean__axioms.Col C m B)) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
exact H22.
------------- assert (* Cut *) (euclidean__axioms.nCol B C E) as H18.
-------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol A B E)))) as H18.
--------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (C) (E) H0).
--------------- assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol A B E)))) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol A B E))) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol A B E)) as H23.
------------------ exact H22.
------------------ destruct H23 as [H23 H24].
exact H23.
-------------- assert (* Cut *) (euclidean__axioms.nCol C B E) as H19.
--------------- assert (* Cut *) ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol E C B))))) as H19.
---------------- apply (@lemma__NCorder.lemma__NCorder (B) (C) (E) H18).
---------------- assert (* AndElim *) ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol E C B))))) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol E C B)))) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol E C B))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol E C B)) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
exact H20.
--------------- assert (* Cut *) (euclidean__axioms.nCol B C D) as H20.
---------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H20.
----------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (C) (D) H).
----------------- assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H21.
------------------ exact H20.
------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D))) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
exact H25.
---------------- assert (* Cut *) (euclidean__axioms.nCol C B D) as H21.
----------------- assert (* Cut *) ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B))))) as H21.
------------------ apply (@lemma__NCorder.lemma__NCorder (B) (C) (D) H20).
------------------ assert (* AndElim *) ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B))))) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B)))) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B))) as H26.
--------------------- exact H25.
--------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B)) as H28.
---------------------- exact H27.
---------------------- destruct H28 as [H28 H29].
exact H22.
----------------- assert (* Cut *) (euclidean__axioms.TS E C B A) as H22.
------------------ exists m.
split.
------------------- exact H12.
------------------- split.
-------------------- exact H17.
-------------------- exact H19.
------------------ assert (* Cut *) (euclidean__axioms.TS D C B A) as H23.
------------------- exists M.
split.
-------------------- exact H13.
-------------------- split.
--------------------- exact H16.
--------------------- exact H21.
------------------- assert (* Cut *) (euclidean__defs.Par C D A B) as H24.
-------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (B) (C) (D) H).
-------------------- assert (* Cut *) (euclidean__defs.Par C E A B) as H25.
--------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (B) (C) (E) H0).
--------------------- assert (* Cut *) (euclidean__defs.Par E C B A) as H26.
---------------------- assert (* Cut *) ((euclidean__defs.Par E C A B) /\ ((euclidean__defs.Par C E B A) /\ (euclidean__defs.Par E C B A))) as H26.
----------------------- apply (@lemma__parallelflip.lemma__parallelflip (C) (E) (A) (B) H25).
----------------------- assert (* AndElim *) ((euclidean__defs.Par E C A B) /\ ((euclidean__defs.Par C E B A) /\ (euclidean__defs.Par E C B A))) as H27.
------------------------ exact H26.
------------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__defs.Par C E B A) /\ (euclidean__defs.Par E C B A)) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [H29 H30].
exact H30.
---------------------- assert (* Cut *) (euclidean__defs.Par D C B A) as H27.
----------------------- assert (* Cut *) ((euclidean__defs.Par D C A B) /\ ((euclidean__defs.Par C D B A) /\ (euclidean__defs.Par D C B A))) as H27.
------------------------ apply (@lemma__parallelflip.lemma__parallelflip (C) (D) (A) (B) H24).
------------------------ assert (* AndElim *) ((euclidean__defs.Par D C A B) /\ ((euclidean__defs.Par C D B A) /\ (euclidean__defs.Par D C B A))) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.Par C D B A) /\ (euclidean__defs.Par D C B A)) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
exact H31.
----------------------- assert (* Cut *) (euclidean__defs.CongA E C B C B A) as H28.
------------------------ apply (@proposition__29B.proposition__29B (E) (A) (C) (B) (H26) H22).
------------------------ assert (* Cut *) (euclidean__defs.CongA D C B C B A) as H29.
------------------------- apply (@proposition__29B.proposition__29B (D) (A) (C) (B) (H27) H23).
------------------------- assert (* Cut *) (euclidean__defs.CongA C B A D C B) as H30.
-------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (C) (B) (C) (B) (A) H29).
-------------------------- assert (* Cut *) (euclidean__defs.CongA E C B D C B) as H31.
--------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (E) (C) (B) (C) (B) (A) (D) (C) (B) (H28) H30).
--------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H32.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E C)))))) as H32.
----------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (C) (B) (E) H19).
----------------------------- assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E C)))))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E C))))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E C)))) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E C))) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E C)) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
exact H37.
---------------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H33.
----------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C)))))) as H33.
------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct (C) (B) (D) H21).
------------------------------ assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C)))))) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C))))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C)))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C)) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
exact H38.
----------------------------- assert (* Cut *) (exists (e: euclidean__axioms.Point), (euclidean__defs.Out C E e) /\ (euclidean__axioms.Cong C e C D)) as H34.
------------------------------ apply (@lemma__layoff.lemma__layoff (C) (E) (C) (D) (H32) H33).
------------------------------ assert (exists e: euclidean__axioms.Point, ((euclidean__defs.Out C E e) /\ (euclidean__axioms.Cong C e C D))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [e H35].
assert (* AndElim *) ((euclidean__defs.Out C E e) /\ (euclidean__axioms.Cong C e C D)) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* Cut *) (B = B) as H38.
--------------------------------- apply (@logic.eq__refl (Point) B).
--------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H39.
---------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H11).
---------------------------------- assert (* Cut *) (euclidean__defs.Out C B B) as H40.
----------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (B) (B)).
------------------------------------right.
left.
exact H38.

------------------------------------ exact H39.
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong C B C B) as H41.
------------------------------------ apply (@euclidean__axioms.cn__congruencereflexive (C) B).
------------------------------------ assert (* Cut *) (euclidean__axioms.nCol E C B) as H42.
------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B C E) /\ ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol E C B) /\ ((euclidean__axioms.nCol C E B) /\ (euclidean__axioms.nCol E B C))))) as H42.
-------------------------------------- apply (@lemma__NCorder.lemma__NCorder (C) (B) (E) H19).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B C E) /\ ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol E C B) /\ ((euclidean__axioms.nCol C E B) /\ (euclidean__axioms.nCol E B C))))) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol E C B) /\ ((euclidean__axioms.nCol C E B) /\ (euclidean__axioms.nCol E B C)))) as H45.
---------------------------------------- exact H44.
---------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.nCol E C B) /\ ((euclidean__axioms.nCol C E B) /\ (euclidean__axioms.nCol E B C))) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.nCol C E B) /\ (euclidean__axioms.nCol E B C)) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49 H50].
exact H47.
------------------------------------- assert (* Cut *) (euclidean__defs.CongA E C B E C B) as H43.
-------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (E) (C) (B) H42).
-------------------------------------- assert (* Cut *) (euclidean__defs.CongA E C B e C B) as H44.
--------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (E) (C) (B) (E) (C) (B) (e) (B) (H43) (H36) H40).
--------------------------------------- assert (* Cut *) (euclidean__defs.CongA e C B E C B) as H45.
---------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (E) (C) (B) (e) (C) (B) H44).
---------------------------------------- assert (* Cut *) (euclidean__defs.CongA e C B D C B) as H46.
----------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (e) (C) (B) (E) (C) (B) (D) (C) (B) (H45) H31).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col C E e) as H47.
------------------------------------------ apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (C) (E) (e) H36).
------------------------------------------ assert (* Cut *) (C = C) as H48.
------------------------------------------- apply (@logic.eq__refl (Point) C).
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C E C) as H49.
-------------------------------------------- right.
left.
exact H48.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E B) as H50.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol B C E))))) as H50.
---------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (E) (C) (B) H42).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol B C E))))) as H51.
----------------------------------------------- exact H50.
----------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol B C E)))) as H53.
------------------------------------------------ exact H52.
------------------------------------------------ destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.nCol B E C) /\ ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol B C E))) as H55.
------------------------------------------------- exact H54.
------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.nCol E B C) /\ (euclidean__axioms.nCol B C E)) as H57.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H57 as [H57 H58].
exact H51.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C e) as H51.
---------------------------------------------- apply (@lemma__raystrict.lemma__raystrict (C) (E) (e) H36).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C e B) as H52.
----------------------------------------------- apply (@euclidean__tactics.nCol__notCol (C) (e) (B)).
------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (C) (e) (B)).
-------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (C) (E) (B) (C) (e) (H50) (H49) (H47) H51).


----------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol e C B) as H53.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol e C B) /\ ((euclidean__axioms.nCol e B C) /\ ((euclidean__axioms.nCol B C e) /\ ((euclidean__axioms.nCol C B e) /\ (euclidean__axioms.nCol B e C))))) as H53.
------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (C) (e) (B) H52).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol e C B) /\ ((euclidean__axioms.nCol e B C) /\ ((euclidean__axioms.nCol B C e) /\ ((euclidean__axioms.nCol C B e) /\ (euclidean__axioms.nCol B e C))))) as H54.
-------------------------------------------------- exact H53.
-------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.nCol e B C) /\ ((euclidean__axioms.nCol B C e) /\ ((euclidean__axioms.nCol C B e) /\ (euclidean__axioms.nCol B e C)))) as H56.
--------------------------------------------------- exact H55.
--------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.nCol B C e) /\ ((euclidean__axioms.nCol C B e) /\ (euclidean__axioms.nCol B e C))) as H58.
---------------------------------------------------- exact H57.
---------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.nCol C B e) /\ (euclidean__axioms.nCol B e C)) as H60.
----------------------------------------------------- exact H59.
----------------------------------------------------- destruct H60 as [H60 H61].
exact H54.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Triangle e C B) as H54.
------------------------------------------------- exact H53.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D C B) as H55.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol D B C))))) as H55.
--------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (C) (B) (D) H21).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol D B C))))) as H56.
---------------------------------------------------- exact H55.
---------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol D B C)))) as H58.
----------------------------------------------------- exact H57.
----------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol D B C))) as H60.
------------------------------------------------------ exact H59.
------------------------------------------------------ destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol D B C)) as H62.
------------------------------------------------------- exact H61.
------------------------------------------------------- destruct H62 as [H62 H63].
exact H60.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle D C B) as H56.
--------------------------------------------------- exact H55.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong e B D B) as H57.
---------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__axioms.Cong A0 B0 a b) -> ((euclidean__axioms.Cong A0 C0 a c) -> ((euclidean__defs.CongA B0 A0 C0 b a c) -> (euclidean__axioms.Cong B0 C0 b c)))) as H57.
----------------------------------------------------- intro A0.
intro B0.
intro C0.
intro a.
intro b.
intro c.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b c) /\ ((euclidean__defs.CongA A0 B0 C0 a b c) /\ (euclidean__defs.CongA A0 C0 B0 a c b))) as __2.
------------------------------------------------------ apply (@proposition__04.proposition__04 (A0) (B0) (C0) (a) (b) (c) (__) (__0) __1).
------------------------------------------------------ destruct __2 as [__2 __3].
exact __2.
----------------------------------------------------- apply (@H57 (C) (e) (B) (C) (D) (B) (H37) (H41) H46).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C E) as H58.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol C B A) /\ (euclidean__axioms.nCol D C A)))) as H58.
------------------------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC (D) (C) (B) (A) H27).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol C B A) /\ (euclidean__axioms.nCol D C A)))) as H59.
------------------------------------------------------- exact H58.
------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol C B A) /\ (euclidean__axioms.nCol D C A))) as H61.
-------------------------------------------------------- exact H60.
-------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ (euclidean__axioms.nCol D C A)) as H63.
--------------------------------------------------------- exact H62.
--------------------------------------------------------- destruct H63 as [H63 H64].
exact H18.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C B E) as H59.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol E C B))))) as H59.
------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (C) (E) H58).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol E C B))))) as H60.
-------------------------------------------------------- exact H59.
-------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.nCol C E B) /\ ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol E C B)))) as H62.
--------------------------------------------------------- exact H61.
--------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol E C B))) as H64.
---------------------------------------------------------- exact H63.
---------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol E C B)) as H66.
----------------------------------------------------------- exact H65.
----------------------------------------------------------- destruct H66 as [H66 H67].
exact H60.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B C D) as H60.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol C B A) /\ (euclidean__axioms.nCol D C A)))) as H60.
-------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (D) (C) (B) (A) H27).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol C B A) /\ (euclidean__axioms.nCol D C A)))) as H61.
--------------------------------------------------------- exact H60.
--------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol C B A) /\ (euclidean__axioms.nCol D C A))) as H63.
---------------------------------------------------------- exact H62.
---------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ (euclidean__axioms.nCol D C A)) as H65.
----------------------------------------------------------- exact H64.
----------------------------------------------------------- destruct H65 as [H65 H66].
exact H20.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C B D) as H61.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B))))) as H61.
--------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (C) (D) H60).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B))))) as H62.
---------------------------------------------------------- exact H61.
---------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B)))) as H64.
----------------------------------------------------------- exact H63.
----------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B))) as H66.
------------------------------------------------------------ exact H65.
------------------------------------------------------------ destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol D C B)) as H68.
------------------------------------------------------------- exact H67.
------------------------------------------------------------- destruct H68 as [H68 H69].
exact H62.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS E D C B) as H62.
--------------------------------------------------------- exists A.
exists m.
exists M.
split.
---------------------------------------------------------- exact H17.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H16.
----------------------------------------------------------- split.
------------------------------------------------------------ exact H12.
------------------------------------------------------------ split.
------------------------------------------------------------- exact H13.
------------------------------------------------------------- split.
-------------------------------------------------------------- exact H59.
-------------------------------------------------------------- exact H61.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C B e) as H63.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C e B) /\ ((euclidean__axioms.nCol C B e) /\ ((euclidean__axioms.nCol B e C) /\ ((euclidean__axioms.nCol e B C) /\ (euclidean__axioms.nCol B C e))))) as H63.
----------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (e) (C) (B) H54).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C e B) /\ ((euclidean__axioms.nCol C B e) /\ ((euclidean__axioms.nCol B e C) /\ ((euclidean__axioms.nCol e B C) /\ (euclidean__axioms.nCol B C e))))) as H64.
------------------------------------------------------------ exact H63.
------------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.nCol C B e) /\ ((euclidean__axioms.nCol B e C) /\ ((euclidean__axioms.nCol e B C) /\ (euclidean__axioms.nCol B C e)))) as H66.
------------------------------------------------------------- exact H65.
------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.nCol B e C) /\ ((euclidean__axioms.nCol e B C) /\ (euclidean__axioms.nCol B C e))) as H68.
-------------------------------------------------------------- exact H67.
-------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.nCol e B C) /\ (euclidean__axioms.nCol B C e)) as H70.
--------------------------------------------------------------- exact H69.
--------------------------------------------------------------- destruct H70 as [H70 H71].
exact H66.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C C B) as H64.
----------------------------------------------------------- left.
exact H48.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C e E) as H65.
------------------------------------------------------------ apply (@lemma__ray5.lemma__ray5 (C) (E) (e) H36).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS e e C B) as H66.
------------------------------------------------------------- apply (@lemma__samesidereflexive.lemma__samesidereflexive (C) (B) (e) H63).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS e E C B) as H67.
-------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 (C) (C) (B) (e) (e) (E) (H66) (H64) H65).
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS e D C B) as H68.
--------------------------------------------------------------- apply (@lemma__samesidetransitive.lemma__samesidetransitive (C) (B) (e) (E) (D) (H67) H62).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong e C D C) as H69.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong e C D C) /\ ((euclidean__axioms.Cong e C C D) /\ (euclidean__axioms.Cong C e D C))) as H69.
----------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (e) (C) (D) H37).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong e C D C) /\ ((euclidean__axioms.Cong e C C D) /\ (euclidean__axioms.Cong C e D C))) as H70.
------------------------------------------------------------------ exact H69.
------------------------------------------------------------------ destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Cong e C C D) /\ (euclidean__axioms.Cong C e D C)) as H72.
------------------------------------------------------------------- exact H71.
------------------------------------------------------------------- destruct H72 as [H72 H73].
exact H70.
---------------------------------------------------------------- assert (* Cut *) (e = D) as H70.
----------------------------------------------------------------- apply (@proposition__07.proposition__07 (C) (B) (e) (D) (H39) (H69) (H57) H68).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C E D) as H71.
------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point D (fun e0: euclidean__axioms.Point => (euclidean__defs.Out C E e0) -> ((euclidean__axioms.Cong C e0 C D) -> ((euclidean__defs.CongA E C B e0 C B) -> ((euclidean__defs.CongA e0 C B E C B) -> ((euclidean__defs.CongA e0 C B D C B) -> ((euclidean__axioms.Col C E e0) -> ((euclidean__axioms.neq C e0) -> ((euclidean__axioms.nCol C e0 B) -> ((euclidean__axioms.nCol e0 C B) -> ((euclidean__axioms.Triangle e0 C B) -> ((euclidean__axioms.Cong e0 B D B) -> ((euclidean__axioms.nCol C B e0) -> ((euclidean__defs.Out C e0 E) -> ((euclidean__defs.OS e0 e0 C B) -> ((euclidean__defs.OS e0 E C B) -> ((euclidean__defs.OS e0 D C B) -> ((euclidean__axioms.Cong e0 C D C) -> (euclidean__axioms.Col C E D))))))))))))))))))) with (x := e).
-------------------------------------------------------------------intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
exact H76.

------------------------------------------------------------------- exact H70.
------------------------------------------------------------------- exact H36.
------------------------------------------------------------------- exact H37.
------------------------------------------------------------------- exact H44.
------------------------------------------------------------------- exact H45.
------------------------------------------------------------------- exact H46.
------------------------------------------------------------------- exact H47.
------------------------------------------------------------------- exact H51.
------------------------------------------------------------------- exact H52.
------------------------------------------------------------------- exact H53.
------------------------------------------------------------------- exact H54.
------------------------------------------------------------------- exact H57.
------------------------------------------------------------------- exact H63.
------------------------------------------------------------------- exact H65.
------------------------------------------------------------------- exact H66.
------------------------------------------------------------------- exact H67.
------------------------------------------------------------------- exact H68.
------------------------------------------------------------------- exact H69.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C D E) as H72.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))))) as H72.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (E) (D) H71).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))))) as H73.
--------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C)))) as H75.
---------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))) as H77.
----------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C)) as H79.
------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------ destruct H79 as [H79 H80].
exact H79.
------------------------------------------------------------------- exact H72.
Qed.
