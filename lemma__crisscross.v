Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__5b.
Require Export lemma__3__6b.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__samesidesymmetric.
Require Export logic.
Definition lemma__crisscross : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.Par A C B D) -> ((~(euclidean__defs.CR A B C D)) -> (euclidean__defs.CR A D B C)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (euclidean__defs.Par B D A C) as H1.
- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (C) (B) (D) H).
- assert (* Cut *) (euclidean__defs.TP B D A C) as H2.
-- apply (@lemma__paralleldef2B.lemma__paralleldef2B (B) (D) (A) (C) H1).
-- assert (* Cut *) (euclidean__defs.OS A C B D) as H3.
--- assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__defs.Meet B D A C)) /\ (euclidean__defs.OS A C B D)))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__defs.Meet B D A C)) /\ (euclidean__defs.OS A C B D))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((~(euclidean__defs.Meet B D A C)) /\ (euclidean__defs.OS A C B D)) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
exact H8.
--- assert (* Cut *) (euclidean__axioms.nCol A C B) as H4.
---- assert (* Cut *) ((euclidean__axioms.nCol A C B) /\ ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D)))) as H4.
----- apply (@lemma__parallelNC.lemma__parallelNC (A) (C) (B) (D) H).
----- assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D)))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D)) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
exact H5.
---- assert (* Cut *) (euclidean__axioms.neq A B) as H5.
----- assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A)))))) as H5.
------ apply (@lemma__NCdistinct.lemma__NCdistinct (A) (C) (B) H4).
------ assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A)))))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A))))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A)))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
exact H10.
----- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS A B E) /\ (euclidean__axioms.Cong B E A B)) as H6.
------ apply (@lemma__extension.lemma__extension (A) (B) (A) (B) (H5) H5).
------ assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS A B E) /\ (euclidean__axioms.Cong B E A B))) as H7.
------- exact H6.
------- destruct H7 as [E H7].
assert (* AndElim *) ((euclidean__axioms.BetS A B E) /\ (euclidean__axioms.Cong B E A B)) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* Cut *) (B = B) as H10.
--------- apply (@logic.eq__refl (Point) B).
--------- assert (* Cut *) (euclidean__axioms.Col B D B) as H11.
---------- right.
left.
exact H10.
---------- assert (* Cut *) (euclidean__axioms.nCol A B D) as H12.
----------- assert (* Cut *) ((euclidean__axioms.nCol A C B) /\ ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D)))) as H12.
------------ apply (@lemma__parallelNC.lemma__parallelNC (A) (C) (B) (D) H).
------------ assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D)))) as H13.
------------- exact H12.
------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D)) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
exact H15.
----------- assert (* Cut *) (euclidean__axioms.nCol B D A) as H13.
------------ assert (* Cut *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H13.
------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (D) H12).
------------- assert (* AndElim *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H14.
-------------- exact H13.
-------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A)))) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A)) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
exact H16.
------------ assert (* Cut *) (euclidean__defs.OS C A B D) as H14.
------------- assert (* Cut *) ((euclidean__defs.OS C A B D) /\ ((euclidean__defs.OS A C D B) /\ (euclidean__defs.OS C A D B))) as H14.
-------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (B) (D) (A) (C) H3).
-------------- assert (* AndElim *) ((euclidean__defs.OS C A B D) /\ ((euclidean__defs.OS A C D B) /\ (euclidean__defs.OS C A D B))) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__defs.OS A C D B) /\ (euclidean__defs.OS C A D B)) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
exact H15.
------------- assert (* Cut *) (euclidean__axioms.TS A B D E) as H15.
-------------- exists B.
split.
--------------- exact H8.
--------------- split.
---------------- exact H11.
---------------- exact H13.
-------------- assert (* Cut *) (euclidean__axioms.TS C B D E) as H16.
--------------- apply (@lemma__planeseparation.lemma__planeseparation (B) (D) (C) (A) (E) (H14) H15).
--------------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS C F E) /\ ((euclidean__axioms.Col B D F) /\ (euclidean__axioms.nCol B D C))) as H17.
---------------- exact H16.
---------------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS C F E) /\ ((euclidean__axioms.Col B D F) /\ (euclidean__axioms.nCol B D C)))) as H18.
----------------- exact H17.
----------------- destruct H18 as [F H18].
assert (* AndElim *) ((euclidean__axioms.BetS C F E) /\ ((euclidean__axioms.Col B D F) /\ (euclidean__axioms.nCol B D C))) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col B D F) /\ (euclidean__axioms.nCol B D C)) as H21.
------------------- exact H20.
------------------- destruct H21 as [H21 H22].
assert (* Cut *) (euclidean__axioms.neq B D) as H23.
-------------------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C B)))))) as H23.
--------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (B) (D) (C) H22).
--------------------- assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C B)))))) as H24.
---------------------- exact H23.
---------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C B))))) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C B)))) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C B))) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C B)) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
exact H24.
-------------------- assert (* Cut *) (euclidean__axioms.nCol A B D) as H24.
--------------------- assert (* Cut *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H24.
---------------------- apply (@lemma__parallelNC.lemma__parallelNC (B) (D) (A) (C) H1).
---------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H25.
----------------------- exact H24.
----------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C))) as H27.
------------------------ exact H26.
------------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [H29 H30].
exact H12.
--------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H25.
---------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A)))))) as H25.
----------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (D) H24).
----------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A)))))) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A))))) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A)))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D A)) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
exact H30.
---------------------- assert (* Cut *) (euclidean__axioms.nCol A C D) as H26.
----------------------- assert (* Cut *) ((euclidean__axioms.nCol A C B) /\ ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D)))) as H26.
------------------------ apply (@lemma__parallelNC.lemma__parallelNC (A) (C) (B) (D) H).
------------------------ assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D)))) as H27.
------------------------- exact H26.
------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D))) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol A C D)) as H31.
--------------------------- exact H30.
--------------------------- destruct H31 as [H31 H32].
exact H32.
----------------------- assert (* Cut *) (euclidean__axioms.neq A C) as H27.
------------------------ assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))))) as H27.
------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (C) (D) H26).
------------------------- assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))))) as H28.
-------------------------- exact H27.
-------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A))))) as H30.
--------------------------- exact H29.
--------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A))) as H34.
----------------------------- exact H33.
----------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)) as H36.
------------------------------ exact H35.
------------------------------ destruct H36 as [H36 H37].
exact H28.
------------------------ assert (* Cut *) (euclidean__axioms.neq C D) as H28.
------------------------- assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))))) as H28.
-------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (C) (D) H26).
-------------------------- assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))))) as H29.
--------------------------- exact H28.
--------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A))))) as H31.
---------------------------- exact H30.
---------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A))) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)) as H37.
------------------------------- exact H36.
------------------------------- destruct H37 as [H37 H38].
exact H31.
------------------------- assert (* Cut *) (euclidean__axioms.neq C A) as H29.
-------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (C) H27).
-------------------------- assert (* Cut *) (euclidean__axioms.nCol A C B) as H30.
--------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H30.
---------------------------- apply (@lemma__parallelNC.lemma__parallelNC (B) (D) (A) (C) H1).
---------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H31.
----------------------------- exact H30.
----------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
exact H4.
--------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H31.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A)))))) as H31.
----------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (C) (B) H30).
----------------------------- assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A)))))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A))))) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A)))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B A)) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
exact H34.
---------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H32.
----------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (B) H31).
----------------------------- assert (* Cut *) ((B = D) \/ ((B = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D B F) \/ ((euclidean__axioms.BetS B D F) \/ (euclidean__axioms.BetS B F D)))))) as H33.
------------------------------ exact H21.
------------------------------ assert (* Cut *) (euclidean__defs.CR A D B C) as H34.
------------------------------- assert (* Cut *) ((B = D) \/ ((B = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D B F) \/ ((euclidean__axioms.BetS B D F) \/ (euclidean__axioms.BetS B F D)))))) as H34.
-------------------------------- exact H33.
-------------------------------- assert (* Cut *) ((B = D) \/ ((B = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D B F) \/ ((euclidean__axioms.BetS B D F) \/ (euclidean__axioms.BetS B F D)))))) as __TmpHyp.
--------------------------------- exact H34.
--------------------------------- assert (B = D \/ (B = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D B F) \/ ((euclidean__axioms.BetS B D F) \/ (euclidean__axioms.BetS B F D))))) as H35.
---------------------------------- exact __TmpHyp.
---------------------------------- destruct H35 as [H35|H35].
----------------------------------- assert (* Cut *) (~(~(euclidean__defs.CR A D B C))) as H36.
------------------------------------ intro H36.
apply (@H23 H35).
------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CR A D B C)).
-------------------------------------intro H37.
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))))) as H38.
-------------------------------------- exact H4.
-------------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H40.
--------------------------------------- exact H12.
--------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D A) /\ ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A))))))) as H42.
---------------------------------------- exact H13.
---------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C))))))) as H44.
----------------------------------------- exact H22.
----------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H46.
------------------------------------------ exact H24.
------------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D))))))) as H48.
------------------------------------------- exact H26.
------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))))) as H50.
-------------------------------------------- exact H30.
-------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))))) as H52.
--------------------------------------------- exact H39.
--------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H54.
---------------------------------------------- exact H41.
---------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D A) /\ ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A)))))) as H56.
----------------------------------------------- exact H43.
----------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C)))))) as H58.
------------------------------------------------ exact H45.
------------------------------------------------ destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H60.
------------------------------------------------- exact H47.
------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D)))))) as H62.
-------------------------------------------------- exact H49.
-------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))))) as H64.
--------------------------------------------------- exact H51.
--------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))) as H66.
---------------------------------------------------- exact H53.
---------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H68.
----------------------------------------------------- exact H55.
----------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A))))) as H70.
------------------------------------------------------ exact H57.
------------------------------------------------------ destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C))))) as H72.
------------------------------------------------------- exact H59.
------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H74.
-------------------------------------------------------- exact H61.
-------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D))))) as H76.
--------------------------------------------------------- exact H63.
--------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))) as H78.
---------------------------------------------------------- exact H65.
---------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))) as H80.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H82.
------------------------------------------------------------ exact H69.
------------------------------------------------------------ destruct H82 as [H82 H83].
assert (* AndElim *) ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A)))) as H84.
------------------------------------------------------------- exact H71.
------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C)))) as H86.
-------------------------------------------------------------- exact H73.
-------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H88.
--------------------------------------------------------------- exact H75.
--------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D)))) as H90.
---------------------------------------------------------------- exact H77.
---------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))) as H92.
----------------------------------------------------------------- exact H79.
----------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))) as H94.
------------------------------------------------------------------ exact H81.
------------------------------------------------------------------ destruct H94 as [H94 H95].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H96.
------------------------------------------------------------------- exact H83.
------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A))) as H98.
-------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C))) as H100.
--------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H102.
---------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D))) as H104.
----------------------------------------------------------------------- exact H91.
----------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))) as H106.
------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------ destruct H106 as [H106 H107].
assert (* Cut *) (False) as H108.
------------------------------------------------------------------------- apply (@H23 H35).
------------------------------------------------------------------------- assert (* Cut *) (False) as H109.
-------------------------------------------------------------------------- apply (@H36 H37).
-------------------------------------------------------------------------- assert False.
---------------------------------------------------------------------------exact H109.
--------------------------------------------------------------------------- contradiction.

----------------------------------- assert (B = F \/ (D = F) \/ ((euclidean__axioms.BetS D B F) \/ ((euclidean__axioms.BetS B D F) \/ (euclidean__axioms.BetS B F D)))) as H36.
------------------------------------ exact H35.
------------------------------------ destruct H36 as [H36|H36].
------------------------------------- assert (* Cut *) (~(~(euclidean__defs.CR A D B C))) as H37.
-------------------------------------- intro H37.
assert (* Cut *) (euclidean__axioms.Col C F E) as H38.
--------------------------------------- right.
right.
right.
right.
left.
exact H19.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F C) as H39.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col F E C) /\ ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col C E F) /\ (euclidean__axioms.Col E F C))))) as H39.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (E) H38).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col F E C) /\ ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col C E F) /\ (euclidean__axioms.Col E F C))))) as H40.
------------------------------------------ exact H39.
------------------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col F E C) /\ ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col C E F) /\ (euclidean__axioms.Col E F C)))) as H42.
------------------------------------------- exact H41.
------------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col C E F) /\ (euclidean__axioms.Col E F C))) as H44.
-------------------------------------------- exact H43.
-------------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col C E F) /\ (euclidean__axioms.Col E F C)) as H46.
--------------------------------------------- exact H45.
--------------------------------------------- destruct H46 as [H46 H47].
exact H47.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H40.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H40.
------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (E) H8).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H41.
------------------------------------------- exact H40.
------------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E)) as H43.
-------------------------------------------- exact H42.
-------------------------------------------- destruct H43 as [H43 H44].
exact H41.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B E) as H41.
------------------------------------------ right.
right.
right.
right.
left.
exact H8.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E B A) as H42.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H42.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (E) H41).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H43.
--------------------------------------------- exact H42.
--------------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A)))) as H45.
---------------------------------------------- exact H44.
---------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))) as H47.
----------------------------------------------- exact H46.
----------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A)) as H49.
------------------------------------------------ exact H48.
------------------------------------------------ destruct H49 as [H49 H50].
exact H50.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F C) as H43.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E A B) /\ (euclidean__axioms.Col A B E))))) as H43.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (B) (A) H42).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E A B) /\ (euclidean__axioms.Col A B E))))) as H44.
---------------------------------------------- exact H43.
---------------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E A B) /\ (euclidean__axioms.Col A B E)))) as H46.
----------------------------------------------- exact H45.
----------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E A B) /\ (euclidean__axioms.Col A B E))) as H48.
------------------------------------------------ exact H47.
------------------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ (euclidean__axioms.Col A B E)) as H50.
------------------------------------------------- exact H49.
------------------------------------------------- destruct H50 as [H50 H51].
exact H39.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B C) as H44.
--------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun B0: euclidean__axioms.Point => (euclidean__defs.Par A C B0 D) -> ((~(euclidean__defs.CR A B0 C D)) -> ((euclidean__defs.Par B0 D A C) -> ((euclidean__defs.TP B0 D A C) -> ((euclidean__defs.OS A C B0 D) -> ((euclidean__axioms.nCol A C B0) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.BetS A B0 E) -> ((euclidean__axioms.Cong B0 E A B0) -> ((B0 = B0) -> ((euclidean__axioms.Col B0 D B0) -> ((euclidean__axioms.nCol A B0 D) -> ((euclidean__axioms.nCol B0 D A) -> ((euclidean__defs.OS C A B0 D) -> ((euclidean__axioms.TS A B0 D E) -> ((euclidean__axioms.TS C B0 D E) -> ((euclidean__axioms.Col B0 D F) -> ((euclidean__axioms.nCol B0 D C) -> ((euclidean__axioms.neq B0 D) -> ((euclidean__axioms.nCol A B0 D) -> ((euclidean__axioms.nCol A C B0) -> ((euclidean__axioms.neq C B0) -> ((euclidean__axioms.neq B0 C) -> ((~(euclidean__defs.CR A D B0 C)) -> ((euclidean__axioms.neq B0 E) -> ((euclidean__axioms.Col A B0 E) -> ((euclidean__axioms.Col E B0 A) -> (euclidean__axioms.Col E B0 C))))))))))))))))))))))))))))) with (x := B).
----------------------------------------------intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
exact H43.

---------------------------------------------- exact H36.
---------------------------------------------- exact H.
---------------------------------------------- exact H0.
---------------------------------------------- exact H1.
---------------------------------------------- exact H2.
---------------------------------------------- exact H3.
---------------------------------------------- exact H4.
---------------------------------------------- exact H5.
---------------------------------------------- exact H8.
---------------------------------------------- exact H9.
---------------------------------------------- exact H10.
---------------------------------------------- exact H11.
---------------------------------------------- exact H12.
---------------------------------------------- exact H13.
---------------------------------------------- exact H14.
---------------------------------------------- exact H15.
---------------------------------------------- exact H16.
---------------------------------------------- exact H21.
---------------------------------------------- exact H22.
---------------------------------------------- exact H23.
---------------------------------------------- exact H24.
---------------------------------------------- exact H30.
---------------------------------------------- exact H31.
---------------------------------------------- exact H32.
---------------------------------------------- exact H37.
---------------------------------------------- exact H40.
---------------------------------------------- exact H41.
---------------------------------------------- exact H42.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H45.
---------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (E) H40).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H46.
----------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
------------------------------------------------intro H46.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (C) (H46)).
-------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (B) (A) (C) (H42) (H44) H45).


----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C B) as H47.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H47.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H46).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H48.
-------------------------------------------------- exact H47.
-------------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H50.
--------------------------------------------------- exact H49.
--------------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H52.
---------------------------------------------------- exact H51.
---------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H54.
----------------------------------------------------- exact H53.
----------------------------------------------------- destruct H54 as [H54 H55].
exact H50.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A C B) as H48.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H48.
-------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (B) (D) (A) (C) H1).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H49.
--------------------------------------------------- exact H48.
--------------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C))) as H51.
---------------------------------------------------- exact H50.
---------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)) as H53.
----------------------------------------------------- exact H52.
----------------------------------------------------- destruct H53 as [H53 H54].
exact H30.
------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (C) (B) (H48) H47).
-------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CR A D B C)).
---------------------------------------intro H38.
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))))) as H39.
---------------------------------------- exact H4.
---------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H41.
----------------------------------------- exact H12.
----------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D A) /\ ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A))))))) as H43.
------------------------------------------ exact H13.
------------------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C))))))) as H45.
------------------------------------------- exact H22.
------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H47.
-------------------------------------------- exact H24.
-------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D))))))) as H49.
--------------------------------------------- exact H26.
--------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))))) as H51.
---------------------------------------------- exact H30.
---------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))))) as H53.
----------------------------------------------- exact H40.
----------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H55.
------------------------------------------------ exact H42.
------------------------------------------------ destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D A) /\ ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A)))))) as H57.
------------------------------------------------- exact H44.
------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C)))))) as H59.
-------------------------------------------------- exact H46.
-------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H61.
--------------------------------------------------- exact H48.
--------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D)))))) as H63.
---------------------------------------------------- exact H50.
---------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))))) as H65.
----------------------------------------------------- exact H52.
----------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))) as H67.
------------------------------------------------------ exact H54.
------------------------------------------------------ destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H69.
------------------------------------------------------- exact H56.
------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A))))) as H71.
-------------------------------------------------------- exact H58.
-------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C))))) as H73.
--------------------------------------------------------- exact H60.
--------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H75.
---------------------------------------------------------- exact H62.
---------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D))))) as H77.
----------------------------------------------------------- exact H64.
----------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))) as H79.
------------------------------------------------------------ exact H66.
------------------------------------------------------------ destruct H79 as [H79 H80].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))) as H81.
------------------------------------------------------------- exact H68.
------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H83.
-------------------------------------------------------------- exact H70.
-------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A)))) as H85.
--------------------------------------------------------------- exact H72.
--------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C)))) as H87.
---------------------------------------------------------------- exact H74.
---------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H89.
----------------------------------------------------------------- exact H76.
----------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D)))) as H91.
------------------------------------------------------------------ exact H78.
------------------------------------------------------------------ destruct H91 as [H91 H92].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))) as H93.
------------------------------------------------------------------- exact H80.
------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))) as H95.
-------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H97.
--------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A))) as H99.
---------------------------------------------------------------------- exact H86.
---------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C))) as H101.
----------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H103.
------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------ destruct H103 as [H103 H104].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D))) as H105.
------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))) as H107.
-------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* Cut *) (False) as H109.
--------------------------------------------------------------------------- apply (@H37 H38).
--------------------------------------------------------------------------- assert False.
----------------------------------------------------------------------------exact H109.
---------------------------------------------------------------------------- contradiction.

------------------------------------- assert (D = F \/ (euclidean__axioms.BetS D B F) \/ ((euclidean__axioms.BetS B D F) \/ (euclidean__axioms.BetS B F D))) as H37.
-------------------------------------- exact H36.
-------------------------------------- destruct H37 as [H37|H37].
--------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A C B) as H38.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H38.
----------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (B) (D) (A) (C) H1).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H39.
------------------------------------------ exact H38.
------------------------------------------ destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C))) as H41.
------------------------------------------- exact H40.
------------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)) as H43.
-------------------------------------------- exact H42.
-------------------------------------------- destruct H43 as [H43 H44].
exact H30.
---------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A C F) as H39.
----------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun D0: euclidean__axioms.Point => (euclidean__defs.Par A C B D0) -> ((~(euclidean__defs.CR A B C D0)) -> ((euclidean__defs.Par B D0 A C) -> ((euclidean__defs.TP B D0 A C) -> ((euclidean__defs.OS A C B D0) -> ((euclidean__axioms.Col B D0 B) -> ((euclidean__axioms.nCol A B D0) -> ((euclidean__axioms.nCol B D0 A) -> ((euclidean__defs.OS C A B D0) -> ((euclidean__axioms.TS A B D0 E) -> ((euclidean__axioms.TS C B D0 E) -> ((euclidean__axioms.Col B D0 F) -> ((euclidean__axioms.nCol B D0 C) -> ((euclidean__axioms.neq B D0) -> ((euclidean__axioms.nCol A B D0) -> ((euclidean__axioms.neq A D0) -> ((euclidean__axioms.nCol A C D0) -> ((euclidean__axioms.neq C D0) -> (euclidean__axioms.nCol A C F)))))))))))))))))))) with (x := D).
------------------------------------------intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
exact H55.

------------------------------------------ exact H37.
------------------------------------------ exact H.
------------------------------------------ exact H0.
------------------------------------------ exact H1.
------------------------------------------ exact H2.
------------------------------------------ exact H3.
------------------------------------------ exact H11.
------------------------------------------ exact H12.
------------------------------------------ exact H13.
------------------------------------------ exact H14.
------------------------------------------ exact H15.
------------------------------------------ exact H16.
------------------------------------------ exact H21.
------------------------------------------ exact H22.
------------------------------------------ exact H23.
------------------------------------------ exact H24.
------------------------------------------ exact H25.
------------------------------------------ exact H26.
------------------------------------------ exact H28.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C F A) as H40.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol C A F) /\ ((euclidean__axioms.nCol C F A) /\ ((euclidean__axioms.nCol F A C) /\ ((euclidean__axioms.nCol A F C) /\ (euclidean__axioms.nCol F C A))))) as H40.
------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (C) (F) H39).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C A F) /\ ((euclidean__axioms.nCol C F A) /\ ((euclidean__axioms.nCol F A C) /\ ((euclidean__axioms.nCol A F C) /\ (euclidean__axioms.nCol F C A))))) as H41.
-------------------------------------------- exact H40.
-------------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.nCol C F A) /\ ((euclidean__axioms.nCol F A C) /\ ((euclidean__axioms.nCol A F C) /\ (euclidean__axioms.nCol F C A)))) as H43.
--------------------------------------------- exact H42.
--------------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol F A C) /\ ((euclidean__axioms.nCol A F C) /\ (euclidean__axioms.nCol F C A))) as H45.
---------------------------------------------- exact H44.
---------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.nCol A F C) /\ (euclidean__axioms.nCol F C A)) as H47.
----------------------------------------------- exact H46.
----------------------------------------------- destruct H47 as [H47 H48].
exact H43.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C F E) as H41.
------------------------------------------- right.
right.
right.
right.
left.
exact H19.
------------------------------------------- assert (* Cut *) (C = C) as H42.
-------------------------------------------- apply (@logic.eq__refl (Point) C).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C F C) as H43.
--------------------------------------------- right.
left.
exact H42.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H44.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C E))) as H44.
----------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (E) H19).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C E))) as H45.
------------------------------------------------ exact H44.
------------------------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C E)) as H47.
------------------------------------------------- exact H46.
------------------------------------------------- destruct H47 as [H47 H48].
exact H48.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E A) as H45.
----------------------------------------------- apply (@euclidean__tactics.nCol__notCol (C) (E) (A)).
------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (C) (E) (A)).
-------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (C) (F) (A) (C) (E) (H40) (H43) (H41) H44).


----------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E C) as H46.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol C A E) /\ (euclidean__axioms.nCol A E C))))) as H46.
------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (C) (E) (A) H45).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol C A E) /\ (euclidean__axioms.nCol A E C))))) as H47.
-------------------------------------------------- exact H46.
-------------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol C A E) /\ (euclidean__axioms.nCol A E C)))) as H49.
--------------------------------------------------- exact H48.
--------------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol C A E) /\ (euclidean__axioms.nCol A E C))) as H51.
---------------------------------------------------- exact H50.
---------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol C A E) /\ (euclidean__axioms.nCol A E C)) as H53.
----------------------------------------------------- exact H52.
----------------------------------------------------- destruct H53 as [H53 H54].
exact H54.
------------------------------------------------ assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M F) /\ (euclidean__axioms.BetS C M B)) as H47.
------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (A) (C) (E) (B) (F) (H8) (H19) H46).
------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M F) /\ (euclidean__axioms.BetS C M B))) as H48.
-------------------------------------------------- exact H47.
-------------------------------------------------- destruct H48 as [M H48].
assert (* AndElim *) ((euclidean__axioms.BetS A M F) /\ (euclidean__axioms.BetS C M B)) as H49.
--------------------------------------------------- exact H48.
--------------------------------------------------- destruct H49 as [H49 H50].
assert (* Cut *) (euclidean__axioms.BetS A M D) as H51.
---------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun D0: euclidean__axioms.Point => (euclidean__defs.Par A C B D0) -> ((~(euclidean__defs.CR A B C D0)) -> ((euclidean__defs.Par B D0 A C) -> ((euclidean__defs.TP B D0 A C) -> ((euclidean__defs.OS A C B D0) -> ((euclidean__axioms.Col B D0 B) -> ((euclidean__axioms.nCol A B D0) -> ((euclidean__axioms.nCol B D0 A) -> ((euclidean__defs.OS C A B D0) -> ((euclidean__axioms.TS A B D0 E) -> ((euclidean__axioms.TS C B D0 E) -> ((euclidean__axioms.Col B D0 F) -> ((euclidean__axioms.nCol B D0 C) -> ((euclidean__axioms.neq B D0) -> ((euclidean__axioms.nCol A B D0) -> ((euclidean__axioms.neq A D0) -> ((euclidean__axioms.nCol A C D0) -> ((euclidean__axioms.neq C D0) -> (euclidean__axioms.BetS A M D0)))))))))))))))))))) with (x := D).
-----------------------------------------------------intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
exact H49.

----------------------------------------------------- exact H37.
----------------------------------------------------- exact H.
----------------------------------------------------- exact H0.
----------------------------------------------------- exact H1.
----------------------------------------------------- exact H2.
----------------------------------------------------- exact H3.
----------------------------------------------------- exact H11.
----------------------------------------------------- exact H12.
----------------------------------------------------- exact H13.
----------------------------------------------------- exact H14.
----------------------------------------------------- exact H15.
----------------------------------------------------- exact H16.
----------------------------------------------------- exact H21.
----------------------------------------------------- exact H22.
----------------------------------------------------- exact H23.
----------------------------------------------------- exact H24.
----------------------------------------------------- exact H25.
----------------------------------------------------- exact H26.
----------------------------------------------------- exact H28.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B M C) as H52.
----------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (M) (B) H50).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.CR A D B C) as H53.
------------------------------------------------------ exists M.
split.
------------------------------------------------------- exact H51.
------------------------------------------------------- exact H52.
------------------------------------------------------ exact H53.
--------------------------------------- assert (euclidean__axioms.BetS D B F \/ (euclidean__axioms.BetS B D F) \/ (euclidean__axioms.BetS B F D)) as H38.
---------------------------------------- exact H37.
---------------------------------------- destruct H38 as [H38|H38].
----------------------------------------- assert (* Cut *) (~(~(euclidean__defs.CR A D B C))) as H39.
------------------------------------------ intro H39.
assert (* Cut *) (euclidean__axioms.nCol D B C) as H40.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol C D B))))) as H40.
-------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (D) (C) H22).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol C D B))))) as H41.
--------------------------------------------- exact H40.
--------------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol C D B)))) as H43.
---------------------------------------------- exact H42.
---------------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol C B D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol C D B))) as H45.
----------------------------------------------- exact H44.
----------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol C D B)) as H47.
------------------------------------------------ exact H46.
------------------------------------------------ destruct H47 as [H47 H48].
exact H41.
------------------------------------------- assert (* Cut *) (D = D) as H41.
-------------------------------------------- apply (@logic.eq__refl (Point) D).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B D) as H42.
--------------------------------------------- right.
left.
exact H41.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B F) as H43.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D B F) /\ ((euclidean__axioms.Col D F B) /\ ((euclidean__axioms.Col F B D) /\ ((euclidean__axioms.Col B F D) /\ (euclidean__axioms.Col F D B))))) as H43.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (D) (F) H21).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D B F) /\ ((euclidean__axioms.Col D F B) /\ ((euclidean__axioms.Col F B D) /\ ((euclidean__axioms.Col B F D) /\ (euclidean__axioms.Col F D B))))) as H44.
------------------------------------------------ exact H43.
------------------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col D F B) /\ ((euclidean__axioms.Col F B D) /\ ((euclidean__axioms.Col B F D) /\ (euclidean__axioms.Col F D B)))) as H46.
------------------------------------------------- exact H45.
------------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col F B D) /\ ((euclidean__axioms.Col B F D) /\ (euclidean__axioms.Col F D B))) as H48.
-------------------------------------------------- exact H47.
-------------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col B F D) /\ (euclidean__axioms.Col F D B)) as H50.
--------------------------------------------------- exact H49.
--------------------------------------------------- destruct H50 as [H50 H51].
exact H44.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D F) as H44.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D F))) as H44.
------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (D) (B) (F) H38).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D F))) as H45.
------------------------------------------------- exact H44.
------------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D F)) as H47.
-------------------------------------------------- exact H46.
-------------------------------------------------- destruct H47 as [H47 H48].
exact H48.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D F C) as H45.
------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (D) (F) (C)).
-------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (D) (F) (C)).
--------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (D) (B) (C) (D) (F) (H40) (H42) (H43) H44).


------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol C F D) as H46.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F D C) /\ ((euclidean__axioms.nCol F C D) /\ ((euclidean__axioms.nCol C D F) /\ ((euclidean__axioms.nCol D C F) /\ (euclidean__axioms.nCol C F D))))) as H46.
-------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (D) (F) (C) H45).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol F D C) /\ ((euclidean__axioms.nCol F C D) /\ ((euclidean__axioms.nCol C D F) /\ ((euclidean__axioms.nCol D C F) /\ (euclidean__axioms.nCol C F D))))) as H47.
--------------------------------------------------- exact H46.
--------------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.nCol F C D) /\ ((euclidean__axioms.nCol C D F) /\ ((euclidean__axioms.nCol D C F) /\ (euclidean__axioms.nCol C F D)))) as H49.
---------------------------------------------------- exact H48.
---------------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol C D F) /\ ((euclidean__axioms.nCol D C F) /\ (euclidean__axioms.nCol C F D))) as H51.
----------------------------------------------------- exact H50.
----------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol D C F) /\ (euclidean__axioms.nCol C F D)) as H53.
------------------------------------------------------ exact H52.
------------------------------------------------------ destruct H53 as [H53 H54].
exact H54.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C F E) as H47.
-------------------------------------------------- right.
right.
right.
right.
left.
exact H19.
-------------------------------------------------- assert (* Cut *) (C = C) as H48.
--------------------------------------------------- apply (@logic.eq__refl (Point) C).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C F C) as H49.
---------------------------------------------------- right.
left.
exact H48.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H50.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C E))) as H50.
------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (E) H19).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C E))) as H51.
------------------------------------------------------- exact H50.
------------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C E)) as H53.
-------------------------------------------------------- exact H52.
-------------------------------------------------------- destruct H53 as [H53 H54].
exact H54.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E D) as H51.
------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (C) (E) (D)).
-------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (C) (E) (D)).
--------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (C) (F) (D) (C) (E) (H46) (H49) (H47) H50).


------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol E C D) as H52.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E C D) /\ ((euclidean__axioms.nCol E D C) /\ ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C))))) as H52.
-------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (C) (E) (D) H51).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E C D) /\ ((euclidean__axioms.nCol E D C) /\ ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C))))) as H53.
--------------------------------------------------------- exact H52.
--------------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.nCol E D C) /\ ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C)))) as H55.
---------------------------------------------------------- exact H54.
---------------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.nCol D C E) /\ ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C))) as H57.
----------------------------------------------------------- exact H56.
----------------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.nCol C D E) /\ (euclidean__axioms.nCol D E C)) as H59.
------------------------------------------------------------ exact H58.
------------------------------------------------------------ destruct H59 as [H59 H60].
exact H53.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E F C) as H53.
-------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (F) (E) H19).
-------------------------------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS D M C) /\ (euclidean__axioms.BetS E B M)) as H54.
--------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (D) (E) (F) (B) (C) (H38) (H53) H52).
--------------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS D M C) /\ (euclidean__axioms.BetS E B M))) as H55.
---------------------------------------------------------- exact H54.
---------------------------------------------------------- destruct H55 as [M H55].
assert (* AndElim *) ((euclidean__axioms.BetS D M C) /\ (euclidean__axioms.BetS E B M)) as H56.
----------------------------------------------------------- exact H55.
----------------------------------------------------------- destruct H56 as [H56 H57].
assert (* Cut *) (euclidean__axioms.BetS C M D) as H58.
------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (M) (C) H56).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS M B E) as H59.
------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (B) (M) H57).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B E) as H60.
-------------------------------------------------------------- right.
right.
right.
right.
left.
exact H8.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B M) as H61.
--------------------------------------------------------------- right.
right.
right.
right.
left.
exact H57.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B A) as H62.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H62.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (E) H60).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H63.
------------------------------------------------------------------ exact H62.
------------------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A)))) as H65.
------------------------------------------------------------------- exact H64.
------------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))) as H67.
-------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A)) as H69.
--------------------------------------------------------------------- exact H68.
--------------------------------------------------------------------- destruct H69 as [H69 H70].
exact H70.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H63.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq M B) /\ (euclidean__axioms.neq M E))) as H63.
------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (M) (B) (E) H59).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq M B) /\ (euclidean__axioms.neq M E))) as H64.
------------------------------------------------------------------- exact H63.
------------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq M B) /\ (euclidean__axioms.neq M E)) as H66.
-------------------------------------------------------------------- exact H65.
-------------------------------------------------------------------- destruct H66 as [H66 H67].
exact H64.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H64.
------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (E) H63).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B M A) as H65.
------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (M) (A)).
--------------------------------------------------------------------intro H65.
apply (@euclidean__tactics.Col__nCol__False (B) (M) (A) (H65)).
---------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (B) (M) (A) (H61) (H62) H64).


------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B M) as H66.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B))))) as H66.
--------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (M) (A) H65).
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M B A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B))))) as H67.
---------------------------------------------------------------------- exact H66.
---------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B)))) as H69.
----------------------------------------------------------------------- exact H68.
----------------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B))) as H71.
------------------------------------------------------------------------ exact H70.
------------------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B)) as H73.
------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------- destruct H73 as [H73 H74].
exact H71.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C A B D) as H67.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par C A B D) /\ ((euclidean__defs.Par A C D B) /\ (euclidean__defs.Par C A D B))) as H67.
---------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (C) (B) (D) H).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par C A B D) /\ ((euclidean__defs.Par A C D B) /\ (euclidean__defs.Par C A D B))) as H68.
----------------------------------------------------------------------- exact H67.
----------------------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__defs.Par A C D B) /\ (euclidean__defs.Par C A D B)) as H70.
------------------------------------------------------------------------ exact H69.
------------------------------------------------------------------------ destruct H70 as [H70 H71].
exact H68.
--------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet C A B D)) as H68.
---------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C A U) /\ ((euclidean__axioms.Col C A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H68.
----------------------------------------------------------------------- exact H67.
----------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C A U) /\ ((euclidean__axioms.Col C A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------------------------------------------------------ exact H68.
------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C A U) /\ ((euclidean__axioms.Col C A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H69.
------------------------------------------------------------------------- exact __TmpHyp0.
------------------------------------------------------------------------- destruct H69 as [x H69].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C A x) /\ ((euclidean__axioms.Col C A V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H70.
-------------------------------------------------------------------------- exact H69.
-------------------------------------------------------------------------- destruct H70 as [x0 H70].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C A x) /\ ((euclidean__axioms.Col C A x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H71.
--------------------------------------------------------------------------- exact H70.
--------------------------------------------------------------------------- destruct H71 as [x1 H71].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C A x) /\ ((euclidean__axioms.Col C A x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B D x1) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H72.
---------------------------------------------------------------------------- exact H71.
---------------------------------------------------------------------------- destruct H72 as [x2 H72].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C A x) /\ ((euclidean__axioms.Col C A x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B D x1) /\ ((euclidean__axioms.Col B D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H73.
----------------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------------- destruct H73 as [x3 H73].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C A x) /\ ((euclidean__axioms.Col C A x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B D x1) /\ ((euclidean__axioms.Col B D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H74.
------------------------------------------------------------------------------ exact H73.
------------------------------------------------------------------------------ destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C A x) /\ ((euclidean__axioms.Col C A x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B D x1) /\ ((euclidean__axioms.Col B D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H76.
------------------------------------------------------------------------------- exact H75.
------------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col C A x) /\ ((euclidean__axioms.Col C A x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B D x1) /\ ((euclidean__axioms.Col B D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H78.
-------------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col C A x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B D x1) /\ ((euclidean__axioms.Col B D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H80.
--------------------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B D x1) /\ ((euclidean__axioms.Col B D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H82.
---------------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col B D x1) /\ ((euclidean__axioms.Col B D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H84.
----------------------------------------------------------------------------------- exact H83.
----------------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col B D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H86.
------------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------------ destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H88.
------------------------------------------------------------------------------------- exact H87.
------------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((~(euclidean__defs.Meet C A B D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H90.
-------------------------------------------------------------------------------------- exact H89.
-------------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H92.
--------------------------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A C u) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H94.
---------------------------------------------------------------------------------------- exact H1.
---------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A C u) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
----------------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A C u) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H95.
------------------------------------------------------------------------------------------ exact __TmpHyp1.
------------------------------------------------------------------------------------------ destruct H95 as [x4 H95].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col A C u) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H96.
------------------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------------------- destruct H96 as [x5 H96].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C u) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H97.
-------------------------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------------------------- destruct H97 as [x6 H97].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H98.
--------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------- destruct H98 as [x7 H98].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H99.
---------------------------------------------------------------------------------------------- exact H98.
---------------------------------------------------------------------------------------------- destruct H99 as [x8 H99].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H100.
----------------------------------------------------------------------------------------------- exact H99.
----------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H102.
------------------------------------------------------------------------------------------------ exact H101.
------------------------------------------------------------------------------------------------ destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H104.
------------------------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H106.
-------------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H108.
--------------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H110.
---------------------------------------------------------------------------------------------------- exact H109.
---------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H112.
----------------------------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H114.
------------------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------------------ destruct H114 as [H114 H115].
assert (* AndElim *) ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H116.
------------------------------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H118.
-------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H120.
--------------------------------------------------------------------------------------------------------- exact H.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
---------------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H121.
----------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
----------------------------------------------------------------------------------------------------------- destruct H121 as [x9 H121].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H122.
------------------------------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------------------------------ destruct H122 as [x10 H122].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H123.
------------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------------- destruct H123 as [x11 H123].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H124.
-------------------------------------------------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------------------------------------------------- destruct H124 as [x12 H124].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H125.
--------------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------------- destruct H125 as [x13 H125].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H126.
---------------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H128.
----------------------------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H130.
------------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------------ destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H132.
------------------------------------------------------------------------------------------------------------------- exact H131.
------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H134.
-------------------------------------------------------------------------------------------------------------------- exact H133.
-------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H136.
--------------------------------------------------------------------------------------------------------------------- exact H135.
--------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H138.
---------------------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H140.
----------------------------------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H142.
------------------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------------------ destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H144.
------------------------------------------------------------------------------------------------------------------------- exact H143.
------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
exact H90.
---------------------------------------------------------------------- assert (* Cut *) (A = A) as H69.
----------------------------------------------------------------------- apply (@logic.eq__refl (Point) A).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C A A) as H70.
------------------------------------------------------------------------ right.
right.
left.
exact H69.
------------------------------------------------------------------------ assert (* Cut *) (B = B) as H71.
------------------------------------------------------------------------- exact H10.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B B D) as H72.
-------------------------------------------------------------------------- left.
exact H71.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A M B) as H73.
--------------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (C) (A) (B) (D) (A) (B) (M) (H70) (H72) (H29) (H23) (H29) (H23) (H68) (H58) H66).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CR A B C D) as H74.
---------------------------------------------------------------------------- exists M.
split.
----------------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------------- exact H58.
---------------------------------------------------------------------------- apply (@H0 H74).
------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CR A D B C)).
-------------------------------------------intro H40.
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))))) as H41.
-------------------------------------------- exact H4.
-------------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H43.
--------------------------------------------- exact H12.
--------------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D A) /\ ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A))))))) as H45.
---------------------------------------------- exact H13.
---------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C))))))) as H47.
----------------------------------------------- exact H22.
----------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H49.
------------------------------------------------ exact H24.
------------------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D))))))) as H51.
------------------------------------------------- exact H26.
------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))))) as H53.
-------------------------------------------------- exact H30.
-------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))))) as H55.
--------------------------------------------------- exact H42.
--------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H57.
---------------------------------------------------- exact H44.
---------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D A) /\ ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A)))))) as H59.
----------------------------------------------------- exact H46.
----------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D C) /\ ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C)))))) as H61.
------------------------------------------------------ exact H48.
------------------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H63.
------------------------------------------------------- exact H50.
------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D)))))) as H65.
-------------------------------------------------------- exact H52.
-------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))))) as H67.
--------------------------------------------------------- exact H54.
--------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))) as H69.
---------------------------------------------------------- exact H56.
---------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H71.
----------------------------------------------------------- exact H58.
----------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A))))) as H73.
------------------------------------------------------------ exact H60.
------------------------------------------------------------ destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C))))) as H75.
------------------------------------------------------------- exact H62.
------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H77.
-------------------------------------------------------------- exact H64.
-------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D))))) as H79.
--------------------------------------------------------------- exact H66.
--------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))))) as H81.
---------------------------------------------------------------- exact H68.
---------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))) as H83.
----------------------------------------------------------------- exact H70.
----------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H85.
------------------------------------------------------------------ exact H72.
------------------------------------------------------------------ destruct H85 as [H85 H86].
assert (* AndElim *) ((~(euclidean__axioms.BetS B D A)) /\ ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A)))) as H87.
------------------------------------------------------------------- exact H74.
------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((~(euclidean__axioms.BetS B D C)) /\ ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C)))) as H89.
-------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H91.
--------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C D)) /\ ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D)))) as H93.
---------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B)))) as H95.
----------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))) as H97.
------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------ destruct H97 as [H97 H98].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H99.
------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A D)) /\ (~(euclidean__axioms.BetS D B A))) as H101.
-------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C D)) /\ (~(euclidean__axioms.BetS D B C))) as H103.
--------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H105.
---------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D C)) /\ (~(euclidean__axioms.BetS C A D))) as H107.
----------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ (~(euclidean__axioms.BetS C A B))) as H109.
------------------------------------------------------------------------------ exact H96.
------------------------------------------------------------------------------ destruct H109 as [H109 H110].
assert (* Cut *) (False) as H111.
------------------------------------------------------------------------------- apply (@H39 H40).
------------------------------------------------------------------------------- assert False.
--------------------------------------------------------------------------------exact H111.
-------------------------------------------------------------------------------- contradiction.

----------------------------------------- assert (euclidean__axioms.BetS B D F \/ euclidean__axioms.BetS B F D) as H39.
------------------------------------------ exact H38.
------------------------------------------ destruct H39 as [H39|H39].
------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A C B) as H40.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H40.
--------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (B) (D) (A) (C) H1).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H41.
---------------------------------------------- exact H40.
---------------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C))) as H43.
----------------------------------------------- exact H42.
----------------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)) as H45.
------------------------------------------------ exact H44.
------------------------------------------------ destruct H45 as [H45 H46].
exact H30.
-------------------------------------------- assert (* Cut *) (A = A) as H41.
--------------------------------------------- apply (@logic.eq__refl (Point) A).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B A) as H42.
---------------------------------------------- right.
left.
exact H41.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B E) as H43.
----------------------------------------------- right.
right.
right.
right.
left.
exact H8.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H44.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H44.
------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (E) H8).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H45.
-------------------------------------------------- exact H44.
-------------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E)) as H47.
--------------------------------------------------- exact H46.
--------------------------------------------------- destruct H47 as [H47 H48].
exact H48.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A B C) as H45.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H45.
-------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (C) (B) H40).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H46.
--------------------------------------------------- exact H45.
--------------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)))) as H48.
---------------------------------------------------- exact H47.
---------------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))) as H50.
----------------------------------------------------- exact H49.
----------------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)) as H52.
------------------------------------------------------ exact H51.
------------------------------------------------------ destruct H52 as [H52 H53].
exact H52.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E C) as H46.
-------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (E) (C)).
---------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (E) (C)).
----------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (B) (C) (A) (E) (H45) (H42) (H43) H44).


-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E B) as H47.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H47.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (E) H43).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H48.
----------------------------------------------------- exact H47.
----------------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A)))) as H50.
------------------------------------------------------ exact H49.
------------------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))) as H52.
------------------------------------------------------- exact H51.
------------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A)) as H54.
-------------------------------------------------------- exact H53.
-------------------------------------------------------- destruct H54 as [H54 H55].
exact H54.
--------------------------------------------------- assert (* Cut *) (E = E) as H48.
---------------------------------------------------- apply (@logic.eq__refl (Point) E).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E E) as H49.
----------------------------------------------------- right.
right.
left.
exact H48.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H50.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H50.
------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (E) H8).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H51.
-------------------------------------------------------- exact H50.
-------------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E)) as H53.
--------------------------------------------------------- exact H52.
--------------------------------------------------------- destruct H53 as [H53 H54].
exact H51.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B E C) as H51.
------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (B) (E) (C)).
--------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (B) (E) (C)).
---------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (E) (C) (B) (E) (H46) (H47) (H49) H50).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E B) as H52.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol E C B) /\ ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol C E B))))) as H52.
--------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (E) (C) H51).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol E C B) /\ ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol C E B))))) as H53.
---------------------------------------------------------- exact H52.
---------------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.nCol E C B) /\ ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol C E B)))) as H55.
----------------------------------------------------------- exact H54.
----------------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol C E B))) as H57.
------------------------------------------------------------ exact H56.
------------------------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol C E B)) as H59.
------------------------------------------------------------- exact H58.
------------------------------------------------------------- destruct H59 as [H59 H60].
exact H60.
-------------------------------------------------------- assert (* Cut *) (exists (J: euclidean__axioms.Point), (euclidean__axioms.BetS B J E) /\ (euclidean__axioms.BetS C D J)) as H53.
--------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (B) (C) (F) (D) (E) (H39) (H19) H52).
--------------------------------------------------------- assert (exists J: euclidean__axioms.Point, ((euclidean__axioms.BetS B J E) /\ (euclidean__axioms.BetS C D J))) as H54.
---------------------------------------------------------- exact H53.
---------------------------------------------------------- destruct H54 as [J H54].
assert (* AndElim *) ((euclidean__axioms.BetS B J E) /\ (euclidean__axioms.BetS C D J)) as H55.
----------------------------------------------------------- exact H54.
----------------------------------------------------------- destruct H55 as [H55 H56].
assert (* Cut *) (euclidean__axioms.BetS A J E) as H57.
------------------------------------------------------------ apply (@lemma__3__5b.lemma__3__5b (A) (B) (J) (E) (H8) H55).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A C B) as H58.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H58.
-------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (B) (D) (A) (C) H1).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H59.
--------------------------------------------------------------- exact H58.
--------------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C))) as H61.
---------------------------------------------------------------- exact H60.
---------------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)) as H63.
----------------------------------------------------------------- exact H62.
----------------------------------------------------------------- destruct H63 as [H63 H64].
exact H40.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H59.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H59.
--------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (C) (B) H58).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H60.
---------------------------------------------------------------- exact H59.
---------------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)))) as H62.
----------------------------------------------------------------- exact H61.
----------------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))) as H64.
------------------------------------------------------------------ exact H63.
------------------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)) as H66.
------------------------------------------------------------------- exact H65.
------------------------------------------------------------------- destruct H66 as [H66 H67].
exact H66.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A J E) as H60.
--------------------------------------------------------------- right.
right.
right.
right.
left.
exact H57.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A B) as H61.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H61.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (B) H47).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H62.
------------------------------------------------------------------ exact H61.
------------------------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)))) as H64.
------------------------------------------------------------------- exact H63.
------------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))) as H66.
-------------------------------------------------------------------- exact H65.
-------------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)) as H68.
--------------------------------------------------------------------- exact H67.
--------------------------------------------------------------------- destruct H68 as [H68 H69].
exact H62.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A J) as H62.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col J A E) /\ ((euclidean__axioms.Col J E A) /\ ((euclidean__axioms.Col E A J) /\ ((euclidean__axioms.Col A E J) /\ (euclidean__axioms.Col E J A))))) as H62.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (J) (E) H60).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col J A E) /\ ((euclidean__axioms.Col J E A) /\ ((euclidean__axioms.Col E A J) /\ ((euclidean__axioms.Col A E J) /\ (euclidean__axioms.Col E J A))))) as H63.
------------------------------------------------------------------- exact H62.
------------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col J E A) /\ ((euclidean__axioms.Col E A J) /\ ((euclidean__axioms.Col A E J) /\ (euclidean__axioms.Col E J A)))) as H65.
-------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col E A J) /\ ((euclidean__axioms.Col A E J) /\ (euclidean__axioms.Col E J A))) as H67.
--------------------------------------------------------------------- exact H66.
--------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col A E J) /\ (euclidean__axioms.Col E J A)) as H69.
---------------------------------------------------------------------- exact H68.
---------------------------------------------------------------------- destruct H69 as [H69 H70].
exact H67.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H63.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq J E) /\ ((euclidean__axioms.neq A J) /\ (euclidean__axioms.neq A E))) as H63.
------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (J) (E) H57).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq J E) /\ ((euclidean__axioms.neq A J) /\ (euclidean__axioms.neq A E))) as H64.
-------------------------------------------------------------------- exact H63.
-------------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq A J) /\ (euclidean__axioms.neq A E)) as H66.
--------------------------------------------------------------------- exact H65.
--------------------------------------------------------------------- destruct H66 as [H66 H67].
exact H67.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq E A) as H64.
------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (E) H63).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B J) as H65.
-------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (B) (J)).
---------------------------------------------------------------------intro H65.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (J) (H65)).
----------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (A) (B) (J) (H61) (H62) H64).


-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A J) as H66.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq J E) /\ ((euclidean__axioms.neq A J) /\ (euclidean__axioms.neq A E))) as H66.
---------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (J) (E) H57).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq J E) /\ ((euclidean__axioms.neq A J) /\ (euclidean__axioms.neq A E))) as H67.
----------------------------------------------------------------------- exact H66.
----------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq A J) /\ (euclidean__axioms.neq A E)) as H69.
------------------------------------------------------------------------ exact H68.
------------------------------------------------------------------------ destruct H69 as [H69 H70].
exact H69.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A J C) as H67.
---------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (J) (C)).
-----------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (J) (C)).
------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (B) (C) (A) (J) (H59) (H42) (H65) H66).


---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A B J) as H68.
----------------------------------------------------------------------- apply (@euclidean__axioms.axiom__innertransitivity (A) (B) (J) (E) (H8) H55).
----------------------------------------------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS C M B)) as H69.
------------------------------------------------------------------------ apply (@euclidean__axioms.postulate__Pasch__inner (A) (C) (J) (B) (D) (H68) (H56) H67).
------------------------------------------------------------------------ assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS C M B))) as H70.
------------------------------------------------------------------------- exact H69.
------------------------------------------------------------------------- destruct H70 as [M H70].
assert (* AndElim *) ((euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS C M B)) as H71.
-------------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* Cut *) (euclidean__axioms.BetS B M C) as H73.
--------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (M) (B) H72).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CR A D B C) as H74.
---------------------------------------------------------------------------- exists M.
split.
----------------------------------------------------------------------------- exact H71.
----------------------------------------------------------------------------- exact H73.
---------------------------------------------------------------------------- exact H74.
------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D F B) as H40.
-------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (F) (D) H39).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E B A) as H41.
--------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (E) H8).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B D) as H42.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H42.
----------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (B) (D) (A) (C) H1).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)))) as H43.
------------------------------------------------ exact H42.
------------------------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C))) as H45.
------------------------------------------------- exact H44.
------------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.nCol D A C) /\ (euclidean__axioms.nCol B D C)) as H47.
-------------------------------------------------- exact H46.
-------------------------------------------------- destruct H47 as [H47 H48].
exact H24.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B E) as H43.
----------------------------------------------- right.
right.
right.
right.
left.
exact H8.
----------------------------------------------- assert (* Cut *) (A = A) as H44.
------------------------------------------------ apply (@logic.eq__refl (Point) A).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B A) as H45.
------------------------------------------------- right.
left.
exact H44.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H46.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H46.
--------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (E) H8).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H47.
---------------------------------------------------- exact H46.
---------------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E)) as H49.
----------------------------------------------------- exact H48.
----------------------------------------------------- destruct H49 as [H49 H50].
exact H50.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E D) as H47.
--------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (E) (D)).
----------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (E) (D)).
-----------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (B) (D) (A) (E) (H42) (H45) (H43) H46).


--------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E A D) as H48.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E A D) /\ ((euclidean__axioms.nCol E D A) /\ ((euclidean__axioms.nCol D A E) /\ ((euclidean__axioms.nCol A D E) /\ (euclidean__axioms.nCol D E A))))) as H48.
----------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (E) (D) H47).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E A D) /\ ((euclidean__axioms.nCol E D A) /\ ((euclidean__axioms.nCol D A E) /\ ((euclidean__axioms.nCol A D E) /\ (euclidean__axioms.nCol D E A))))) as H49.
------------------------------------------------------ exact H48.
------------------------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol E D A) /\ ((euclidean__axioms.nCol D A E) /\ ((euclidean__axioms.nCol A D E) /\ (euclidean__axioms.nCol D E A)))) as H51.
------------------------------------------------------- exact H50.
------------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol D A E) /\ ((euclidean__axioms.nCol A D E) /\ (euclidean__axioms.nCol D E A))) as H53.
-------------------------------------------------------- exact H52.
-------------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.nCol A D E) /\ (euclidean__axioms.nCol D E A)) as H55.
--------------------------------------------------------- exact H54.
--------------------------------------------------------- destruct H55 as [H55 H56].
exact H49.
---------------------------------------------------- assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__axioms.BetS D Q A) /\ (euclidean__axioms.BetS E F Q)) as H49.
----------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (D) (E) (B) (F) (A) (H40) (H41) H48).
----------------------------------------------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__axioms.BetS D Q A) /\ (euclidean__axioms.BetS E F Q))) as H50.
------------------------------------------------------ exact H49.
------------------------------------------------------ destruct H50 as [Q H50].
assert (* AndElim *) ((euclidean__axioms.BetS D Q A) /\ (euclidean__axioms.BetS E F Q)) as H51.
------------------------------------------------------- exact H50.
------------------------------------------------------- destruct H51 as [H51 H52].
assert (* Cut *) (euclidean__axioms.BetS E F C) as H53.
-------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (F) (E) H19).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F Q) as H54.
--------------------------------------------------------- right.
right.
right.
right.
left.
exact H52.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F C) as H55.
---------------------------------------------------------- right.
right.
right.
right.
left.
exact H53.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F E) as H56.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C E))) as H56.
------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (E) H19).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C E))) as H57.
------------------------------------------------------------- exact H56.
------------------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C E)) as H59.
-------------------------------------------------------------- exact H58.
-------------------------------------------------------------- destruct H59 as [H59 H60].
exact H57.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E F) as H57.
------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (E) H56).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col F Q C) as H58.
------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (Q) (C)).
--------------------------------------------------------------intro H58.
apply (@euclidean__tactics.Col__nCol__False (F) (Q) (C) (H58)).
---------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (F) (Q) (C) (H54) (H55) H57).


------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F C Q) as H59.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q F C) /\ ((euclidean__axioms.Col Q C F) /\ ((euclidean__axioms.Col C F Q) /\ ((euclidean__axioms.Col F C Q) /\ (euclidean__axioms.Col C Q F))))) as H59.
--------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (Q) (C) H58).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col Q F C) /\ ((euclidean__axioms.Col Q C F) /\ ((euclidean__axioms.Col C F Q) /\ ((euclidean__axioms.Col F C Q) /\ (euclidean__axioms.Col C Q F))))) as H60.
---------------------------------------------------------------- exact H59.
---------------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col Q C F) /\ ((euclidean__axioms.Col C F Q) /\ ((euclidean__axioms.Col F C Q) /\ (euclidean__axioms.Col C Q F)))) as H62.
----------------------------------------------------------------- exact H61.
----------------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col C F Q) /\ ((euclidean__axioms.Col F C Q) /\ (euclidean__axioms.Col C Q F))) as H64.
------------------------------------------------------------------ exact H63.
------------------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col F C Q) /\ (euclidean__axioms.Col C Q F)) as H66.
------------------------------------------------------------------- exact H65.
------------------------------------------------------------------- destruct H66 as [H66 H67].
exact H66.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A Q D) as H60.
--------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (Q) (A) H51).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B F D) as H61.
---------------------------------------------------------------- right.
right.
right.
right.
left.
exact H39.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B D F) as H62.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F B D) /\ ((euclidean__axioms.Col F D B) /\ ((euclidean__axioms.Col D B F) /\ ((euclidean__axioms.Col B D F) /\ (euclidean__axioms.Col D F B))))) as H62.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (D) H61).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col F B D) /\ ((euclidean__axioms.Col F D B) /\ ((euclidean__axioms.Col D B F) /\ ((euclidean__axioms.Col B D F) /\ (euclidean__axioms.Col D F B))))) as H63.
------------------------------------------------------------------- exact H62.
------------------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col F D B) /\ ((euclidean__axioms.Col D B F) /\ ((euclidean__axioms.Col B D F) /\ (euclidean__axioms.Col D F B)))) as H65.
-------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col D B F) /\ ((euclidean__axioms.Col B D F) /\ (euclidean__axioms.Col D F B))) as H67.
--------------------------------------------------------------------- exact H66.
--------------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col B D F) /\ (euclidean__axioms.Col D F B)) as H69.
---------------------------------------------------------------------- exact H68.
---------------------------------------------------------------------- destruct H69 as [H69 H70].
exact H69.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F D) as H63.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B F) /\ (euclidean__axioms.neq B D))) as H63.
------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (F) (D) H39).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B F) /\ (euclidean__axioms.neq B D))) as H64.
-------------------------------------------------------------------- exact H63.
-------------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ (euclidean__axioms.neq B D)) as H66.
--------------------------------------------------------------------- exact H65.
--------------------------------------------------------------------- destruct H66 as [H66 H67].
exact H64.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par A C F D) as H64.
------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (A) (C) (F) (B) (D) (H) (H62) H63).
------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A C F D)) as H65.
-------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F D u) /\ ((euclidean__axioms.Col F D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H65.
--------------------------------------------------------------------- exact H64.
--------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F D u) /\ ((euclidean__axioms.Col F D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
---------------------------------------------------------------------- exact H65.
---------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F D u) /\ ((euclidean__axioms.Col F D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H66.
----------------------------------------------------------------------- exact __TmpHyp0.
----------------------------------------------------------------------- destruct H66 as [x H66].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.Col A C x) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col F D u) /\ ((euclidean__axioms.Col F D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H67.
------------------------------------------------------------------------ exact H66.
------------------------------------------------------------------------ destruct H67 as [x0 H67].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.Col A C x) /\ ((euclidean__axioms.Col A C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F D u) /\ ((euclidean__axioms.Col F D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H68.
------------------------------------------------------------------------- exact H67.
------------------------------------------------------------------------- destruct H68 as [x1 H68].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.Col A C x) /\ ((euclidean__axioms.Col A C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F D x1) /\ ((euclidean__axioms.Col F D v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H69.
-------------------------------------------------------------------------- exact H68.
-------------------------------------------------------------------------- destruct H69 as [x2 H69].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.Col A C x) /\ ((euclidean__axioms.Col A C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F D x1) /\ ((euclidean__axioms.Col F D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H70.
--------------------------------------------------------------------------- exact H69.
--------------------------------------------------------------------------- destruct H70 as [x3 H70].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.Col A C x) /\ ((euclidean__axioms.Col A C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F D x1) /\ ((euclidean__axioms.Col F D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H71.
---------------------------------------------------------------------------- exact H70.
---------------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.Col A C x) /\ ((euclidean__axioms.Col A C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F D x1) /\ ((euclidean__axioms.Col F D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H73.
----------------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col A C x) /\ ((euclidean__axioms.Col A C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F D x1) /\ ((euclidean__axioms.Col F D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H75.
------------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col A C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F D x1) /\ ((euclidean__axioms.Col F D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H77.
------------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F D x1) /\ ((euclidean__axioms.Col F D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H79.
-------------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col F D x1) /\ ((euclidean__axioms.Col F D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H81.
--------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col F D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H83.
---------------------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H85.
----------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((~(euclidean__defs.Meet A C F D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H87.
------------------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------------------ destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H89.
------------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A C u) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H91.
-------------------------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A C u) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
--------------------------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A C u) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H92.
---------------------------------------------------------------------------------------- exact __TmpHyp1.
---------------------------------------------------------------------------------------- destruct H92 as [x4 H92].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col A C u) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H93.
----------------------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------------------- destruct H93 as [x5 H93].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C u) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H94.
------------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------------ destruct H94 as [x6 H94].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H95.
------------------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------------------- destruct H95 as [x7 H95].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H96.
-------------------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------------------- destruct H96 as [x8 H96].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H97.
--------------------------------------------------------------------------------------------- exact H96.
--------------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H99.
---------------------------------------------------------------------------------------------- exact H98.
---------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.Col B D x4) /\ ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H101.
----------------------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.Col B D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H103.
------------------------------------------------------------------------------------------------ exact H102.
------------------------------------------------------------------------------------------------ destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H105.
------------------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col A C x6) /\ ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H107.
-------------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col A C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H109.
--------------------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H111.
---------------------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((~(euclidean__defs.Meet B D A C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H113.
----------------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H115.
------------------------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------------------------ destruct H115 as [H115 H116].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H117.
------------------------------------------------------------------------------------------------------- exact H.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
-------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H118.
--------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
--------------------------------------------------------------------------------------------------------- destruct H118 as [x9 H118].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H119.
---------------------------------------------------------------------------------------------------------- exact H118.
---------------------------------------------------------------------------------------------------------- destruct H119 as [x10 H119].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H120.
----------------------------------------------------------------------------------------------------------- exact H119.
----------------------------------------------------------------------------------------------------------- destruct H120 as [x11 H120].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H121.
------------------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------------------ destruct H121 as [x12 H121].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H122.
------------------------------------------------------------------------------------------------------------- exact H121.
------------------------------------------------------------------------------------------------------------- destruct H122 as [x13 H122].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H123.
-------------------------------------------------------------------------------------------------------------- exact H122.
-------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H125.
--------------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col A C x9) /\ ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H127.
---------------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col A C x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H129.
----------------------------------------------------------------------------------------------------------------- exact H128.
----------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H131.
------------------------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------------------------ destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col B D x11) /\ ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H133.
------------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col B D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H135.
-------------------------------------------------------------------------------------------------------------------- exact H134.
-------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H137.
--------------------------------------------------------------------------------------------------------------------- exact H136.
--------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H139.
---------------------------------------------------------------------------------------------------------------------- exact H138.
---------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H141.
----------------------------------------------------------------------------------------------------------------------- exact H140.
----------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
exact H87.
-------------------------------------------------------------------- assert (* Cut *) (C = C) as H66.
--------------------------------------------------------------------- apply (@logic.eq__refl (Point) C).
--------------------------------------------------------------------- assert (* Cut *) (F = F) as H67.
---------------------------------------------------------------------- apply (@logic.eq__refl (Point) F).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C C) as H68.
----------------------------------------------------------------------- right.
right.
left.
exact H66.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F F D) as H69.
------------------------------------------------------------------------ left.
exact H67.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C F Q) as H70.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C F Q) /\ ((euclidean__axioms.Col C Q F) /\ ((euclidean__axioms.Col Q F C) /\ ((euclidean__axioms.Col F Q C) /\ (euclidean__axioms.Col Q C F))))) as H70.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (C) (Q) H59).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C F Q) /\ ((euclidean__axioms.Col C Q F) /\ ((euclidean__axioms.Col Q F C) /\ ((euclidean__axioms.Col F Q C) /\ (euclidean__axioms.Col Q C F))))) as H71.
--------------------------------------------------------------------------- exact H70.
--------------------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col C Q F) /\ ((euclidean__axioms.Col Q F C) /\ ((euclidean__axioms.Col F Q C) /\ (euclidean__axioms.Col Q C F)))) as H73.
---------------------------------------------------------------------------- exact H72.
---------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col Q F C) /\ ((euclidean__axioms.Col F Q C) /\ (euclidean__axioms.Col Q C F))) as H75.
----------------------------------------------------------------------------- exact H74.
----------------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col F Q C) /\ (euclidean__axioms.Col Q C F)) as H77.
------------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------------ destruct H77 as [H77 H78].
exact H71.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C Q F) as H71.
-------------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (A) (C) (F) (D) (C) (F) (Q) (H68) (H69) (H27) (H63) (H27) (H63) (H65) (H60) H70).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A C B) as H72.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A C F) /\ ((euclidean__axioms.nCol A F D) /\ ((euclidean__axioms.nCol C F D) /\ (euclidean__axioms.nCol A C D)))) as H72.
---------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (C) (F) (D) H64).
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A C F) /\ ((euclidean__axioms.nCol A F D) /\ ((euclidean__axioms.nCol C F D) /\ (euclidean__axioms.nCol A C D)))) as H73.
----------------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.nCol A F D) /\ ((euclidean__axioms.nCol C F D) /\ (euclidean__axioms.nCol A C D))) as H75.
------------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.nCol C F D) /\ (euclidean__axioms.nCol A C D)) as H77.
------------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------------- destruct H77 as [H77 H78].
exact H30.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H73.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H73.
----------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (C) (B) H72).
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H74.
------------------------------------------------------------------------------ exact H73.
------------------------------------------------------------------------------ destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)))) as H76.
------------------------------------------------------------------------------- exact H75.
------------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))) as H78.
-------------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A)) as H80.
--------------------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------------------- destruct H80 as [H80 H81].
exact H80.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B A) as H74.
----------------------------------------------------------------------------- exact H45.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B E) as H75.
------------------------------------------------------------------------------ exact H43.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A E) as H76.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq Q F) /\ ((euclidean__axioms.neq C Q) /\ (euclidean__axioms.neq C F))) as H76.
-------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (Q) (F) H71).
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq Q F) /\ ((euclidean__axioms.neq C Q) /\ (euclidean__axioms.neq C F))) as H77.
--------------------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq C Q) /\ (euclidean__axioms.neq C F)) as H79.
---------------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------------- destruct H79 as [H79 H80].
exact H46.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E C) as H77.
-------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (E) (C)).
---------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (E) (C)).
----------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (B) (C) (A) (E) (H73) (H74) (H75) H76).


-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C Q E) as H78.
--------------------------------------------------------------------------------- apply (@lemma__3__6b.lemma__3__6b (C) (Q) (F) (E) (H71) H19).
--------------------------------------------------------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M Q) /\ (euclidean__axioms.BetS C M B)) as H79.
---------------------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (A) (C) (E) (B) (Q) (H8) (H78) H77).
---------------------------------------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M Q) /\ (euclidean__axioms.BetS C M B))) as H80.
----------------------------------------------------------------------------------- exact H79.
----------------------------------------------------------------------------------- destruct H80 as [M H80].
assert (* AndElim *) ((euclidean__axioms.BetS A M Q) /\ (euclidean__axioms.BetS C M B)) as H81.
------------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* Cut *) (euclidean__axioms.BetS A M D) as H83.
------------------------------------------------------------------------------------- apply (@lemma__3__6b.lemma__3__6b (A) (M) (Q) (D) (H81) H60).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B M C) as H84.
-------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (M) (B) H82).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CR A D B C) as H85.
--------------------------------------------------------------------------------------- exists M.
split.
---------------------------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------------- exact H85.
------------------------------- exact H34.
Qed.
