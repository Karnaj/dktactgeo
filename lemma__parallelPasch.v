Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__samesidesymmetric.
Require Export logic.
Definition lemma__parallelPasch : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__defs.PG A B C D) -> ((euclidean__axioms.BetS A D E) -> (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B X E) /\ (euclidean__axioms.BetS C X D))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
assert (* Cut *) (euclidean__defs.Par A B C D) as H1.
- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H1.
-- exact H.
-- destruct H1 as [H1 H2].
exact H1.
- assert (* Cut *) (euclidean__defs.Par A D B C) as H2.
-- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H2.
--- exact H.
--- destruct H2 as [H2 H3].
exact H3.
-- assert (* Cut *) (euclidean__defs.Par C D A B) as H3.
--- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (B) (C) (D) H1).
--- assert (* Cut *) (euclidean__defs.TP C D A B) as H4.
---- apply (@lemma__paralleldef2B.lemma__paralleldef2B (C) (D) (A) (B) H3).
---- assert (* Cut *) (euclidean__defs.OS A B C D) as H5.
----- assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__defs.Meet C D A B)) /\ (euclidean__defs.OS A B C D)))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__defs.Meet C D A B)) /\ (euclidean__defs.OS A B C D))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((~(euclidean__defs.Meet C D A B)) /\ (euclidean__defs.OS A B C D)) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
exact H10.
----- assert (* Cut *) (euclidean__defs.OS B A C D) as H6.
------ assert (* Cut *) ((euclidean__defs.OS B A C D) /\ ((euclidean__defs.OS A B D C) /\ (euclidean__defs.OS B A D C))) as H6.
------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (C) (D) (A) (B) H5).
------- assert (* AndElim *) ((euclidean__defs.OS B A C D) /\ ((euclidean__defs.OS A B D C) /\ (euclidean__defs.OS B A D C))) as H7.
-------- exact H6.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.OS A B D C) /\ (euclidean__defs.OS B A D C)) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
exact H7.
------ assert (* Cut *) (D = D) as H7.
------- apply (@logic.eq__refl (Point) D).
------- assert (* Cut *) (euclidean__axioms.neq A D) as H8.
-------- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H8.
--------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (D) (E) H0).
--------- assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H9.
---------- exact H8.
---------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E)) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
exact H11.
-------- assert (* Cut *) (euclidean__axioms.Col A D D) as H9.
--------- right.
right.
left.
exact H7.
--------- assert (* Cut *) (euclidean__axioms.Col A D E) as H10.
---------- right.
right.
right.
right.
left.
exact H0.
---------- assert (* Cut *) (euclidean__axioms.Col D D E) as H11.
----------- apply (@euclidean__tactics.not__nCol__Col (D) (D) (E)).
------------intro H11.
apply (@euclidean__tactics.Col__nCol__False (D) (D) (E) (H11)).
-------------apply (@lemma__collinear4.lemma__collinear4 (A) (D) (D) (E) (H9) (H10) H8).


----------- assert (* Cut *) (euclidean__axioms.Col E D D) as H12.
------------ assert (* Cut *) ((euclidean__axioms.Col D D E) /\ ((euclidean__axioms.Col D E D) /\ ((euclidean__axioms.Col E D D) /\ ((euclidean__axioms.Col D E D) /\ (euclidean__axioms.Col E D D))))) as H12.
------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (D) (E) H11).
------------- assert (* AndElim *) ((euclidean__axioms.Col D D E) /\ ((euclidean__axioms.Col D E D) /\ ((euclidean__axioms.Col E D D) /\ ((euclidean__axioms.Col D E D) /\ (euclidean__axioms.Col E D D))))) as H13.
-------------- exact H12.
-------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col D E D) /\ ((euclidean__axioms.Col E D D) /\ ((euclidean__axioms.Col D E D) /\ (euclidean__axioms.Col E D D)))) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col E D D) /\ ((euclidean__axioms.Col D E D) /\ (euclidean__axioms.Col E D D))) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col D E D) /\ (euclidean__axioms.Col E D D)) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
exact H20.
------------ assert (* Cut *) (euclidean__axioms.Col C D D) as H13.
------------- right.
right.
left.
exact H7.
------------- assert (* Cut *) (euclidean__axioms.nCol A C D) as H14.
-------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H14.
--------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (C) (D) H1).
--------------- assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H15.
---------------- exact H14.
---------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D))) as H17.
----------------- exact H16.
----------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
exact H17.
-------------- assert (* Cut *) (euclidean__axioms.nCol C D A) as H15.
--------------- assert (* Cut *) ((euclidean__axioms.nCol C A D) /\ ((euclidean__axioms.nCol C D A) /\ ((euclidean__axioms.nCol D A C) /\ ((euclidean__axioms.nCol A D C) /\ (euclidean__axioms.nCol D C A))))) as H15.
---------------- apply (@lemma__NCorder.lemma__NCorder (A) (C) (D) H14).
---------------- assert (* AndElim *) ((euclidean__axioms.nCol C A D) /\ ((euclidean__axioms.nCol C D A) /\ ((euclidean__axioms.nCol D A C) /\ ((euclidean__axioms.nCol A D C) /\ (euclidean__axioms.nCol D C A))))) as H16.
----------------- exact H15.
----------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol C D A) /\ ((euclidean__axioms.nCol D A C) /\ ((euclidean__axioms.nCol A D C) /\ (euclidean__axioms.nCol D C A)))) as H18.
------------------ exact H17.
------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol D A C) /\ ((euclidean__axioms.nCol A D C) /\ (euclidean__axioms.nCol D C A))) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.nCol A D C) /\ (euclidean__axioms.nCol D C A)) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
exact H18.
--------------- assert (* Cut *) (euclidean__axioms.TS A C D E) as H16.
---------------- exists D.
split.
----------------- exact H0.
----------------- split.
------------------ exact H13.
------------------ exact H15.
---------------- assert (* Cut *) (euclidean__axioms.TS B C D E) as H17.
----------------- apply (@lemma__planeseparation.lemma__planeseparation (C) (D) (B) (A) (E) (H6) H16).
----------------- assert (* Cut *) (exists (H18: euclidean__axioms.Point), (euclidean__axioms.BetS B H18 E) /\ ((euclidean__axioms.Col C D H18) /\ (euclidean__axioms.nCol C D B))) as H18.
------------------ exact H17.
------------------ assert (exists H19: euclidean__axioms.Point, ((euclidean__axioms.BetS B H19 E) /\ ((euclidean__axioms.Col C D H19) /\ (euclidean__axioms.nCol C D B)))) as H20.
------------------- exact H18.
------------------- destruct H20 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.BetS B H19 E) /\ ((euclidean__axioms.Col C D H19) /\ (euclidean__axioms.nCol C D B))) as H21.
-------------------- exact H20.
-------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col C D H19) /\ (euclidean__axioms.nCol C D B)) as H23.
--------------------- exact H22.
--------------------- destruct H23 as [H23 H24].
assert (* Cut *) (euclidean__axioms.BetS E H19 B) as H25.
---------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (H19) (E) H21).
---------------------- assert (* Cut *) (euclidean__axioms.Col D C H19) as H26.
----------------------- assert (* Cut *) ((euclidean__axioms.Col D C H19) /\ ((euclidean__axioms.Col D H19 C) /\ ((euclidean__axioms.Col H19 C D) /\ ((euclidean__axioms.Col C H19 D) /\ (euclidean__axioms.Col H19 D C))))) as H26.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (H19) H23).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col D C H19) /\ ((euclidean__axioms.Col D H19 C) /\ ((euclidean__axioms.Col H19 C D) /\ ((euclidean__axioms.Col C H19 D) /\ (euclidean__axioms.Col H19 D C))))) as H27.
------------------------- exact H26.
------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col D H19 C) /\ ((euclidean__axioms.Col H19 C D) /\ ((euclidean__axioms.Col C H19 D) /\ (euclidean__axioms.Col H19 D C)))) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col H19 C D) /\ ((euclidean__axioms.Col C H19 D) /\ (euclidean__axioms.Col H19 D C))) as H31.
--------------------------- exact H30.
--------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col C H19 D) /\ (euclidean__axioms.Col H19 D C)) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
exact H27.
----------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H27.
------------------------ exact H8.
------------------------ assert (* Cut *) (~(euclidean__defs.Meet A D B C)) as H28.
------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H28.
-------------------------- exact H3.
-------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
--------------------------- exact H28.
--------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H29.
---------------------------- exact __TmpHyp.
---------------------------- destruct H29 as [x H29].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H30.
----------------------------- exact H29.
----------------------------- destruct H30 as [x0 H30].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H31.
------------------------------ exact H30.
------------------------------ destruct H31 as [x1 H31].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H32.
------------------------------- exact H31.
------------------------------- destruct H32 as [x2 H32].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H33.
-------------------------------- exact H32.
-------------------------------- destruct H33 as [x3 H33].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H34.
--------------------------------- exact H33.
--------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H36.
---------------------------------- exact H35.
---------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H38.
----------------------------------- exact H37.
----------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H44.
-------------------------------------- exact H43.
-------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H48.
---------------------------------------- exact H47.
---------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H50.
----------------------------------------- exact H49.
----------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H52.
------------------------------------------ exact H51.
------------------------------------------ destruct H52 as [H52 H53].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H54.
------------------------------------------- exact H2.
------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
-------------------------------------------- exact H54.
-------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H55.
--------------------------------------------- exact __TmpHyp0.
--------------------------------------------- destruct H55 as [x4 H55].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H56.
---------------------------------------------- exact H55.
---------------------------------------------- destruct H56 as [x5 H56].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H57.
----------------------------------------------- exact H56.
----------------------------------------------- destruct H57 as [x6 H57].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H58.
------------------------------------------------ exact H57.
------------------------------------------------ destruct H58 as [x7 H58].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H59.
------------------------------------------------- exact H58.
------------------------------------------------- destruct H59 as [x8 H59].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H60.
-------------------------------------------------- exact H59.
-------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H62.
--------------------------------------------------- exact H61.
--------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H64.
---------------------------------------------------- exact H63.
---------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H66.
----------------------------------------------------- exact H65.
----------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H68.
------------------------------------------------------ exact H67.
------------------------------------------------------ destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H70.
------------------------------------------------------- exact H69.
------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H72.
-------------------------------------------------------- exact H71.
-------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H74.
--------------------------------------------------------- exact H73.
--------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H76.
---------------------------------------------------------- exact H75.
---------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H78.
----------------------------------------------------------- exact H77.
----------------------------------------------------------- destruct H78 as [H78 H79].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H80.
------------------------------------------------------------ exact H1.
------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
------------------------------------------------------------- exact H80.
------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H81.
-------------------------------------------------------------- exact __TmpHyp1.
-------------------------------------------------------------- destruct H81 as [x9 H81].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H82.
--------------------------------------------------------------- exact H81.
--------------------------------------------------------------- destruct H82 as [x10 H82].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H83.
---------------------------------------------------------------- exact H82.
---------------------------------------------------------------- destruct H83 as [x11 H83].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H84.
----------------------------------------------------------------- exact H83.
----------------------------------------------------------------- destruct H84 as [x12 H84].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H85.
------------------------------------------------------------------ exact H84.
------------------------------------------------------------------ destruct H85 as [x13 H85].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H86.
------------------------------------------------------------------- exact H85.
------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H88.
-------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H90.
--------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H92.
---------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H94.
----------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H96.
------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------ destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H98.
------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H100.
-------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H102.
--------------------------------------------------------------------------- exact H101.
--------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H104.
---------------------------------------------------------------------------- exact H103.
---------------------------------------------------------------------------- destruct H104 as [H104 H105].
exact H76.
------------------------- assert (* Cut *) (~(euclidean__defs.Meet E D C B)) as H29.
-------------------------- intro H29.
assert (* Cut *) (exists (p: euclidean__axioms.Point), (euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col E D p) /\ (euclidean__axioms.Col C B p)))) as H30.
--------------------------- exact H29.
--------------------------- assert (exists p: euclidean__axioms.Point, ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col E D p) /\ (euclidean__axioms.Col C B p))))) as H31.
---------------------------- exact H30.
---------------------------- destruct H31 as [p H31].
assert (* AndElim *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col E D p) /\ (euclidean__axioms.Col C B p)))) as H32.
----------------------------- exact H31.
----------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col E D p) /\ (euclidean__axioms.Col C B p))) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col E D p) /\ (euclidean__axioms.Col C B p)) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
assert (* Cut *) (euclidean__axioms.neq B C) as H38.
-------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (B) H34).
-------------------------------- assert (* Cut *) (euclidean__axioms.Col B C p) as H39.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C p) /\ ((euclidean__axioms.Col B p C) /\ ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C))))) as H39.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (p) H37).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C p) /\ ((euclidean__axioms.Col B p C) /\ ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C))))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col B p C) /\ ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C)))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C)) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
exact H40.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col E D A) as H40.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H40.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (E) H10).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)))) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A)) as H47.
--------------------------------------- exact H46.
--------------------------------------- destruct H47 as [H47 H48].
exact H48.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col D A p) as H41.
----------------------------------- apply (@euclidean__tactics.not__nCol__Col (D) (A) (p)).
------------------------------------intro H41.
apply (@euclidean__tactics.Col__nCol__False (D) (A) (p) (H41)).
-------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (D) (A) (p) (H40) (H36) H32).


----------------------------------- assert (* Cut *) (euclidean__axioms.Col A D p) as H42.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A D p) /\ ((euclidean__axioms.Col A p D) /\ ((euclidean__axioms.Col p D A) /\ ((euclidean__axioms.Col D p A) /\ (euclidean__axioms.Col p A D))))) as H42.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (A) (p) H41).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A D p) /\ ((euclidean__axioms.Col A p D) /\ ((euclidean__axioms.Col p D A) /\ ((euclidean__axioms.Col D p A) /\ (euclidean__axioms.Col p A D))))) as H43.
-------------------------------------- exact H42.
-------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col A p D) /\ ((euclidean__axioms.Col p D A) /\ ((euclidean__axioms.Col D p A) /\ (euclidean__axioms.Col p A D)))) as H45.
--------------------------------------- exact H44.
--------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col p D A) /\ ((euclidean__axioms.Col D p A) /\ (euclidean__axioms.Col p A D))) as H47.
---------------------------------------- exact H46.
---------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col D p A) /\ (euclidean__axioms.Col p A D)) as H49.
----------------------------------------- exact H48.
----------------------------------------- destruct H49 as [H49 H50].
exact H43.
------------------------------------ assert (* Cut *) (euclidean__defs.Meet A D B C) as H43.
------------------------------------- exists p.
split.
-------------------------------------- exact H27.
-------------------------------------- split.
--------------------------------------- exact H38.
--------------------------------------- split.
---------------------------------------- exact H42.
---------------------------------------- exact H39.
------------------------------------- apply (@H28 H43).
-------------------------- assert (* Cut *) (C = C) as H30.
--------------------------- apply (@logic.eq__refl (Point) C).
--------------------------- assert (* Cut *) (euclidean__axioms.neq D E) as H31.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H31.
----------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (D) (E) H0).
----------------------------- assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E)) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
exact H32.
---------------------------- assert (* Cut *) (euclidean__axioms.neq E D) as H32.
----------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (E) H31).
----------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H33.
------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H33.
------------------------------- exact H3.
------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
-------------------------------- exact H33.
-------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H34.
--------------------------------- exact __TmpHyp.
--------------------------------- destruct H34 as [x H34].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H35.
---------------------------------- exact H34.
---------------------------------- destruct H35 as [x0 H35].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H36.
----------------------------------- exact H35.
----------------------------------- destruct H36 as [x1 H36].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H37.
------------------------------------ exact H36.
------------------------------------ destruct H37 as [x2 H37].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H38.
------------------------------------- exact H37.
------------------------------------- destruct H38 as [x3 H38].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H39.
-------------------------------------- exact H38.
-------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H41.
--------------------------------------- exact H40.
--------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col C D x) /\ ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H43.
---------------------------------------- exact H42.
---------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col C D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H45.
----------------------------------------- exact H44.
----------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H47.
------------------------------------------ exact H46.
------------------------------------------ destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H49.
------------------------------------------- exact H48.
------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col A B x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H51.
-------------------------------------------- exact H50.
-------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H53.
--------------------------------------------- exact H52.
--------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H55.
---------------------------------------------- exact H54.
---------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H57.
----------------------------------------------- exact H56.
----------------------------------------------- destruct H57 as [H57 H58].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H59.
------------------------------------------------ exact H2.
------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------------------------------- exact H59.
------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H60.
-------------------------------------------------- exact __TmpHyp0.
-------------------------------------------------- destruct H60 as [x4 H60].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H61.
--------------------------------------------------- exact H60.
--------------------------------------------------- destruct H61 as [x5 H61].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H62.
---------------------------------------------------- exact H61.
---------------------------------------------------- destruct H62 as [x6 H62].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H63.
----------------------------------------------------- exact H62.
----------------------------------------------------- destruct H63 as [x7 H63].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H64.
------------------------------------------------------ exact H63.
------------------------------------------------------ destruct H64 as [x8 H64].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H65.
------------------------------------------------------- exact H64.
------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H67.
-------------------------------------------------------- exact H66.
-------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col A D x4) /\ ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H69.
--------------------------------------------------------- exact H68.
--------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H71.
---------------------------------------------------------- exact H70.
---------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H73.
----------------------------------------------------------- exact H72.
----------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col B C x6) /\ ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H75.
------------------------------------------------------------ exact H74.
------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col B C x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H77.
------------------------------------------------------------- exact H76.
------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H79.
-------------------------------------------------------------- exact H78.
-------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H81.
--------------------------------------------------------------- exact H80.
--------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H83.
---------------------------------------------------------------- exact H82.
---------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H85.
----------------------------------------------------------------- exact H1.
----------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
------------------------------------------------------------------ exact H85.
------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H86.
------------------------------------------------------------------- exact __TmpHyp1.
------------------------------------------------------------------- destruct H86 as [x9 H86].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H87.
-------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------- destruct H87 as [x10 H87].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H88.
--------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------- destruct H88 as [x11 H88].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H89.
---------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------- destruct H89 as [x12 H89].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H90.
----------------------------------------------------------------------- exact H89.
----------------------------------------------------------------------- destruct H90 as [x13 H90].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H91.
------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------ destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H93.
------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H95.
-------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H97.
--------------------------------------------------------------------------- exact H96.
--------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H99.
---------------------------------------------------------------------------- exact H98.
---------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.Col C D x11) /\ ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H101.
----------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.Col C D x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H103.
------------------------------------------------------------------------------ exact H102.
------------------------------------------------------------------------------ destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H105.
------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H107.
-------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H109.
--------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------- destruct H109 as [H109 H110].
exact H67.
------------------------------ assert (* Cut *) (euclidean__axioms.neq C B) as H34.
------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H33).
------------------------------- assert (* Cut *) (euclidean__axioms.Col C C B) as H35.
-------------------------------- left.
exact H30.
-------------------------------- assert (* Cut *) (euclidean__axioms.BetS D H19 C) as H36.
--------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (E) (D) (C) (B) (D) (C) (H19) (H12) (H35) (H32) (H34) (H32) (H34) (H29) (H25) H26).
--------------------------------- assert (* Cut *) (euclidean__axioms.BetS C H19 D) as H37.
---------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (H19) (C) H36).
---------------------------------- exists H19.
split.
----------------------------------- exact H21.
----------------------------------- exact H37.
Qed.
