Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglessymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__interior5.
Require Export lemma__layoff.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__ray5.
Require Export lemma__sameside2.
Require Export lemma__samesidecollinear.
Require Export lemma__samesideflip.
Require Export lemma__samesidesymmetric.
Require Export lemma__samesidetransitive.
Require Export logic.
Require Export proposition__04.
Require Export proposition__23C.
Require Export proposition__42.
Definition proposition__42B : forall (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (J: euclidean__axioms.Point) (K: euclidean__axioms.Point) (R: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__axioms.Triangle a b c) -> ((euclidean__defs.Midpoint b e c) -> ((euclidean__axioms.nCol J D K) -> ((euclidean__defs.Midpoint B E C) -> ((euclidean__axioms.Cong E C e c) -> ((euclidean__axioms.nCol R E C) -> (exists (X: euclidean__axioms.Point) (Z: euclidean__axioms.Point), (euclidean__defs.PG X E C Z) /\ ((euclidean__axioms.EF a b e c X E C Z) /\ ((euclidean__defs.CongA C E X J D K) /\ (euclidean__defs.OS R X E C))))))))).
Proof.
intro B.
intro C.
intro D.
intro E.
intro J.
intro K.
intro R.
intro a.
intro b.
intro c.
intro e.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
assert (* Cut *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H5.
- assert (* Cut *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H5.
-- exact H2.
-- assert (* Cut *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as __TmpHyp.
--- exact H5.
--- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H6.
---- exact __TmpHyp.
---- destruct H6 as [H6 H7].
assert (* Cut *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H8.
----- exact H0.
----- assert (* Cut *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as __TmpHyp0.
------ exact H8.
------ assert (* AndElim *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H9.
------- exact __TmpHyp0.
------- destruct H9 as [H9 H10].
split.
-------- exact H6.
-------- exact H7.
- assert (* Cut *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H6.
-- assert (* Cut *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H6.
--- exact H5.
--- assert (* Cut *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as __TmpHyp.
---- exact H6.
---- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H7.
----- exact __TmpHyp.
----- destruct H7 as [H7 H8].
assert (* Cut *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H9.
------ exact H2.
------ assert (* Cut *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as __TmpHyp0.
------- exact H9.
------- assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H10.
-------- exact __TmpHyp0.
-------- destruct H10 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H12.
--------- exact H0.
--------- assert (* Cut *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as __TmpHyp1.
---------- exact H12.
---------- assert (* AndElim *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H13.
----------- exact __TmpHyp1.
----------- destruct H13 as [H13 H14].
split.
------------ exact H13.
------------ exact H14.
-- assert (* Cut *) (euclidean__axioms.neq B C) as H7.
--- assert (* AndElim *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H7.
---- exact H6.
---- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H9.
----- exact H5.
----- destruct H9 as [H9 H10].
assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H11.
------ apply (@lemma__betweennotequal.lemma__betweennotequal (B) (E) (C) H9).
------ assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H12.
------- exact H11.
------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C)) as H14.
-------- exact H13.
-------- destruct H14 as [H14 H15].
exact H15.
--- assert (* Cut *) (euclidean__axioms.nCol a b c) as H8.
---- assert (* AndElim *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H8.
----- exact H6.
----- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H10.
------ exact H5.
------ destruct H10 as [H10 H11].
exact H.
---- assert (* Cut *) (euclidean__axioms.nCol E C R) as H9.
----- assert (* AndElim *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H9.
------ exact H6.
------ destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H11.
------- exact H5.
------- destruct H11 as [H11 H12].
assert (* Cut *) ((euclidean__axioms.nCol E R C) /\ ((euclidean__axioms.nCol E C R) /\ ((euclidean__axioms.nCol C R E) /\ ((euclidean__axioms.nCol R C E) /\ (euclidean__axioms.nCol C E R))))) as H13.
-------- apply (@lemma__NCorder.lemma__NCorder (R) (E) (C) H4).
-------- assert (* AndElim *) ((euclidean__axioms.nCol E R C) /\ ((euclidean__axioms.nCol E C R) /\ ((euclidean__axioms.nCol C R E) /\ ((euclidean__axioms.nCol R C E) /\ (euclidean__axioms.nCol C E R))))) as H14.
--------- exact H13.
--------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.nCol E C R) /\ ((euclidean__axioms.nCol C R E) /\ ((euclidean__axioms.nCol R C E) /\ (euclidean__axioms.nCol C E R)))) as H16.
---------- exact H15.
---------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol C R E) /\ ((euclidean__axioms.nCol R C E) /\ (euclidean__axioms.nCol C E R))) as H18.
----------- exact H17.
----------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol R C E) /\ (euclidean__axioms.nCol C E R)) as H20.
------------ exact H19.
------------ destruct H20 as [H20 H21].
exact H16.
----- assert (* Cut *) (euclidean__axioms.Col B E C) as H10.
------ assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H10.
------- exact H5.
------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H12.
-------- exact H6.
-------- destruct H12 as [H12 H13].
right.
right.
right.
right.
left.
exact H10.
------ assert (* Cut *) (euclidean__axioms.Col E C B) as H11.
------- assert (* AndElim *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H11.
-------- exact H6.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H13.
--------- exact H5.
--------- destruct H13 as [H13 H14].
assert (* Cut *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H15.
---------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (C) H10).
---------- assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B)))) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))) as H20.
------------- exact H19.
------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B)) as H22.
-------------- exact H21.
-------------- destruct H22 as [H22 H23].
exact H18.
------- assert (* Cut *) (C = C) as H12.
-------- assert (* AndElim *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H12.
--------- exact H6.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H14.
---------- exact H5.
---------- destruct H14 as [H14 H15].
apply (@logic.eq__refl (Point) C).
-------- assert (* Cut *) (euclidean__axioms.Col E C C) as H13.
--------- right.
right.
left.
exact H12.
--------- assert (* Cut *) (euclidean__axioms.nCol B C R) as H14.
---------- assert (* AndElim *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H14.
----------- exact H6.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H16.
------------ exact H5.
------------ destruct H16 as [H16 H17].
apply (@euclidean__tactics.nCol__notCol (B) (C) (R)).
-------------apply (@euclidean__tactics.nCol__not__Col (B) (C) (R)).
--------------apply (@lemma__NChelper.lemma__NChelper (E) (C) (R) (B) (C) (H9) (H11) (H13) H7).


---------- assert (* Cut *) (exists (P: euclidean__axioms.Point) (H15: euclidean__axioms.Point), (euclidean__defs.Out B C H15) /\ ((euclidean__defs.CongA P B H15 a b c) /\ (euclidean__defs.OS P R B C))) as H15.
----------- assert (* AndElim *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H15.
------------ exact H6.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H17.
------------- exact H5.
------------- destruct H17 as [H17 H18].
apply (@proposition__23C.proposition__23C (B) (C) (b) (a) (c) (R) (H7) (H8) H14).
----------- assert (exists P: euclidean__axioms.Point, (exists (H16: euclidean__axioms.Point), (euclidean__defs.Out B C H16) /\ ((euclidean__defs.CongA P B H16 a b c) /\ (euclidean__defs.OS P R B C)))) as H16.
------------ exact H15.
------------ destruct H16 as [P H16].
assert (exists H17: euclidean__axioms.Point, ((euclidean__defs.Out B C H17) /\ ((euclidean__defs.CongA P B H17 a b c) /\ (euclidean__defs.OS P R B C)))) as H18.
------------- exact H16.
------------- destruct H18 as [H17 H18].
assert (* AndElim *) ((euclidean__defs.Out B C H17) /\ ((euclidean__defs.CongA P B H17 a b c) /\ (euclidean__defs.OS P R B C))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__defs.CongA P B H17 a b c) /\ (euclidean__defs.OS P R B C)) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS b e c) /\ (euclidean__axioms.Cong b e e c)) as H23.
---------------- exact H6.
---------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H25.
----------------- exact H5.
----------------- destruct H25 as [H25 H26].
assert (* Cut *) (euclidean__axioms.Cong B E e c) as H27.
------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (E) (E) (C) (e) (c) (H26) H3).
------------------ assert (* Cut *) (euclidean__axioms.Cong E C B E) as H28.
------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (B) (E) (C) H26).
------------------- assert (* Cut *) (euclidean__axioms.Cong E C e c) as H29.
-------------------- exact H3.
-------------------- assert (* Cut *) (euclidean__axioms.Cong B E e c) as H30.
--------------------- exact H27.
--------------------- assert (* Cut *) (euclidean__axioms.Cong e c b e) as H31.
---------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (e) (b) (e) (c) H24).
---------------------- assert (* Cut *) (euclidean__axioms.Cong B E b e) as H32.
----------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (E) (e) (c) (b) (e) (H30) H31).
----------------------- assert (* Cut *) (euclidean__axioms.Cong B C b c) as H33.
------------------------ apply (@euclidean__axioms.cn__sumofparts (B) (E) (C) (b) (e) (c) (H32) (H29) (H25) H23).
------------------------ assert (* Cut *) (euclidean__defs.CongA a b c P B H17) as H34.
------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (P) (B) (H17) (a) (b) (c) H21).
------------------------- assert (* Cut *) (euclidean__defs.Out B H17 C) as H35.
-------------------------- apply (@lemma__ray5.lemma__ray5 (B) (C) (H17) H19).
-------------------------- assert (* Cut *) (euclidean__axioms.nCol B C P) as H36.
--------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS R V X) /\ ((euclidean__axioms.nCol B C P) /\ (euclidean__axioms.nCol B C R)))))) as H36.
---------------------------- exact H22.
---------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS R V X) /\ ((euclidean__axioms.nCol B C P) /\ (euclidean__axioms.nCol B C R)))))) as __TmpHyp.
----------------------------- exact H36.
----------------------------- assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS R V X) /\ ((euclidean__axioms.nCol B C P) /\ (euclidean__axioms.nCol B C R))))))) as H37.
------------------------------ exact __TmpHyp.
------------------------------ destruct H37 as [x H37].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.BetS P U x) /\ ((euclidean__axioms.BetS R V x) /\ ((euclidean__axioms.nCol B C P) /\ (euclidean__axioms.nCol B C R))))))) as H38.
------------------------------- exact H37.
------------------------------- destruct H38 as [x0 H38].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col B C x0) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.BetS P x0 x) /\ ((euclidean__axioms.BetS R V x) /\ ((euclidean__axioms.nCol B C P) /\ (euclidean__axioms.nCol B C R))))))) as H39.
-------------------------------- exact H38.
-------------------------------- destruct H39 as [x1 H39].
assert (* AndElim *) ((euclidean__axioms.Col B C x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.BetS P x0 x) /\ ((euclidean__axioms.BetS R x1 x) /\ ((euclidean__axioms.nCol B C P) /\ (euclidean__axioms.nCol B C R)))))) as H40.
--------------------------------- exact H39.
--------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.BetS P x0 x) /\ ((euclidean__axioms.BetS R x1 x) /\ ((euclidean__axioms.nCol B C P) /\ (euclidean__axioms.nCol B C R))))) as H42.
---------------------------------- exact H41.
---------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.BetS P x0 x) /\ ((euclidean__axioms.BetS R x1 x) /\ ((euclidean__axioms.nCol B C P) /\ (euclidean__axioms.nCol B C R)))) as H44.
----------------------------------- exact H43.
----------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.BetS R x1 x) /\ ((euclidean__axioms.nCol B C P) /\ (euclidean__axioms.nCol B C R))) as H46.
------------------------------------ exact H45.
------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.nCol B C P) /\ (euclidean__axioms.nCol B C R)) as H48.
------------------------------------- exact H47.
------------------------------------- destruct H48 as [H48 H49].
exact H48.
--------------------------- assert (* Cut *) (euclidean__axioms.neq B P) as H37.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq C P) /\ ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq P C) /\ (euclidean__axioms.neq P B)))))) as H37.
----------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (B) (C) (P) H36).
----------------------------- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq C P) /\ ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq P C) /\ (euclidean__axioms.neq P B)))))) as H38.
------------------------------ exact H37.
------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq C P) /\ ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq P C) /\ (euclidean__axioms.neq P B))))) as H40.
------------------------------- exact H39.
------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq P C) /\ (euclidean__axioms.neq P B)))) as H42.
-------------------------------- exact H41.
-------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq P C) /\ (euclidean__axioms.neq P B))) as H44.
--------------------------------- exact H43.
--------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq P C) /\ (euclidean__axioms.neq P B)) as H46.
---------------------------------- exact H45.
---------------------------------- destruct H46 as [H46 H47].
exact H42.
---------------------------- assert (* Cut *) (euclidean__axioms.nCol a b c) as H38.
----------------------------- exact H8.
----------------------------- assert (* Cut *) (euclidean__axioms.neq b a) as H39.
------------------------------ assert (* Cut *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a)))))) as H39.
------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (a) (b) (c) H38).
------------------------------- assert (* AndElim *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a)))))) as H40.
-------------------------------- exact H39.
-------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a))))) as H42.
--------------------------------- exact H41.
--------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a)))) as H44.
---------------------------------- exact H43.
---------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq b a) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a))) as H46.
----------------------------------- exact H45.
----------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c a)) as H48.
------------------------------------ exact H47.
------------------------------------ destruct H48 as [H48 H49].
exact H46.
------------------------------ assert (* Cut *) (exists (A: euclidean__axioms.Point), (euclidean__defs.Out B P A) /\ (euclidean__axioms.Cong B A b a)) as H40.
------------------------------- apply (@lemma__layoff.lemma__layoff (B) (P) (b) (a) (H37) H39).
------------------------------- assert (exists A: euclidean__axioms.Point, ((euclidean__defs.Out B P A) /\ (euclidean__axioms.Cong B A b a))) as H41.
-------------------------------- exact H40.
-------------------------------- destruct H41 as [A H41].
assert (* AndElim *) ((euclidean__defs.Out B P A) /\ (euclidean__axioms.Cong B A b a)) as H42.
--------------------------------- exact H41.
--------------------------------- destruct H42 as [H42 H43].
assert (* Cut *) (euclidean__defs.CongA a b c A B C) as H44.
---------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (a) (b) (c) (P) (B) (H17) (A) (C) (H34) (H42) H35).
---------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C a b c) as H45.
----------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (a) (b) (c) (A) (B) (C) H44).
----------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H46.
------------------------------------ apply (@euclidean__tactics.nCol__notCol (A) (B) (C)).
-------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (B) (C)).
--------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (a) (b) (c) (A) (B) (C) H44).


------------------------------------ assert (* Cut *) (euclidean__axioms.Triangle A B C) as H47.
------------------------------------- exact H46.
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C a c) as H48.
-------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (a0: euclidean__axioms.Point) (b0: euclidean__axioms.Point) (c0: euclidean__axioms.Point), (euclidean__axioms.Cong A0 B0 a0 b0) -> ((euclidean__axioms.Cong A0 C0 a0 c0) -> ((euclidean__defs.CongA B0 A0 C0 b0 a0 c0) -> (euclidean__axioms.Cong B0 C0 b0 c0)))) as H48.
--------------------------------------- intro A0.
intro B0.
intro C0.
intro a0.
intro b0.
intro c0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b0 c0) /\ ((euclidean__defs.CongA A0 B0 C0 a0 b0 c0) /\ (euclidean__defs.CongA A0 C0 B0 a0 c0 b0))) as __2.
---------------------------------------- apply (@proposition__04.proposition__04 (A0) (B0) (C0) (a0) (b0) (c0) (__) (__0) __1).
---------------------------------------- destruct __2 as [__2 __3].
exact __2.
--------------------------------------- apply (@H48 (B) (A) (C) (b) (a) (c) (H43) (H33) H45).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B a b) as H49.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong A B a b) /\ ((euclidean__axioms.Cong A B b a) /\ (euclidean__axioms.Cong B A a b))) as H49.
---------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (A) (b) (a) H43).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A B a b) /\ ((euclidean__axioms.Cong A B b a) /\ (euclidean__axioms.Cong B A a b))) as H50.
----------------------------------------- exact H49.
----------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Cong A B b a) /\ (euclidean__axioms.Cong B A a b)) as H52.
------------------------------------------ exact H51.
------------------------------------------ destruct H52 as [H52 H53].
exact H50.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C A c a) as H50.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C A c a) /\ ((euclidean__axioms.Cong C A a c) /\ (euclidean__axioms.Cong A C c a))) as H50.
----------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (C) (a) (c) H48).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong C A c a) /\ ((euclidean__axioms.Cong C A a c) /\ (euclidean__axioms.Cong A C c a))) as H51.
------------------------------------------ exact H50.
------------------------------------------ destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Cong C A a c) /\ (euclidean__axioms.Cong A C c a)) as H53.
------------------------------------------- exact H52.
------------------------------------------- destruct H53 as [H53 H54].
exact H51.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E A e a) as H51.
----------------------------------------- apply (@lemma__interior5.lemma__interior5 (B) (E) (C) (A) (b) (e) (c) (a) (H25) (H23) (H32) (H29) (H43) H50).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A E a e) as H52.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong A E a e) /\ ((euclidean__axioms.Cong A E e a) /\ (euclidean__axioms.Cong E A a e))) as H52.
------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (E) (A) (e) (a) H51).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong A E a e) /\ ((euclidean__axioms.Cong A E e a) /\ (euclidean__axioms.Cong E A a e))) as H53.
-------------------------------------------- exact H52.
-------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Cong A E e a) /\ (euclidean__axioms.Cong E A a e)) as H55.
--------------------------------------------- exact H54.
--------------------------------------------- destruct H55 as [H55 H56].
exact H53.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong E B e b) as H53.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E B e b) /\ ((euclidean__axioms.Cong E B b e) /\ (euclidean__axioms.Cong B E e b))) as H53.
-------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (E) (b) (e) H32).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E B e b) /\ ((euclidean__axioms.Cong E B b e) /\ (euclidean__axioms.Cong B E e b))) as H54.
--------------------------------------------- exact H53.
--------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Cong E B b e) /\ (euclidean__axioms.Cong B E e b)) as H56.
---------------------------------------------- exact H55.
---------------------------------------------- destruct H56 as [H56 H57].
exact H54.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E C) as H54.
-------------------------------------------- exact H10.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C E) as H55.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H55.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (E) (C) H54).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H56.
----------------------------------------------- exact H55.
----------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B)))) as H58.
------------------------------------------------ exact H57.
------------------------------------------------ destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))) as H60.
------------------------------------------------- exact H59.
------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B)) as H62.
-------------------------------------------------- exact H61.
-------------------------------------------------- destruct H62 as [H62 H63].
exact H62.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C A) as H56.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H56.
----------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H47).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H57.
------------------------------------------------ exact H56.
------------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H59.
------------------------------------------------- exact H58.
------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H61.
-------------------------------------------------- exact H60.
-------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H63.
--------------------------------------------------- exact H62.
--------------------------------------------------- destruct H63 as [H63 H64].
exact H59.
---------------------------------------------- assert (* Cut *) (B = B) as H57.
----------------------------------------------- apply (@logic.eq__refl (Point) B).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C B) as H58.
------------------------------------------------ right.
left.
exact H57.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq B E) as H59.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H59.
-------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (E) (C) H25).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H60.
--------------------------------------------------- exact H59.
--------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C)) as H62.
---------------------------------------------------- exact H61.
---------------------------------------------------- destruct H62 as [H62 H63].
exact H62.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E A) as H60.
-------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (B) (E) (A)).
---------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (B) (E) (A)).
----------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (B) (C) (A) (B) (E) (H56) (H58) (H55) H59).


-------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E B) as H61.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B A) /\ ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol B A E) /\ (euclidean__axioms.nCol A E B))))) as H61.
---------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (E) (A) H60).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E B A) /\ ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol B A E) /\ (euclidean__axioms.nCol A E B))))) as H62.
----------------------------------------------------- exact H61.
----------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol B A E) /\ (euclidean__axioms.nCol A E B)))) as H64.
------------------------------------------------------ exact H63.
------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol B A E) /\ (euclidean__axioms.nCol A E B))) as H66.
------------------------------------------------------- exact H65.
------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.nCol B A E) /\ (euclidean__axioms.nCol A E B)) as H68.
-------------------------------------------------------- exact H67.
-------------------------------------------------------- destruct H68 as [H68 H69].
exact H69.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col b e c) as H62.
---------------------------------------------------- right.
right.
right.
right.
left.
exact H23.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col b c e) as H63.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col e b c) /\ ((euclidean__axioms.Col e c b) /\ ((euclidean__axioms.Col c b e) /\ ((euclidean__axioms.Col b c e) /\ (euclidean__axioms.Col c e b))))) as H63.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (b) (e) (c) H62).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col e b c) /\ ((euclidean__axioms.Col e c b) /\ ((euclidean__axioms.Col c b e) /\ ((euclidean__axioms.Col b c e) /\ (euclidean__axioms.Col c e b))))) as H64.
------------------------------------------------------- exact H63.
------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col e c b) /\ ((euclidean__axioms.Col c b e) /\ ((euclidean__axioms.Col b c e) /\ (euclidean__axioms.Col c e b)))) as H66.
-------------------------------------------------------- exact H65.
-------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col c b e) /\ ((euclidean__axioms.Col b c e) /\ (euclidean__axioms.Col c e b))) as H68.
--------------------------------------------------------- exact H67.
--------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col b c e) /\ (euclidean__axioms.Col c e b)) as H70.
---------------------------------------------------------- exact H69.
---------------------------------------------------------- destruct H70 as [H70 H71].
exact H70.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol b c a) as H64.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol b a c) /\ ((euclidean__axioms.nCol b c a) /\ ((euclidean__axioms.nCol c a b) /\ ((euclidean__axioms.nCol a c b) /\ (euclidean__axioms.nCol c b a))))) as H64.
------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (a) (b) (c) H38).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol b a c) /\ ((euclidean__axioms.nCol b c a) /\ ((euclidean__axioms.nCol c a b) /\ ((euclidean__axioms.nCol a c b) /\ (euclidean__axioms.nCol c b a))))) as H65.
-------------------------------------------------------- exact H64.
-------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.nCol b c a) /\ ((euclidean__axioms.nCol c a b) /\ ((euclidean__axioms.nCol a c b) /\ (euclidean__axioms.nCol c b a)))) as H67.
--------------------------------------------------------- exact H66.
--------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.nCol c a b) /\ ((euclidean__axioms.nCol a c b) /\ (euclidean__axioms.nCol c b a))) as H69.
---------------------------------------------------------- exact H68.
---------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.nCol a c b) /\ (euclidean__axioms.nCol c b a)) as H71.
----------------------------------------------------------- exact H70.
----------------------------------------------------------- destruct H71 as [H71 H72].
exact H67.
------------------------------------------------------ assert (* Cut *) (b = b) as H65.
------------------------------------------------------- apply (@logic.eq__refl (Point) b).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col b c b) as H66.
-------------------------------------------------------- right.
left.
exact H65.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq b e) as H67.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq e c) /\ ((euclidean__axioms.neq b e) /\ (euclidean__axioms.neq b c))) as H67.
---------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (b) (e) (c) H23).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq e c) /\ ((euclidean__axioms.neq b e) /\ (euclidean__axioms.neq b c))) as H68.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq b e) /\ (euclidean__axioms.neq b c)) as H70.
------------------------------------------------------------ exact H69.
------------------------------------------------------------ destruct H70 as [H70 H71].
exact H70.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol b e a) as H68.
---------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (b) (e) (a)).
-----------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (b) (e) (a)).
------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (b) (c) (a) (b) (e) (H64) (H66) (H63) H67).


---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol a e b) as H69.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol e b a) /\ ((euclidean__axioms.nCol e a b) /\ ((euclidean__axioms.nCol a b e) /\ ((euclidean__axioms.nCol b a e) /\ (euclidean__axioms.nCol a e b))))) as H69.
------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (b) (e) (a) H68).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol e b a) /\ ((euclidean__axioms.nCol e a b) /\ ((euclidean__axioms.nCol a b e) /\ ((euclidean__axioms.nCol b a e) /\ (euclidean__axioms.nCol a e b))))) as H70.
------------------------------------------------------------- exact H69.
------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.nCol e a b) /\ ((euclidean__axioms.nCol a b e) /\ ((euclidean__axioms.nCol b a e) /\ (euclidean__axioms.nCol a e b)))) as H72.
-------------------------------------------------------------- exact H71.
-------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.nCol a b e) /\ ((euclidean__axioms.nCol b a e) /\ (euclidean__axioms.nCol a e b))) as H74.
--------------------------------------------------------------- exact H73.
--------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.nCol b a e) /\ (euclidean__axioms.nCol a e b)) as H76.
---------------------------------------------------------------- exact H75.
---------------------------------------------------------------- destruct H76 as [H76 H77].
exact H77.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle A E B) as H70.
------------------------------------------------------------ exact H61.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong__3 A E B a e b) as H71.
------------------------------------------------------------- split.
-------------------------------------------------------------- exact H52.
-------------------------------------------------------------- split.
--------------------------------------------------------------- exact H53.
--------------------------------------------------------------- exact H49.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E B a e b) as H72.
-------------------------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal (A) (E) (B) (a) (e) (b) H71).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B E) as H73.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H73.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (E) H55).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H74.
----------------------------------------------------------------- exact H73.
----------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)))) as H76.
------------------------------------------------------------------ exact H75.
------------------------------------------------------------------ destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))) as H78.
------------------------------------------------------------------- exact H77.
------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)) as H80.
-------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------- destruct H80 as [H80 H81].
exact H74.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E C) as H74.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H74.
----------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (E) (C) H25).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H75.
------------------------------------------------------------------ exact H74.
------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C)) as H77.
------------------------------------------------------------------- exact H76.
------------------------------------------------------------------- destruct H77 as [H77 H78].
exact H75.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H75.
----------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (C) H74).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C B A) as H76.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H76.
------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (C) (A) H56).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H77.
-------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B)))) as H79.
--------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))) as H81.
---------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B)) as H83.
----------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------- destruct H83 as [H83 H84].
exact H77.
------------------------------------------------------------------ assert (* Cut *) (C = C) as H77.
------------------------------------------------------------------- exact H12.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B C) as H78.
-------------------------------------------------------------------- right.
left.
exact H77.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E A) as H79.
--------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (C) (E) (A)).
----------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (C) (E) (A)).
-----------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (C) (B) (A) (C) (E) (H76) (H78) (H73) H75).


--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E C) as H80.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol C A E) /\ (euclidean__axioms.nCol A E C))))) as H80.
----------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (C) (E) (A) H79).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol C A E) /\ (euclidean__axioms.nCol A E C))))) as H81.
------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol C A E) /\ (euclidean__axioms.nCol A E C)))) as H83.
------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol C A E) /\ (euclidean__axioms.nCol A E C))) as H85.
-------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.nCol C A E) /\ (euclidean__axioms.nCol A E C)) as H87.
--------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------- destruct H87 as [H87 H88].
exact H88.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle A E C) as H81.
----------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 A E C a e c) as H82.
------------------------------------------------------------------------ split.
------------------------------------------------------------------------- exact H52.
------------------------------------------------------------------------- split.
-------------------------------------------------------------------------- exact H29.
-------------------------------------------------------------------------- exact H48.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET A E C a e c) as H83.
------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal (A) (E) (C) (a) (e) (c) H82).
------------------------------------------------------------------------- assert (* Cut *) (E = E) as H84.
-------------------------------------------------------------------------- apply (@logic.eq__refl (Point) E).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E E) as H85.
--------------------------------------------------------------------------- right.
right.
left.
exact H84.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS B A E C) as H86.
---------------------------------------------------------------------------- exists E.
split.
----------------------------------------------------------------------------- exact H25.
----------------------------------------------------------------------------- split.
------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------ exact H70.
---------------------------------------------------------------------------- assert (* Cut *) (e = e) as H87.
----------------------------------------------------------------------------- apply (@logic.eq__refl (Point) e).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col a e e) as H88.
------------------------------------------------------------------------------ right.
right.
left.
exact H87.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS b a e c) as H89.
------------------------------------------------------------------------------- exists e.
split.
-------------------------------------------------------------------------------- exact H23.
-------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------------- exact H69.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B E C a b e c) as H90.
-------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__paste3 (A) (E) (B) (C) (E) (a) (e) (b) (c) (e) (H72) (H83) (H25)).
---------------------------------------------------------------------------------right.
right.
exact H84.

--------------------------------------------------------------------------------- exact H23.
---------------------------------------------------------------------------------right.
right.
exact H87.

-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF a b e c A B E C) as H91.
--------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (A) (B) (E) (C) (a) (b) (e) (c) H90).
--------------------------------------------------------------------------------- assert (* Cut *) (exists (F: euclidean__axioms.Point) (G: euclidean__axioms.Point), (euclidean__defs.PG F E C G) /\ ((euclidean__axioms.EF A B E C F E C G) /\ ((euclidean__defs.CongA C E F J D K) /\ (euclidean__axioms.Col F G A)))) as H92.
---------------------------------------------------------------------------------- apply (@proposition__42.proposition__42 (A) (B) (C) (D) (E) (J) (K) (H47) (H1) H2).
---------------------------------------------------------------------------------- assert (exists F: euclidean__axioms.Point, (exists (G: euclidean__axioms.Point), (euclidean__defs.PG F E C G) /\ ((euclidean__axioms.EF A B E C F E C G) /\ ((euclidean__defs.CongA C E F J D K) /\ (euclidean__axioms.Col F G A))))) as H93.
----------------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------------- destruct H93 as [F H93].
assert (exists G: euclidean__axioms.Point, ((euclidean__defs.PG F E C G) /\ ((euclidean__axioms.EF A B E C F E C G) /\ ((euclidean__defs.CongA C E F J D K) /\ (euclidean__axioms.Col F G A))))) as H94.
------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------ destruct H94 as [G H94].
assert (* AndElim *) ((euclidean__defs.PG F E C G) /\ ((euclidean__axioms.EF A B E C F E C G) /\ ((euclidean__defs.CongA C E F J D K) /\ (euclidean__axioms.Col F G A)))) as H95.
------------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.EF A B E C F E C G) /\ ((euclidean__defs.CongA C E F J D K) /\ (euclidean__axioms.Col F G A))) as H97.
-------------------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__defs.CongA C E F J D K) /\ (euclidean__axioms.Col F G A)) as H99.
--------------------------------------------------------------------------------------- exact H98.
--------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* Cut *) (euclidean__axioms.EF a b e c F E C G) as H101.
---------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFtransitive (a) (b) (e) (c) (F) (E) (C) (G) (A) (B) (E) (C) (H91) H97).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS R P B C) as H102.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS R P B C) /\ ((euclidean__defs.OS P R C B) /\ (euclidean__defs.OS R P C B))) as H102.
------------------------------------------------------------------------------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (B) (C) (P) (R) H22).
------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__defs.OS R P B C) /\ ((euclidean__defs.OS P R C B) /\ (euclidean__defs.OS R P C B))) as H103.
------------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__defs.OS P R C B) /\ (euclidean__defs.OS R P C B)) as H105.
-------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
exact H103.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B B C) as H103.
------------------------------------------------------------------------------------------ left.
exact H57.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS R A B C) as H104.
------------------------------------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 (B) (B) (C) (R) (P) (A) (H102) (H103) H42).
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS R A C B) as H105.
-------------------------------------------------------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip (B) (C) (R) (A) H104).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS R A C E) as H106.
--------------------------------------------------------------------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear (C) (B) (E) (R) (A) (H105) (H73) H75).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A R C E) as H107.
---------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS A R C E) /\ ((euclidean__defs.OS R A E C) /\ (euclidean__defs.OS A R E C))) as H107.
----------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (C) (E) (R) (A) H106).
----------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS A R C E) /\ ((euclidean__defs.OS R A E C) /\ (euclidean__defs.OS A R E C))) as H108.
------------------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------------------ destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__defs.OS R A E C) /\ (euclidean__defs.OS A R E C)) as H110.
------------------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
exact H108.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A R E C) as H108.
----------------------------------------------------------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip (C) (E) (A) (R) H107).
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G F A) as H109.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col G F A) /\ ((euclidean__axioms.Col G A F) /\ ((euclidean__axioms.Col A F G) /\ ((euclidean__axioms.Col F A G) /\ (euclidean__axioms.Col A G F))))) as H109.
------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (G) (A) H100).
------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G F A) /\ ((euclidean__axioms.Col G A F) /\ ((euclidean__axioms.Col A F G) /\ ((euclidean__axioms.Col F A G) /\ (euclidean__axioms.Col A G F))))) as H110.
-------------------------------------------------------------------------------------------------- exact H109.
-------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.Col G A F) /\ ((euclidean__axioms.Col A F G) /\ ((euclidean__axioms.Col F A G) /\ (euclidean__axioms.Col A G F)))) as H112.
--------------------------------------------------------------------------------------------------- exact H111.
--------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.Col A F G) /\ ((euclidean__axioms.Col F A G) /\ (euclidean__axioms.Col A G F))) as H114.
---------------------------------------------------------------------------------------------------- exact H113.
---------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Col F A G) /\ (euclidean__axioms.Col A G F)) as H116.
----------------------------------------------------------------------------------------------------- exact H115.
----------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
exact H110.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par F G E C) as H110.
------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par F E C G) /\ (euclidean__defs.Par F G E C)) as H110.
-------------------------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
exact H111.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E C F G) as H111.
-------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (F) (G) (E) (C) H110).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E C G F) as H112.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par C E F G) /\ ((euclidean__defs.Par E C G F) /\ (euclidean__defs.Par C E G F))) as H112.
---------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (E) (C) (F) (G) H111).
---------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par C E F G) /\ ((euclidean__defs.Par E C G F) /\ (euclidean__defs.Par C E G F))) as H113.
----------------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__defs.Par E C G F) /\ (euclidean__defs.Par C E G F)) as H115.
------------------------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------------------------ destruct H115 as [H115 H116].
exact H115.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS R F E C) as H113.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as H113.
----------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.eq__or__neq (A) F).
----------------------------------------------------------------------------------------------------- assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as H114.
------------------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((A = F) \/ (euclidean__axioms.neq A F)) as __TmpHyp.
------------------------------------------------------------------------------------------------------- exact H114.
------------------------------------------------------------------------------------------------------- assert (A = F \/ euclidean__axioms.neq A F) as H115.
-------------------------------------------------------------------------------------------------------- exact __TmpHyp.
-------------------------------------------------------------------------------------------------------- destruct H115 as [H115|H115].
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS R A E C) as H116.
---------------------------------------------------------------------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip (C) (E) (R) (A) H106).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS R F E C) as H117.
----------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun A0: euclidean__axioms.Point => (euclidean__defs.Out B P A0) -> ((euclidean__axioms.Cong B A0 b a) -> ((euclidean__defs.CongA a b c A0 B C) -> ((euclidean__defs.CongA A0 B C a b c) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__axioms.Triangle A0 B C) -> ((euclidean__axioms.Cong A0 C a c) -> ((euclidean__axioms.Cong A0 B a b) -> ((euclidean__axioms.Cong C A0 c a) -> ((euclidean__axioms.Cong E A0 e a) -> ((euclidean__axioms.Cong A0 E a e) -> ((euclidean__axioms.nCol B C A0) -> ((euclidean__axioms.nCol B E A0) -> ((euclidean__axioms.nCol A0 E B) -> ((euclidean__axioms.Triangle A0 E B) -> ((euclidean__axioms.Cong__3 A0 E B a e b) -> ((euclidean__axioms.ET A0 E B a e b) -> ((euclidean__axioms.nCol C B A0) -> ((euclidean__axioms.nCol C E A0) -> ((euclidean__axioms.nCol A0 E C) -> ((euclidean__axioms.Triangle A0 E C) -> ((euclidean__axioms.Cong__3 A0 E C a e c) -> ((euclidean__axioms.ET A0 E C a e c) -> ((euclidean__axioms.Col A0 E E) -> ((euclidean__axioms.TS B A0 E C) -> ((euclidean__axioms.EF A0 B E C a b e c) -> ((euclidean__axioms.EF a b e c A0 B E C) -> ((euclidean__axioms.EF A0 B E C F E C G) -> ((euclidean__axioms.Col F G A0) -> ((euclidean__defs.OS R A0 B C) -> ((euclidean__defs.OS R A0 C B) -> ((euclidean__defs.OS R A0 C E) -> ((euclidean__defs.OS A0 R C E) -> ((euclidean__defs.OS A0 R E C) -> ((euclidean__axioms.Col G F A0) -> ((euclidean__defs.OS R A0 E C) -> (euclidean__defs.OS R F E C)))))))))))))))))))))))))))))))))))))) with (x := A).
------------------------------------------------------------------------------------------------------------intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
exact H152.

------------------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------------------ exact H42.
------------------------------------------------------------------------------------------------------------ exact H43.
------------------------------------------------------------------------------------------------------------ exact H44.
------------------------------------------------------------------------------------------------------------ exact H45.
------------------------------------------------------------------------------------------------------------ exact H46.
------------------------------------------------------------------------------------------------------------ exact H47.
------------------------------------------------------------------------------------------------------------ exact H48.
------------------------------------------------------------------------------------------------------------ exact H49.
------------------------------------------------------------------------------------------------------------ exact H50.
------------------------------------------------------------------------------------------------------------ exact H51.
------------------------------------------------------------------------------------------------------------ exact H52.
------------------------------------------------------------------------------------------------------------ exact H56.
------------------------------------------------------------------------------------------------------------ exact H60.
------------------------------------------------------------------------------------------------------------ exact H61.
------------------------------------------------------------------------------------------------------------ exact H70.
------------------------------------------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------------------------------------------ exact H72.
------------------------------------------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------------------------------------------ exact H79.
------------------------------------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------------------------ exact H109.
------------------------------------------------------------------------------------------------------------ exact H116.
----------------------------------------------------------------------------------------------------------- exact H117.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E C A F) as H116.
---------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (E) (C) (A) (G) (F) (H112) (H109) H115).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E C F A) as H117.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par C E A F) /\ ((euclidean__defs.Par E C F A) /\ (euclidean__defs.Par C E F A))) as H117.
------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip (E) (C) (A) (F) H116).
------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__defs.Par C E A F) /\ ((euclidean__defs.Par E C F A) /\ (euclidean__defs.Par C E F A))) as H118.
------------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__defs.Par E C F A) /\ (euclidean__defs.Par C E F A)) as H120.
-------------------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
exact H120.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP E C F A) as H118.
------------------------------------------------------------------------------------------------------------ apply (@lemma__paralleldef2B.lemma__paralleldef2B (E) (C) (F) (A) H117).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS F A E C) as H119.
------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F A) /\ ((~(euclidean__defs.Meet E C F A)) /\ (euclidean__defs.OS F A E C)))) as H119.
-------------------------------------------------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.neq F A) /\ ((~(euclidean__defs.Meet E C F A)) /\ (euclidean__defs.OS F A E C))) as H121.
--------------------------------------------------------------------------------------------------------------- exact H120.
--------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((~(euclidean__defs.Meet E C F A)) /\ (euclidean__defs.OS F A E C)) as H123.
---------------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
exact H124.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS F R E C) as H120.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__samesidetransitive.lemma__samesidetransitive (E) (C) (F) (A) (R) (H119) H108).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS R F E C) as H121.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS R F E C) /\ ((euclidean__defs.OS F R C E) /\ (euclidean__defs.OS R F C E))) as H121.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (E) (C) (F) (R) H120).
---------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS R F E C) /\ ((euclidean__defs.OS F R C E) /\ (euclidean__defs.OS R F C E))) as H122.
----------------------------------------------------------------------------------------------------------------- exact H121.
----------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__defs.OS F R C E) /\ (euclidean__defs.OS R F C E)) as H124.
------------------------------------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------------------------------------ destruct H124 as [H124 H125].
exact H122.
--------------------------------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------------------- exists F.
exists G.
split.
----------------------------------------------------------------------------------------------------- exact H95.
----------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------ exact H101.
------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------------------------------- exact H113.
Qed.
