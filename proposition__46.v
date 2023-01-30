Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__3__7a.
Require Export lemma__8__2.
Require Export lemma__9__5.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__PGflip.
Require Export lemma__PGsymmetric.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__collinearright.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equaltorightisright.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray2.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__samenotopposite.
Require Export lemma__triangletoparallelogram.
Require Export logic.
Require Export proposition__11B.
Require Export proposition__31short.
Require Export proposition__34.
Definition proposition__46 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__axioms.neq A B) -> ((euclidean__axioms.nCol A B R) -> (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point), (euclidean__defs.SQ A B X Y) /\ ((euclidean__axioms.TS Y A B R) /\ (euclidean__defs.PG A B X Y)))).
Proof.
intro A.
intro B.
intro R.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.neq B A) as H1.
- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H).
- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS B A F) /\ (euclidean__axioms.Cong A F A B)) as H2.
-- apply (@lemma__extension.lemma__extension (B) (A) (A) (B) (H1) H).
-- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS B A F) /\ (euclidean__axioms.Cong A F A B))) as H3.
--- exact H2.
--- destruct H3 as [F H3].
assert (* AndElim *) ((euclidean__axioms.BetS B A F) /\ (euclidean__axioms.Cong A F A B)) as H4.
---- exact H3.
---- destruct H4 as [H4 H5].
assert (* Cut *) (euclidean__axioms.nCol B A R) as H6.
----- assert (* Cut *) ((euclidean__axioms.nCol B A R) /\ ((euclidean__axioms.nCol B R A) /\ ((euclidean__axioms.nCol R A B) /\ ((euclidean__axioms.nCol A R B) /\ (euclidean__axioms.nCol R B A))))) as H6.
------ apply (@lemma__NCorder.lemma__NCorder (A) (B) (R) H0).
------ assert (* AndElim *) ((euclidean__axioms.nCol B A R) /\ ((euclidean__axioms.nCol B R A) /\ ((euclidean__axioms.nCol R A B) /\ ((euclidean__axioms.nCol A R B) /\ (euclidean__axioms.nCol R B A))))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.nCol B R A) /\ ((euclidean__axioms.nCol R A B) /\ ((euclidean__axioms.nCol A R B) /\ (euclidean__axioms.nCol R B A)))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.nCol R A B) /\ ((euclidean__axioms.nCol A R B) /\ (euclidean__axioms.nCol R B A))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.nCol A R B) /\ (euclidean__axioms.nCol R B A)) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
exact H7.
----- assert (* Cut *) (euclidean__axioms.Col B A F) as H7.
------ right.
right.
right.
right.
left.
exact H4.
------ assert (* Cut *) (B = B) as H8.
------- apply (@logic.eq__refl (Point) B).
------- assert (* Cut *) (euclidean__axioms.Col B A B) as H9.
-------- right.
left.
exact H8.
-------- assert (* Cut *) (euclidean__axioms.neq B F) as H10.
--------- assert (* Cut *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B F))) as H10.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (A) (F) H4).
---------- assert (* AndElim *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B F))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B F)) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
exact H14.
--------- assert (* Cut *) (euclidean__axioms.nCol B F R) as H11.
---------- apply (@euclidean__tactics.nCol__notCol (B) (F) (R)).
-----------apply (@euclidean__tactics.nCol__not__Col (B) (F) (R)).
------------apply (@lemma__NChelper.lemma__NChelper (B) (A) (R) (B) (F) (H6) (H9) (H7) H10).


---------- assert (* Cut *) (exists (C: euclidean__axioms.Point), (euclidean__defs.Per B A C) /\ (euclidean__axioms.TS C B F R)) as H12.
----------- apply (@proposition__11B.proposition__11B (B) (F) (A) (R) (H4) H11).
----------- assert (exists C: euclidean__axioms.Point, ((euclidean__defs.Per B A C) /\ (euclidean__axioms.TS C B F R))) as H13.
------------ exact H12.
------------ destruct H13 as [C H13].
assert (* AndElim *) ((euclidean__defs.Per B A C) /\ (euclidean__axioms.TS C B F R)) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* Cut *) (euclidean__axioms.nCol B F C) as H16.
-------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as H16.
--------------- exact H15.
--------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as __TmpHyp.
---------------- exact H16.
---------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C)))) as H17.
----------------- exact __TmpHyp.
----------------- destruct H17 as [x H17].
assert (* AndElim *) ((euclidean__axioms.BetS C x R) /\ ((euclidean__axioms.Col B F x) /\ (euclidean__axioms.nCol B F C))) as H18.
------------------ exact H17.
------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col B F x) /\ (euclidean__axioms.nCol B F C)) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
exact H21.
-------------- assert (* Cut *) (euclidean__axioms.Col B F A) as H17.
--------------- assert (* Cut *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))))) as H17.
---------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (F) H7).
---------------- assert (* AndElim *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B)))) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B)) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
exact H24.
--------------- assert (* Cut *) (euclidean__axioms.Col B F B) as H18.
---------------- right.
left.
exact H8.
---------------- assert (* Cut *) (euclidean__axioms.nCol B A C) as H19.
----------------- apply (@euclidean__tactics.nCol__notCol (B) (A) (C)).
------------------apply (@euclidean__tactics.nCol__not__Col (B) (A) (C)).
-------------------apply (@lemma__NChelper.lemma__NChelper (B) (F) (C) (B) (A) (H16) (H18) (H17) H1).


----------------- assert (* Cut *) (euclidean__axioms.neq A C) as H20.
------------------ assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)))))) as H20.
------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (B) (A) (C) H19).
------------------- assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)))))) as H21.
-------------------- exact H20.
-------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B))))) as H23.
--------------------- exact H22.
--------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)))) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B))) as H27.
----------------------- exact H26.
----------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
exact H23.
------------------ assert (* Cut *) (exists (D: euclidean__axioms.Point), (euclidean__defs.Out A C D) /\ (euclidean__axioms.Cong A D A B)) as H21.
------------------- apply (@lemma__layoff.lemma__layoff (A) (C) (A) (B) (H20) H).
------------------- assert (exists D: euclidean__axioms.Point, ((euclidean__defs.Out A C D) /\ (euclidean__axioms.Cong A D A B))) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [D H22].
assert (* AndElim *) ((euclidean__defs.Out A C D) /\ (euclidean__axioms.Cong A D A B)) as H23.
--------------------- exact H22.
--------------------- destruct H23 as [H23 H24].
assert (* Cut *) (euclidean__defs.Out A D C) as H25.
---------------------- apply (@lemma__ray5.lemma__ray5 (A) (C) (D) H23).
---------------------- assert (* Cut *) (A = A) as H26.
----------------------- apply (@logic.eq__refl (Point) A).
----------------------- assert (* Cut *) (euclidean__axioms.Col A B A) as H27.
------------------------ right.
left.
exact H26.
------------------------ assert (* Cut *) (exists (q: euclidean__axioms.Point), (euclidean__axioms.BetS C q R) /\ ((euclidean__axioms.Col B F q) /\ (euclidean__axioms.nCol B F C))) as H28.
------------------------- exact H15.
------------------------- assert (exists q: euclidean__axioms.Point, ((euclidean__axioms.BetS C q R) /\ ((euclidean__axioms.Col B F q) /\ (euclidean__axioms.nCol B F C)))) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [q H29].
assert (* AndElim *) ((euclidean__axioms.BetS C q R) /\ ((euclidean__axioms.Col B F q) /\ (euclidean__axioms.nCol B F C))) as H30.
--------------------------- exact H29.
--------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col B F q) /\ (euclidean__axioms.nCol B F C)) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [H32 H33].
assert (* Cut *) (euclidean__axioms.Col F B q) as H34.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col F B q) /\ ((euclidean__axioms.Col F q B) /\ ((euclidean__axioms.Col q B F) /\ ((euclidean__axioms.Col B q F) /\ (euclidean__axioms.Col q F B))))) as H34.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (q) H32).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col F B q) /\ ((euclidean__axioms.Col F q B) /\ ((euclidean__axioms.Col q B F) /\ ((euclidean__axioms.Col B q F) /\ (euclidean__axioms.Col q F B))))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col F q B) /\ ((euclidean__axioms.Col q B F) /\ ((euclidean__axioms.Col B q F) /\ (euclidean__axioms.Col q F B)))) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col q B F) /\ ((euclidean__axioms.Col B q F) /\ (euclidean__axioms.Col q F B))) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col B q F) /\ (euclidean__axioms.Col q F B)) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
exact H35.
----------------------------- assert (* Cut *) (B = B) as H35.
------------------------------ exact H8.
------------------------------ assert (* Cut *) (euclidean__axioms.nCol A B C) as H36.
------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (C)).
--------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (B) (C)).
---------------------------------apply (@lemma__NChelper.lemma__NChelper (B) (F) (C) (A) (B) (H33) (H17) (H18) H).


------------------------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H37.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col B A F) /\ (euclidean__axioms.Col A F B))))) as H37.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (A) H17).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col B A F) /\ (euclidean__axioms.Col A F B))))) as H38.
---------------------------------- exact H37.
---------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col B A F) /\ (euclidean__axioms.Col A F B)))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col B A F) /\ (euclidean__axioms.Col A F B))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ (euclidean__axioms.Col A F B)) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
exact H42.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col F B A) as H38.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H38.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (F) H37).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)))) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [H45 H46].
exact H46.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H39.
---------------------------------- assert (* Cut *) ((euclidean__axioms.neq q R) /\ ((euclidean__axioms.neq C q) /\ (euclidean__axioms.neq C R))) as H39.
----------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (q) (R) H30).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.neq q R) /\ ((euclidean__axioms.neq C q) /\ (euclidean__axioms.neq C R))) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq C q) /\ (euclidean__axioms.neq C R)) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
exact H10.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq F B) as H40.
----------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (F) H39).
----------------------------------- assert (* Cut *) (euclidean__axioms.Col B A q) as H41.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col (B) (A) (q)).
-------------------------------------intro H41.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (q) (H41)).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 (F) (B) (A) (q) (H38) (H34) H40).


------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B q) as H42.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B q) /\ ((euclidean__axioms.Col A q B) /\ ((euclidean__axioms.Col q B A) /\ ((euclidean__axioms.Col B q A) /\ (euclidean__axioms.Col q A B))))) as H42.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (q) H41).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B q) /\ ((euclidean__axioms.Col A q B) /\ ((euclidean__axioms.Col q B A) /\ ((euclidean__axioms.Col B q A) /\ (euclidean__axioms.Col q A B))))) as H43.
--------------------------------------- exact H42.
--------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col A q B) /\ ((euclidean__axioms.Col q B A) /\ ((euclidean__axioms.Col B q A) /\ (euclidean__axioms.Col q A B)))) as H45.
---------------------------------------- exact H44.
---------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col q B A) /\ ((euclidean__axioms.Col B q A) /\ (euclidean__axioms.Col q A B))) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col B q A) /\ (euclidean__axioms.Col q A B)) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49 H50].
exact H43.
------------------------------------- assert (* Cut *) (euclidean__axioms.TS C A B R) as H43.
-------------------------------------- exists q.
split.
--------------------------------------- exact H30.
--------------------------------------- split.
---------------------------------------- exact H42.
---------------------------------------- exact H36.
-------------------------------------- assert (* Cut *) (euclidean__axioms.TS D A B R) as H44.
--------------------------------------- apply (@lemma__9__5.lemma__9__5 (A) (B) (R) (C) (D) (A) (H43) (H25) H27).
--------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C A B) as H45.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H45.
----------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H36).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H48.
------------------------------------------- exact H47.
------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H50.
-------------------------------------------- exact H49.
-------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H52.
--------------------------------------------- exact H51.
--------------------------------------------- destruct H52 as [H52 H53].
exact H50.
---------------------------------------- assert (* Cut *) (A = A) as H46.
----------------------------------------- exact H26.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col C A A) as H47.
------------------------------------------ right.
right.
left.
exact H46.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A C D) as H48.
------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (A) (C) (D) H23).
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C A D) as H49.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H49.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (D) H48).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H50.
---------------------------------------------- exact H49.
---------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A)))) as H52.
----------------------------------------------- exact H51.
----------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))) as H54.
------------------------------------------------ exact H53.
------------------------------------------------ destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A)) as H56.
------------------------------------------------- exact H55.
------------------------------------------------- destruct H56 as [H56 H57].
exact H50.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H50.
--------------------------------------------- apply (@lemma__ray2.lemma__ray2 (A) (D) (C) H25).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C A B) as H51.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H51.
----------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H36).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H52.
------------------------------------------------ exact H51.
------------------------------------------------ destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H54.
------------------------------------------------- exact H53.
------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H56.
-------------------------------------------------- exact H55.
-------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H58.
--------------------------------------------------- exact H57.
--------------------------------------------------- destruct H58 as [H58 H59].
exact H45.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A D B) as H52.
----------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (D) (B)).
------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (D) (B)).
-------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (C) (A) (B) (A) (D) (H51) (H47) (H49) H50).


----------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B D) as H53.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A))))) as H53.
------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (D) (B) H52).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A))))) as H54.
-------------------------------------------------- exact H53.
-------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A)))) as H56.
--------------------------------------------------- exact H55.
--------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A))) as H58.
---------------------------------------------------- exact H57.
---------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A)) as H60.
----------------------------------------------------- exact H59.
----------------------------------------------------- destruct H60 as [H60 H61].
exact H60.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS F A B) as H54.
------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (A) (F) H4).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H55.
-------------------------------------------------- right.
right.
left.
exact H35.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F B D) as H56.
--------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (F) (B) (D)).
----------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (F) (B) (D)).
-----------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (B) (D) (F) (B) (H53) (H37) (H55) H40).


--------------------------------------------------- assert (* Cut *) (exists (G: euclidean__axioms.Point) (e: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__axioms.BetS G D e) /\ ((euclidean__defs.CongA G D A D A B) /\ ((euclidean__defs.Par G e F B) /\ ((euclidean__axioms.BetS G M B) /\ (euclidean__axioms.BetS D M A))))) as H57.
---------------------------------------------------- apply (@proposition__31short.proposition__31short (D) (F) (B) (A) (H54) H56).
---------------------------------------------------- assert (exists G: euclidean__axioms.Point, (exists (e: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__axioms.BetS G D e) /\ ((euclidean__defs.CongA G D A D A B) /\ ((euclidean__defs.Par G e F B) /\ ((euclidean__axioms.BetS G M B) /\ (euclidean__axioms.BetS D M A)))))) as H58.
----------------------------------------------------- exact H57.
----------------------------------------------------- destruct H58 as [G H58].
assert (exists e: euclidean__axioms.Point, (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS G D e) /\ ((euclidean__defs.CongA G D A D A B) /\ ((euclidean__defs.Par G e F B) /\ ((euclidean__axioms.BetS G M B) /\ (euclidean__axioms.BetS D M A)))))) as H59.
------------------------------------------------------ exact H58.
------------------------------------------------------ destruct H59 as [e H59].
assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS G D e) /\ ((euclidean__defs.CongA G D A D A B) /\ ((euclidean__defs.Par G e F B) /\ ((euclidean__axioms.BetS G M B) /\ (euclidean__axioms.BetS D M A)))))) as H60.
------------------------------------------------------- exact H59.
------------------------------------------------------- destruct H60 as [M H60].
assert (* AndElim *) ((euclidean__axioms.BetS G D e) /\ ((euclidean__defs.CongA G D A D A B) /\ ((euclidean__defs.Par G e F B) /\ ((euclidean__axioms.BetS G M B) /\ (euclidean__axioms.BetS D M A))))) as H61.
-------------------------------------------------------- exact H60.
-------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__defs.CongA G D A D A B) /\ ((euclidean__defs.Par G e F B) /\ ((euclidean__axioms.BetS G M B) /\ (euclidean__axioms.BetS D M A)))) as H63.
--------------------------------------------------------- exact H62.
--------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__defs.Par G e F B) /\ ((euclidean__axioms.BetS G M B) /\ (euclidean__axioms.BetS D M A))) as H65.
---------------------------------------------------------- exact H64.
---------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.BetS G M B) /\ (euclidean__axioms.BetS D M A)) as H67.
----------------------------------------------------------- exact H66.
----------------------------------------------------------- destruct H67 as [H67 H68].
assert (* Cut *) (euclidean__defs.Par G e A B) as H69.
------------------------------------------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel (G) (e) (A) (F) (B) (H65) (H38) H).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par A B G e) as H70.
------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (G) (e) (A) (B) H69).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G D e) as H71.
-------------------------------------------------------------- right.
right.
right.
right.
left.
exact H61.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G e D) as H72.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D G e) /\ ((euclidean__axioms.Col D e G) /\ ((euclidean__axioms.Col e G D) /\ ((euclidean__axioms.Col G e D) /\ (euclidean__axioms.Col e D G))))) as H72.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (D) (e) H71).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D G e) /\ ((euclidean__axioms.Col D e G) /\ ((euclidean__axioms.Col e G D) /\ ((euclidean__axioms.Col G e D) /\ (euclidean__axioms.Col e D G))))) as H73.
----------------------------------------------------------------- exact H72.
----------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col D e G) /\ ((euclidean__axioms.Col e G D) /\ ((euclidean__axioms.Col G e D) /\ (euclidean__axioms.Col e D G)))) as H75.
------------------------------------------------------------------ exact H74.
------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col e G D) /\ ((euclidean__axioms.Col G e D) /\ (euclidean__axioms.Col e D G))) as H77.
------------------------------------------------------------------- exact H76.
------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col G e D) /\ (euclidean__axioms.Col e D G)) as H79.
-------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------- destruct H79 as [H79 H80].
exact H79.
--------------------------------------------------------------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__defs.PG D E B A) /\ (euclidean__axioms.Col G e E)) as H73.
---------------------------------------------------------------- apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram (D) (B) (A) (G) (e) (H70) H72).
---------------------------------------------------------------- assert (exists E: euclidean__axioms.Point, ((euclidean__defs.PG D E B A) /\ (euclidean__axioms.Col G e E))) as H74.
----------------------------------------------------------------- exact H73.
----------------------------------------------------------------- destruct H74 as [E H74].
assert (* AndElim *) ((euclidean__defs.PG D E B A) /\ (euclidean__axioms.Col G e E)) as H75.
------------------------------------------------------------------ exact H74.
------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* Cut *) (euclidean__defs.Per C A B) as H77.
------------------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (B) (A) (C) H14).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D A) as H78.
-------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (D) H50).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per D A B) as H79.
--------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (C) (A) (D) (B) (H77) (H49) H78).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B A D) as H80.
---------------------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (D) (A) (B) H79).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per G D A) as H81.
----------------------------------------------------------------------- apply (@lemma__equaltorightisright.lemma__equaltorightisright (D) (A) (B) (G) (D) (A) (H79) H63).
----------------------------------------------------------------------- assert (* Cut *) (exists (p: euclidean__axioms.Point), (euclidean__axioms.BetS G D p) /\ ((euclidean__axioms.Cong G D p D) /\ ((euclidean__axioms.Cong G A p A) /\ (euclidean__axioms.neq D A)))) as H82.
------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------ assert (exists p: euclidean__axioms.Point, ((euclidean__axioms.BetS G D p) /\ ((euclidean__axioms.Cong G D p D) /\ ((euclidean__axioms.Cong G A p A) /\ (euclidean__axioms.neq D A))))) as H83.
------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------- destruct H83 as [p H83].
assert (* AndElim *) ((euclidean__axioms.BetS G D p) /\ ((euclidean__axioms.Cong G D p D) /\ ((euclidean__axioms.Cong G A p A) /\ (euclidean__axioms.neq D A)))) as H84.
-------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Cong G D p D) /\ ((euclidean__axioms.Cong G A p A) /\ (euclidean__axioms.neq D A))) as H86.
--------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Cong G A p A) /\ (euclidean__axioms.neq D A)) as H88.
---------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* Cut *) (euclidean__axioms.BetS p D G) as H90.
----------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (D) (p) H84).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong p D G D) as H91.
------------------------------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (p) (G) (D) (D) H86).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong p A G A) as H92.
------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (p) (G) (A) (A) H88).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per p D A) as H93.
-------------------------------------------------------------------------------- exists G.
split.
--------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------------- exact H89.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par D A E B) as H94.
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par D E B A) /\ (euclidean__defs.Par D A E B)) as H94.
---------------------------------------------------------------------------------- exact H75.
---------------------------------------------------------------------------------- destruct H94 as [H94 H95].
exact H95.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP D A E B) as H95.
---------------------------------------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B (D) (A) (E) (B) H94).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS E B D A) as H96.
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq E B) /\ ((~(euclidean__defs.Meet D A E B)) /\ (euclidean__defs.OS E B D A)))) as H96.
------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------ destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((~(euclidean__defs.Meet D A E B)) /\ (euclidean__defs.OS E B D A))) as H98.
------------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((~(euclidean__defs.Meet D A E B)) /\ (euclidean__defs.OS E B D A)) as H100.
-------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
exact H101.
----------------------------------------------------------------------------------- assert (* Cut *) (D = D) as H97.
------------------------------------------------------------------------------------ apply (@logic.eq__refl (Point) D).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D A D) as H98.
------------------------------------------------------------------------------------- right.
left.
exact H97.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D A B) as H99.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H99.
--------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (D) H53).
--------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H100.
---------------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A)))) as H102.
----------------------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))) as H104.
------------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------------ destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A)) as H106.
------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
exact H104.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B M G) as H100.
--------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (M) (B) H67).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D M A) as H101.
---------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H68.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D A M) as H102.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M D A) /\ ((euclidean__axioms.Col M A D) /\ ((euclidean__axioms.Col A D M) /\ ((euclidean__axioms.Col D A M) /\ (euclidean__axioms.Col A M D))))) as H102.
------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (D) (M) (A) H101).
------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col M D A) /\ ((euclidean__axioms.Col M A D) /\ ((euclidean__axioms.Col A D M) /\ ((euclidean__axioms.Col D A M) /\ (euclidean__axioms.Col A M D))))) as H103.
------------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.Col M A D) /\ ((euclidean__axioms.Col A D M) /\ ((euclidean__axioms.Col D A M) /\ (euclidean__axioms.Col A M D)))) as H105.
-------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col A D M) /\ ((euclidean__axioms.Col D A M) /\ (euclidean__axioms.Col A M D))) as H107.
--------------------------------------------------------------------------------------------- exact H106.
--------------------------------------------------------------------------------------------- destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col D A M) /\ (euclidean__axioms.Col A M D)) as H109.
---------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
exact H109.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS B D A G) as H103.
------------------------------------------------------------------------------------------ exists M.
split.
------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------- exact H102.
-------------------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS E D A G) as H104.
------------------------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation (D) (A) (E) (B) (G) (H96) H103).
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D A E) as H105.
-------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS E X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A E))) as H105.
--------------------------------------------------------------------------------------------- exact H104.
--------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS E X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A E))) as __TmpHyp.
---------------------------------------------------------------------------------------------- exact H105.
---------------------------------------------------------------------------------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS E X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A E)))) as H106.
----------------------------------------------------------------------------------------------- exact __TmpHyp.
----------------------------------------------------------------------------------------------- destruct H106 as [x H106].
assert (* AndElim *) ((euclidean__axioms.BetS E x G) /\ ((euclidean__axioms.Col D A x) /\ (euclidean__axioms.nCol D A E))) as H107.
------------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------------ destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col D A x) /\ (euclidean__axioms.nCol D A E)) as H109.
------------------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A B))) as H111.
-------------------------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A B))) as __TmpHyp0.
--------------------------------------------------------------------------------------------------- exact H111.
--------------------------------------------------------------------------------------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS B X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A B)))) as H112.
---------------------------------------------------------------------------------------------------- exact __TmpHyp0.
---------------------------------------------------------------------------------------------------- destruct H112 as [x0 H112].
assert (* AndElim *) ((euclidean__axioms.BetS B x0 G) /\ ((euclidean__axioms.Col D A x0) /\ (euclidean__axioms.nCol D A B))) as H113.
----------------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Col D A x0) /\ (euclidean__axioms.nCol D A B)) as H115.
------------------------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------------------------ destruct H115 as [H115 H116].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS D X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B D))) as H117.
------------------------------------------------------------------------------------------------------- exact H44.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS D X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B D))) as __TmpHyp1.
-------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS D X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B D)))) as H118.
--------------------------------------------------------------------------------------------------------- exact __TmpHyp1.
--------------------------------------------------------------------------------------------------------- destruct H118 as [x1 H118].
assert (* AndElim *) ((euclidean__axioms.BetS D x1 R) /\ ((euclidean__axioms.Col A B x1) /\ (euclidean__axioms.nCol A B D))) as H119.
---------------------------------------------------------------------------------------------------------- exact H118.
---------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.Col A B x1) /\ (euclidean__axioms.nCol A B D)) as H121.
----------------------------------------------------------------------------------------------------------- exact H120.
----------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B C))) as H123.
------------------------------------------------------------------------------------------------------------ exact H43.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B C))) as __TmpHyp2.
------------------------------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------------------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B C)))) as H124.
-------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
-------------------------------------------------------------------------------------------------------------- destruct H124 as [x2 H124].
assert (* AndElim *) ((euclidean__axioms.BetS C x2 R) /\ ((euclidean__axioms.Col A B x2) /\ (euclidean__axioms.nCol A B C))) as H125.
--------------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col A B x2) /\ (euclidean__axioms.nCol A B C)) as H127.
---------------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as H129.
----------------------------------------------------------------------------------------------------------------- exact H15.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as __TmpHyp3.
------------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------------ assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C)))) as H130.
------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
------------------------------------------------------------------------------------------------------------------- destruct H130 as [x3 H130].
assert (* AndElim *) ((euclidean__axioms.BetS C x3 R) /\ ((euclidean__axioms.Col B F x3) /\ (euclidean__axioms.nCol B F C))) as H131.
-------------------------------------------------------------------------------------------------------------------- exact H130.
-------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col B F x3) /\ (euclidean__axioms.nCol B F C)) as H133.
--------------------------------------------------------------------------------------------------------------------- exact H132.
--------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
exact H110.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS G D A E) as H106.
--------------------------------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (D) (A) (E) (G) H104).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D A G) as H107.
---------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G X E) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A G))) as H107.
----------------------------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G X E) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A G))) as __TmpHyp.
------------------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------------------ assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS G X E) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A G)))) as H108.
------------------------------------------------------------------------------------------------- exact __TmpHyp.
------------------------------------------------------------------------------------------------- destruct H108 as [x H108].
assert (* AndElim *) ((euclidean__axioms.BetS G x E) /\ ((euclidean__axioms.Col D A x) /\ (euclidean__axioms.nCol D A G))) as H109.
-------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col D A x) /\ (euclidean__axioms.nCol D A G)) as H111.
--------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS E X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A E))) as H113.
---------------------------------------------------------------------------------------------------- exact H104.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS E X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A E))) as __TmpHyp0.
----------------------------------------------------------------------------------------------------- exact H113.
----------------------------------------------------------------------------------------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS E X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A E)))) as H114.
------------------------------------------------------------------------------------------------------ exact __TmpHyp0.
------------------------------------------------------------------------------------------------------ destruct H114 as [x0 H114].
assert (* AndElim *) ((euclidean__axioms.BetS E x0 G) /\ ((euclidean__axioms.Col D A x0) /\ (euclidean__axioms.nCol D A E))) as H115.
------------------------------------------------------------------------------------------------------- exact H114.
------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col D A x0) /\ (euclidean__axioms.nCol D A E)) as H117.
-------------------------------------------------------------------------------------------------------- exact H116.
-------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A B))) as H119.
--------------------------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A B))) as __TmpHyp1.
---------------------------------------------------------------------------------------------------------- exact H119.
---------------------------------------------------------------------------------------------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS B X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A B)))) as H120.
----------------------------------------------------------------------------------------------------------- exact __TmpHyp1.
----------------------------------------------------------------------------------------------------------- destruct H120 as [x1 H120].
assert (* AndElim *) ((euclidean__axioms.BetS B x1 G) /\ ((euclidean__axioms.Col D A x1) /\ (euclidean__axioms.nCol D A B))) as H121.
------------------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------------------ destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col D A x1) /\ (euclidean__axioms.nCol D A B)) as H123.
------------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS D X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B D))) as H125.
-------------------------------------------------------------------------------------------------------------- exact H44.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS D X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B D))) as __TmpHyp2.
--------------------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS D X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B D)))) as H126.
---------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
---------------------------------------------------------------------------------------------------------------- destruct H126 as [x2 H126].
assert (* AndElim *) ((euclidean__axioms.BetS D x2 R) /\ ((euclidean__axioms.Col A B x2) /\ (euclidean__axioms.nCol A B D))) as H127.
----------------------------------------------------------------------------------------------------------------- exact H126.
----------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col A B x2) /\ (euclidean__axioms.nCol A B D)) as H129.
------------------------------------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------------------------------------ destruct H129 as [H129 H130].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B C))) as H131.
------------------------------------------------------------------------------------------------------------------- exact H43.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B C))) as __TmpHyp3.
-------------------------------------------------------------------------------------------------------------------- exact H131.
-------------------------------------------------------------------------------------------------------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B C)))) as H132.
--------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
--------------------------------------------------------------------------------------------------------------------- destruct H132 as [x3 H132].
assert (* AndElim *) ((euclidean__axioms.BetS C x3 R) /\ ((euclidean__axioms.Col A B x3) /\ (euclidean__axioms.nCol A B C))) as H133.
---------------------------------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col A B x3) /\ (euclidean__axioms.nCol A B C)) as H135.
----------------------------------------------------------------------------------------------------------------------- exact H134.
----------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as H137.
------------------------------------------------------------------------------------------------------------------------ exact H15.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as __TmpHyp4.
------------------------------------------------------------------------------------------------------------------------- exact H137.
------------------------------------------------------------------------------------------------------------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C)))) as H138.
-------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
-------------------------------------------------------------------------------------------------------------------------- destruct H138 as [x4 H138].
assert (* AndElim *) ((euclidean__axioms.BetS C x4 R) /\ ((euclidean__axioms.Col B F x4) /\ (euclidean__axioms.nCol B F C))) as H139.
--------------------------------------------------------------------------------------------------------------------------- exact H138.
--------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.Col B F x4) /\ (euclidean__axioms.nCol B F C)) as H141.
---------------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
exact H112.
---------------------------------------------------------------------------------------------- assert (* Cut *) (exists (d: euclidean__axioms.Point), (euclidean__axioms.BetS E d G) /\ ((euclidean__axioms.Col D A d) /\ (euclidean__axioms.nCol D A E))) as H108.
----------------------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------------------- assert (exists d: euclidean__axioms.Point, ((euclidean__axioms.BetS E d G) /\ ((euclidean__axioms.Col D A d) /\ (euclidean__axioms.nCol D A E)))) as H109.
------------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------------ destruct H109 as [d H109].
assert (* AndElim *) ((euclidean__axioms.BetS E d G) /\ ((euclidean__axioms.Col D A d) /\ (euclidean__axioms.nCol D A E))) as H110.
------------------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.Col D A d) /\ (euclidean__axioms.nCol D A E)) as H112.
-------------------------------------------------------------------------------------------------- exact H111.
-------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* Cut *) (euclidean__axioms.neq E G) as H114.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq d G) /\ ((euclidean__axioms.neq E d) /\ (euclidean__axioms.neq E G))) as H114.
---------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (d) (G) H110).
---------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq d G) /\ ((euclidean__axioms.neq E d) /\ (euclidean__axioms.neq E G))) as H115.
----------------------------------------------------------------------------------------------------- exact H114.
----------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.neq E d) /\ (euclidean__axioms.neq E G)) as H117.
------------------------------------------------------------------------------------------------------ exact H116.
------------------------------------------------------------------------------------------------------ destruct H117 as [H117 H118].
exact H118.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G E) as H115.
---------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (G) H114).
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G D) as H116.
----------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G D)))))) as H116.
------------------------------------------------------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct (D) (A) (G) H107).
------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G D)))))) as H117.
------------------------------------------------------------------------------------------------------- exact H116.
------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G D))))) as H119.
-------------------------------------------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G D)))) as H121.
--------------------------------------------------------------------------------------------------------- exact H120.
--------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G D))) as H123.
---------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G D)) as H125.
----------------------------------------------------------------------------------------------------------- exact H124.
----------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
exact H126.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D E) as H117.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E D)))))) as H117.
------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (D) (A) (E) H113).
------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E D)))))) as H118.
-------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E D))))) as H120.
--------------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E D)))) as H122.
---------------------------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E D))) as H124.
----------------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E D)) as H126.
------------------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------------------ destruct H126 as [H126 H127].
exact H122.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__defs.OS E G D A)) as H118.
------------------------------------------------------------------------------------------------------- intro H118.
assert (* Cut *) (~(euclidean__axioms.TS E D A G)) as H119.
-------------------------------------------------------------------------------------------------------- apply (@lemma__samenotopposite.lemma__samenotopposite (E) (G) (D) (A) H118).
-------------------------------------------------------------------------------------------------------- apply (@H119 H104).
------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS D G E)) as H119.
-------------------------------------------------------------------------------------------------------- intro H119.
assert (* Cut *) (euclidean__axioms.BetS E G D) as H120.
--------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (G) (E) H119).
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E D e) as H121.
---------------------------------------------------------------------------------------------------------- apply (@lemma__3__7a.lemma__3__7a (E) (G) (D) (e) (H120) H61).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS E G D A) as H122.
----------------------------------------------------------------------------------------------------------- exists e.
exists D.
exists D.
split.
------------------------------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------- exact H61.
--------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------- exact H113.
---------------------------------------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------------------------------------- apply (@H118 H122).
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS G E D)) as H120.
--------------------------------------------------------------------------------------------------------- intro H120.
assert (* Cut *) (euclidean__axioms.BetS E D e) as H121.
---------------------------------------------------------------------------------------------------------- apply (@lemma__3__6a.lemma__3__6a (G) (E) (D) (e) (H120) H61).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS E G D A) as H122.
----------------------------------------------------------------------------------------------------------- exists e.
exists D.
exists D.
split.
------------------------------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------- exact H61.
--------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------- exact H113.
---------------------------------------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------------------------------------- apply (@H118 H122).
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e G D) as H121.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col e G D) /\ ((euclidean__axioms.Col e D G) /\ ((euclidean__axioms.Col D G e) /\ ((euclidean__axioms.Col G D e) /\ (euclidean__axioms.Col D e G))))) as H121.
----------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (e) (D) H72).
----------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col e G D) /\ ((euclidean__axioms.Col e D G) /\ ((euclidean__axioms.Col D G e) /\ ((euclidean__axioms.Col G D e) /\ (euclidean__axioms.Col D e G))))) as H122.
------------------------------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------------------------------ destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col e D G) /\ ((euclidean__axioms.Col D G e) /\ ((euclidean__axioms.Col G D e) /\ (euclidean__axioms.Col D e G)))) as H124.
------------------------------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.Col D G e) /\ ((euclidean__axioms.Col G D e) /\ (euclidean__axioms.Col D e G))) as H126.
-------------------------------------------------------------------------------------------------------------- exact H125.
-------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col G D e) /\ (euclidean__axioms.Col D e G)) as H128.
--------------------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
exact H122.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e G E) as H122.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col e G E) /\ ((euclidean__axioms.Col e E G) /\ ((euclidean__axioms.Col E G e) /\ ((euclidean__axioms.Col G E e) /\ (euclidean__axioms.Col E e G))))) as H122.
------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (G) (e) (E) H76).
------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col e G E) /\ ((euclidean__axioms.Col e E G) /\ ((euclidean__axioms.Col E G e) /\ ((euclidean__axioms.Col G E e) /\ (euclidean__axioms.Col E e G))))) as H123.
------------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col e E G) /\ ((euclidean__axioms.Col E G e) /\ ((euclidean__axioms.Col G E e) /\ (euclidean__axioms.Col E e G)))) as H125.
-------------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col E G e) /\ ((euclidean__axioms.Col G E e) /\ (euclidean__axioms.Col E e G))) as H127.
--------------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col G E e) /\ (euclidean__axioms.Col E e G)) as H129.
---------------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
exact H123.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G e F) as H123.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol G e F) /\ ((euclidean__axioms.nCol G F B) /\ ((euclidean__axioms.nCol e F B) /\ (euclidean__axioms.nCol G e B)))) as H123.
------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (G) (e) (F) (B) H65).
------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol G e F) /\ ((euclidean__axioms.nCol G F B) /\ ((euclidean__axioms.nCol e F B) /\ (euclidean__axioms.nCol G e B)))) as H124.
-------------------------------------------------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.nCol G F B) /\ ((euclidean__axioms.nCol e F B) /\ (euclidean__axioms.nCol G e B))) as H126.
--------------------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.nCol e F B) /\ (euclidean__axioms.nCol G e B)) as H128.
---------------------------------------------------------------------------------------------------------------- exact H127.
---------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
exact H124.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq G e) as H124.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G e) /\ ((euclidean__axioms.neq e F) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e G) /\ ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F G)))))) as H124.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (G) (e) (F) H123).
-------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G e) /\ ((euclidean__axioms.neq e F) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e G) /\ ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F G)))))) as H125.
--------------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.neq e F) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e G) /\ ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F G))))) as H127.
---------------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e G) /\ ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F G)))) as H129.
----------------------------------------------------------------------------------------------------------------- exact H128.
----------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.neq e G) /\ ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F G))) as H131.
------------------------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------------------------ destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F G)) as H133.
------------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
exact H125.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq e G) as H125.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (e) H124).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G D E) as H126.
--------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (G) (D) (E)).
----------------------------------------------------------------------------------------------------------------intro H126.
apply (@euclidean__tactics.Col__nCol__False (G) (D) (E) (H126)).
-----------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (e) (G) (D) (E) (H121) (H122) H125).


--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((G = D) \/ ((G = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D G E) \/ ((euclidean__axioms.BetS G D E) \/ (euclidean__axioms.BetS G E D)))))) as H127.
---------------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G D E) as H128.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((G = D) \/ ((G = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D G E) \/ ((euclidean__axioms.BetS G D E) \/ (euclidean__axioms.BetS G E D)))))) as H128.
------------------------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((G = D) \/ ((G = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D G E) \/ ((euclidean__axioms.BetS G D E) \/ (euclidean__axioms.BetS G E D)))))) as __TmpHyp.
------------------------------------------------------------------------------------------------------------------- exact H128.
------------------------------------------------------------------------------------------------------------------- assert (G = D \/ (G = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D G E) \/ ((euclidean__axioms.BetS G D E) \/ (euclidean__axioms.BetS G E D))))) as H129.
-------------------------------------------------------------------------------------------------------------------- exact __TmpHyp.
-------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129|H129].
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS G D E))) as H130.
---------------------------------------------------------------------------------------------------------------------- intro H130.
apply (@H116 H129).
---------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS G D E)).
-----------------------------------------------------------------------------------------------------------------------intro H131.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))))))) as H132.
------------------------------------------------------------------------------------------------------------------------ exact H0.
------------------------------------------------------------------------------------------------------------------------ destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))))))) as H134.
------------------------------------------------------------------------------------------------------------------------- exact H6.
------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))))))) as H136.
-------------------------------------------------------------------------------------------------------------------------- exact H11.
-------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))))) as H138.
--------------------------------------------------------------------------------------------------------------------------- exact H16.
--------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H140.
---------------------------------------------------------------------------------------------------------------------------- exact H19.
---------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))))) as H142.
----------------------------------------------------------------------------------------------------------------------------- exact H33.
----------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H144.
------------------------------------------------------------------------------------------------------------------------------ exact H36.
------------------------------------------------------------------------------------------------------------------------------ destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))))) as H146.
------------------------------------------------------------------------------------------------------------------------------- exact H45.
------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))))) as H148.
-------------------------------------------------------------------------------------------------------------------------------- exact H51.
-------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))))) as H150.
--------------------------------------------------------------------------------------------------------------------------------- exact H52.
--------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H152.
---------------------------------------------------------------------------------------------------------------------------------- exact H53.
---------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))))))) as H154.
----------------------------------------------------------------------------------------------------------------------------------- exact H56.
----------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))))))) as H156.
------------------------------------------------------------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------------------------------------------------------------ destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))))) as H158.
------------------------------------------------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))))))) as H160.
-------------------------------------------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))))) as H162.
--------------------------------------------------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.neq G e) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))))))) as H164.
---------------------------------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R)))))) as H166.
----------------------------------------------------------------------------------------------------------------------------------------- exact H133.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R)))))) as H168.
------------------------------------------------------------------------------------------------------------------------------------------ exact H135.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R)))))) as H170.
------------------------------------------------------------------------------------------------------------------------------------------- exact H137.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))))) as H172.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H139.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H174.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H141.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))))) as H176.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H143.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H178.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H145.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))))) as H180.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H147.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H180 as [H180 H181].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))))) as H182.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H149.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H182 H183].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))))) as H184.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H151.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H184 H185].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H186.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H153.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H186 H187].
assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D)))))) as H188.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H155.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B)))))) as H190.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H157.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H190 H191].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))))) as H192.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H192 as [H192 H193].
assert (* AndElim *) ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G)))))) as H194.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H161.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))))) as H196.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F)))))) as H198.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H165.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [H198 H199].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))))) as H200.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H200 H201].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))))) as H202.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H169.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))))) as H204.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H171.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H204 as [H204 H205].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))) as H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H173.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H206 H207].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H208.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [H208 H209].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))) as H210.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [H210 H211].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H212.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H179.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))) as H214.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))) as H216.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H183.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H216 as [H216 H217].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))) as H218.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H185.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H218 as [H218 H219].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H220.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [H220 H221].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))))) as H222.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H222 as [H222 H223].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))))) as H224.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H224 as [H224 H225].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))) as H226.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H193.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H226 as [H226 H227].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))))) as H228.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H195.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H228 as [H228 H229].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))) as H230.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H197.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H230 as [H230 H231].
assert (* AndElim *) ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))))) as H232.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H232 as [H232 H233].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R)))) as H234.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H234 as [H234 H235].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R)))) as H236.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H236 as [H236 H237].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R)))) as H238.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H238 as [H238 H239].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))) as H240.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H207.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H240 as [H240 H241].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H242.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H242 as [H242 H243].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))) as H244.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H244 as [H244 H245].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H246.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H246 as [H246 H247].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))) as H248.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H248 as [H248 H249].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))) as H250.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H217.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H250 as [H250 H251].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))) as H252.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H219.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H252 as [H252 H253].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H254.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H254 as [H254 H255].
assert (* AndElim *) ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D)))) as H256.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H223.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H256 as [H256 H257].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B)))) as H258.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H225.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H258 as [H258 H259].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))) as H260.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H260 as [H260 H261].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G)))) as H262.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H229.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H262 as [H262 H263].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))) as H264.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H231.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H264 as [H264 H265].
assert (* AndElim *) ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F)))) as H266.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H233.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H266 as [H266 H267].
assert (* AndElim *) ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))) as H268.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H235.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H268 as [H268 H269].
assert (* AndElim *) ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))) as H270.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H237.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H270 as [H270 H271].
assert (* AndElim *) ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))) as H272.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H239.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H272 as [H272 H273].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))) as H274.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H241.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H274 as [H274 H275].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H276.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H243.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H276 as [H276 H277].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))) as H278.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H245.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H278 as [H278 H279].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H280.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H247.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H280 as [H280 H281].
assert (* AndElim *) ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))) as H282.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H249.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H282 as [H282 H283].
assert (* AndElim *) ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))) as H284.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H251.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H284 as [H284 H285].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))) as H286.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H253.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H286 as [H286 H287].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H288.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H255.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H288 as [H288 H289].
assert (* AndElim *) ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))) as H290.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H257.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H290 as [H290 H291].
assert (* AndElim *) ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))) as H292.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H259.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H292 as [H292 H293].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))) as H294.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H261.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H294 as [H294 H295].
assert (* AndElim *) ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))) as H296.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H263.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H296 as [H296 H297].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))) as H298.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H265.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H298 as [H298 H299].
assert (* AndElim *) ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))) as H300.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H267.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H300 as [H300 H301].
assert (* Cut *) (False) as H302.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H116 H129).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H303.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H130 H131).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert False.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------exact H303.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- contradiction.

--------------------------------------------------------------------------------------------------------------------- assert (G = E \/ (D = E) \/ ((euclidean__axioms.BetS D G E) \/ ((euclidean__axioms.BetS G D E) \/ (euclidean__axioms.BetS G E D)))) as H130.
---------------------------------------------------------------------------------------------------------------------- exact H129.
---------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130|H130].
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS G D E))) as H131.
------------------------------------------------------------------------------------------------------------------------ intro H131.
apply (@H115 H130).
------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS G D E)).
-------------------------------------------------------------------------------------------------------------------------intro H132.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))))))) as H133.
-------------------------------------------------------------------------------------------------------------------------- exact H0.
-------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))))))) as H135.
--------------------------------------------------------------------------------------------------------------------------- exact H6.
--------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))))))) as H137.
---------------------------------------------------------------------------------------------------------------------------- exact H11.
---------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))))) as H139.
----------------------------------------------------------------------------------------------------------------------------- exact H16.
----------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H141.
------------------------------------------------------------------------------------------------------------------------------ exact H19.
------------------------------------------------------------------------------------------------------------------------------ destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))))) as H143.
------------------------------------------------------------------------------------------------------------------------------- exact H33.
------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H145.
-------------------------------------------------------------------------------------------------------------------------------- exact H36.
-------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))))) as H147.
--------------------------------------------------------------------------------------------------------------------------------- exact H45.
--------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))))) as H149.
---------------------------------------------------------------------------------------------------------------------------------- exact H51.
---------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))))) as H151.
----------------------------------------------------------------------------------------------------------------------------------- exact H52.
----------------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H153.
------------------------------------------------------------------------------------------------------------------------------------ exact H53.
------------------------------------------------------------------------------------------------------------------------------------ destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))))))) as H155.
------------------------------------------------------------------------------------------------------------------------------------- exact H56.
------------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))))))) as H157.
-------------------------------------------------------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))))) as H159.
--------------------------------------------------------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))))))) as H161.
---------------------------------------------------------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))))) as H163.
----------------------------------------------------------------------------------------------------------------------------------------- exact H113.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
assert (* AndElim *) ((euclidean__axioms.neq G e) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))))))) as H165.
------------------------------------------------------------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R)))))) as H167.
------------------------------------------------------------------------------------------------------------------------------------------- exact H134.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R)))))) as H169.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H136.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R)))))) as H171.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H138.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))))) as H173.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H175.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H142.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))))) as H177.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H179.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H146.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))))) as H181.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H148.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))))) as H183.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H150.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))))) as H185.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H152.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H187.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H154.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D)))))) as H189.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H156.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B)))))) as H191.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H158.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))))) as H193.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H160.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G)))))) as H195.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H162.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))))) as H197.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H164.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
assert (* AndElim *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F)))))) as H199.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H166.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [H199 H200].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))))) as H201.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H168.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H201 as [H201 H202].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))))) as H203.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H170.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [H203 H204].
assert (* AndElim *) ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))))) as H205.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [H205 H206].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))) as H207.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H207 as [H207 H208].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H209.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [H209 H210].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))) as H211.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [H211 H212].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H180.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H213 as [H213 H214].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))) as H215.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [H215 H216].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))) as H217.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [H217 H218].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))) as H219.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H219 as [H219 H220].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H221.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))))) as H223.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H223 as [H223 H224].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))))) as H225.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H192.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H225 as [H225 H226].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))) as H227.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H227 as [H227 H228].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))))) as H229.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [H229 H230].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))) as H231.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [H231 H232].
assert (* AndElim *) ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))))) as H233.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H233 as [H233 H234].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R)))) as H235.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H202.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H235 as [H235 H236].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R)))) as H237.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H204.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H237 as [H237 H238].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R)))) as H239.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H239 as [H239 H240].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))) as H241.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H241 as [H241 H242].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H243.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H210.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H243 as [H243 H244].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))) as H245.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H212.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H245 as [H245 H246].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H247.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H247 as [H247 H248].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))) as H249.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H216.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H249 as [H249 H250].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))) as H251.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H218.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H251 as [H251 H252].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))) as H253.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H220.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H253 as [H253 H254].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H255.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H222.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H255 as [H255 H256].
assert (* AndElim *) ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D)))) as H257.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H224.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H257 as [H257 H258].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B)))) as H259.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H226.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H259 as [H259 H260].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))) as H261.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H228.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H261 as [H261 H262].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G)))) as H263.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H263 as [H263 H264].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))) as H265.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H232.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H265 as [H265 H266].
assert (* AndElim *) ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F)))) as H267.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H234.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H267 as [H267 H268].
assert (* AndElim *) ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))) as H269.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H236.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H269 as [H269 H270].
assert (* AndElim *) ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))) as H271.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H238.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H271 as [H271 H272].
assert (* AndElim *) ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))) as H273.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H240.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H273 as [H273 H274].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))) as H275.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H242.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H275 as [H275 H276].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H277.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H244.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H277 as [H277 H278].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))) as H279.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H246.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H279 as [H279 H280].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H281.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H248.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H281 as [H281 H282].
assert (* AndElim *) ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))) as H283.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H250.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H283 as [H283 H284].
assert (* AndElim *) ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))) as H285.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H252.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H285 as [H285 H286].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))) as H287.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H254.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H287 as [H287 H288].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H289.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H256.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H289 as [H289 H290].
assert (* AndElim *) ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))) as H291.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H258.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H291 as [H291 H292].
assert (* AndElim *) ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))) as H293.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H260.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H293 as [H293 H294].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))) as H295.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H262.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H295 as [H295 H296].
assert (* AndElim *) ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))) as H297.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H264.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H297 as [H297 H298].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))) as H299.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H266.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H299 as [H299 H300].
assert (* AndElim *) ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))) as H301.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H268.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H301 as [H301 H302].
assert (* Cut *) (False) as H303.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H115 H130).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H304.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H131 H132).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert False.
-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------exact H304.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- contradiction.

----------------------------------------------------------------------------------------------------------------------- assert (D = E \/ (euclidean__axioms.BetS D G E) \/ ((euclidean__axioms.BetS G D E) \/ (euclidean__axioms.BetS G E D))) as H131.
------------------------------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------------------------------ destruct H131 as [H131|H131].
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS G D E))) as H132.
-------------------------------------------------------------------------------------------------------------------------- intro H132.
apply (@H117 H131).
-------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS G D E)).
---------------------------------------------------------------------------------------------------------------------------intro H133.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))))))) as H134.
---------------------------------------------------------------------------------------------------------------------------- exact H0.
---------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))))))) as H136.
----------------------------------------------------------------------------------------------------------------------------- exact H6.
----------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))))))) as H138.
------------------------------------------------------------------------------------------------------------------------------ exact H11.
------------------------------------------------------------------------------------------------------------------------------ destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))))) as H140.
------------------------------------------------------------------------------------------------------------------------------- exact H16.
------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H142.
-------------------------------------------------------------------------------------------------------------------------------- exact H19.
-------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))))) as H144.
--------------------------------------------------------------------------------------------------------------------------------- exact H33.
--------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H146.
---------------------------------------------------------------------------------------------------------------------------------- exact H36.
---------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))))) as H148.
----------------------------------------------------------------------------------------------------------------------------------- exact H45.
----------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))))) as H150.
------------------------------------------------------------------------------------------------------------------------------------ exact H51.
------------------------------------------------------------------------------------------------------------------------------------ destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))))) as H152.
------------------------------------------------------------------------------------------------------------------------------------- exact H52.
------------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H154.
-------------------------------------------------------------------------------------------------------------------------------------- exact H53.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))))))) as H156.
--------------------------------------------------------------------------------------------------------------------------------------- exact H56.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))))))) as H158.
---------------------------------------------------------------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))))) as H160.
----------------------------------------------------------------------------------------------------------------------------------------- exact H105.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))))))) as H162.
------------------------------------------------------------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))))) as H164.
------------------------------------------------------------------------------------------------------------------------------------------- exact H113.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.neq G e) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))))))) as H166.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R)))))) as H168.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H135.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R)))))) as H170.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R)))))) as H172.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))))) as H174.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H174 as [H174 H175].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H176.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H143.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))))) as H178.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H145.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H180.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H147.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H180 H181].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))))) as H182.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H149.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H182 H183].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))))) as H184.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H151.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H184 H185].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))))) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H153.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H186 as [H186 H187].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H188.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H155.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D)))))) as H190.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H157.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H190 H191].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B)))))) as H192.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H159.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H192 H193].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))))) as H194.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H161.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G)))))) as H196.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))))) as H198.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H165.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H198 as [H198 H199].
assert (* AndElim *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F)))))) as H200.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H200 H201].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))))) as H202.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H169.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))))) as H204.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H171.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [H204 H205].
assert (* AndElim *) ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))))) as H206.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H173.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H206 H207].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))) as H208.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [H208 H209].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H210.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H177.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H210 as [H210 H211].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))) as H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H179.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H214.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))) as H216.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H183.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H216 as [H216 H217].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))) as H218.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H185.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H218 as [H218 H219].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))) as H220.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [H220 H221].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H222.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H189.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H222 as [H222 H223].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))))) as H224.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H224 as [H224 H225].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))))) as H226.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H193.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H226 as [H226 H227].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))) as H228.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H195.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H228 as [H228 H229].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))))) as H230.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H197.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H230 as [H230 H231].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))) as H232.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H232 as [H232 H233].
assert (* AndElim *) ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))))) as H234.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H201.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H234 as [H234 H235].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R)))) as H236.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H236 as [H236 H237].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R)))) as H238.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H238 as [H238 H239].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R)))) as H240.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H207.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H240 as [H240 H241].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))) as H242.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H242 as [H242 H243].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H244.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H244 as [H244 H245].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))) as H246.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H246 as [H246 H247].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H248.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H248 as [H248 H249].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))) as H250.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H217.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H250 as [H250 H251].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))) as H252.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H219.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H252 as [H252 H253].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))) as H254.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H221.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H254 as [H254 H255].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H256.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H223.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H256 as [H256 H257].
assert (* AndElim *) ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D)))) as H258.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H225.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H258 as [H258 H259].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B)))) as H260.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H260 as [H260 H261].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))) as H262.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H229.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H262 as [H262 H263].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G)))) as H264.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H231.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H264 as [H264 H265].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))) as H266.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H233.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H266 as [H266 H267].
assert (* AndElim *) ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F)))) as H268.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H235.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H268 as [H268 H269].
assert (* AndElim *) ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))) as H270.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H237.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H270 as [H270 H271].
assert (* AndElim *) ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))) as H272.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H239.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H272 as [H272 H273].
assert (* AndElim *) ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))) as H274.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H241.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H274 as [H274 H275].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))) as H276.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H243.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H276 as [H276 H277].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H278.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H245.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H278 as [H278 H279].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))) as H280.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H247.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H280 as [H280 H281].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H282.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H249.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H282 as [H282 H283].
assert (* AndElim *) ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))) as H284.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H251.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H284 as [H284 H285].
assert (* AndElim *) ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))) as H286.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H253.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H286 as [H286 H287].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))) as H288.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H255.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H288 as [H288 H289].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H290.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H257.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H290 as [H290 H291].
assert (* AndElim *) ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))) as H292.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H259.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H292 as [H292 H293].
assert (* AndElim *) ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))) as H294.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H261.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H294 as [H294 H295].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))) as H296.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H263.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H296 as [H296 H297].
assert (* AndElim *) ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))) as H298.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H265.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H298 as [H298 H299].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))) as H300.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H267.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H300 as [H300 H301].
assert (* AndElim *) ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))) as H302.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H269.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H302 as [H302 H303].
assert (* Cut *) (False) as H304.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H117 H131).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H305.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@H132 H133).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert False.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------exact H305.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- contradiction.

------------------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.BetS D G E \/ (euclidean__axioms.BetS G D E) \/ (euclidean__axioms.BetS G E D)) as H132.
-------------------------------------------------------------------------------------------------------------------------- exact H131.
-------------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132|H132].
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS G D E))) as H133.
---------------------------------------------------------------------------------------------------------------------------- intro H133.
apply (@H119 H132).
---------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS G D E)).
-----------------------------------------------------------------------------------------------------------------------------intro H134.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))))))) as H135.
------------------------------------------------------------------------------------------------------------------------------ exact H0.
------------------------------------------------------------------------------------------------------------------------------ destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))))))) as H137.
------------------------------------------------------------------------------------------------------------------------------- exact H6.
------------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))))))) as H139.
-------------------------------------------------------------------------------------------------------------------------------- exact H11.
-------------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))))) as H141.
--------------------------------------------------------------------------------------------------------------------------------- exact H16.
--------------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H143.
---------------------------------------------------------------------------------------------------------------------------------- exact H19.
---------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))))) as H145.
----------------------------------------------------------------------------------------------------------------------------------- exact H33.
----------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H147.
------------------------------------------------------------------------------------------------------------------------------------ exact H36.
------------------------------------------------------------------------------------------------------------------------------------ destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))))) as H149.
------------------------------------------------------------------------------------------------------------------------------------- exact H45.
------------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))))) as H151.
-------------------------------------------------------------------------------------------------------------------------------------- exact H51.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))))) as H153.
--------------------------------------------------------------------------------------------------------------------------------------- exact H52.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H155.
---------------------------------------------------------------------------------------------------------------------------------------- exact H53.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))))))) as H157.
----------------------------------------------------------------------------------------------------------------------------------------- exact H56.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))))))) as H159.
------------------------------------------------------------------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))))) as H161.
------------------------------------------------------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))))))) as H163.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))))) as H165.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__axioms.neq G e) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))))))) as H167.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R)))))) as H169.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H136.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R)))))) as H171.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R)))))) as H173.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H140.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))))) as H175.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H142.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H177.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))))) as H179.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H146.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H181.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H148.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))))) as H183.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H150.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H183 as [H183 H184].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))))) as H185.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H152.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H185 as [H185 H186].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))))) as H187.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H154.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H187 H188].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H189.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H156.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H189 H190].
assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D)))))) as H191.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H158.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B)))))) as H193.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H160.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))))) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H162.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G)))))) as H197.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H164.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))))) as H199.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H166.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [H199 H200].
assert (* AndElim *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F)))))) as H201.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H168.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [H201 H202].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))))) as H203.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H170.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [H203 H204].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))))) as H205.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H172.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [H205 H206].
assert (* AndElim *) ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))))) as H207.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H174.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H207 as [H207 H208].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))) as H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [H209 H210].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H211.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [H211 H212].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))) as H213.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H213 as [H213 H214].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H215.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [H215 H216].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))) as H217.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [H217 H218].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))) as H219.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H186.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H219 as [H219 H220].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))) as H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H223.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H223 as [H223 H224].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))))) as H225.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H192.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H225 as [H225 H226].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))))) as H227.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H227 as [H227 H228].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))) as H229.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [H229 H230].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))))) as H231.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H198.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H231 as [H231 H232].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))) as H233.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H233 as [H233 H234].
assert (* AndElim *) ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))))) as H235.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H202.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H235 as [H235 H236].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R)))) as H237.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H204.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H237 as [H237 H238].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R)))) as H239.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H206.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H239 as [H239 H240].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R)))) as H241.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H241 as [H241 H242].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))) as H243.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H210.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H243 as [H243 H244].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H245.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H245 as [H245 H246].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))) as H247.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H247 as [H247 H248].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H249.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H216.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H249 as [H249 H250].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))) as H251.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H218.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H251 as [H251 H252].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))) as H253.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H220.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H253 as [H253 H254].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))) as H255.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H222.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H255 as [H255 H256].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H257.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H224.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H257 as [H257 H258].
assert (* AndElim *) ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D)))) as H259.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H226.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H259 as [H259 H260].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B)))) as H261.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H228.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H261 as [H261 H262].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))) as H263.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H263 as [H263 H264].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G)))) as H265.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H232.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H265 as [H265 H266].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))) as H267.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H234.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H267 as [H267 H268].
assert (* AndElim *) ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F)))) as H269.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H236.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H269 as [H269 H270].
assert (* AndElim *) ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))) as H271.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H238.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H271 as [H271 H272].
assert (* AndElim *) ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))) as H273.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H240.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H273 as [H273 H274].
assert (* AndElim *) ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))) as H275.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H242.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H275 as [H275 H276].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))) as H277.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H244.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H277 as [H277 H278].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H279.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H246.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H279 as [H279 H280].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))) as H281.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H248.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H281 as [H281 H282].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H283.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H250.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H283 as [H283 H284].
assert (* AndElim *) ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))) as H285.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H252.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H285 as [H285 H286].
assert (* AndElim *) ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))) as H287.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H254.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H287 as [H287 H288].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))) as H289.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H256.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H289 as [H289 H290].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H291.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H258.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H291 as [H291 H292].
assert (* AndElim *) ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))) as H293.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H260.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H293 as [H293 H294].
assert (* AndElim *) ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))) as H295.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H262.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H295 as [H295 H296].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))) as H297.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H264.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H297 as [H297 H298].
assert (* AndElim *) ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))) as H299.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H266.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H299 as [H299 H300].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))) as H301.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H268.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H301 as [H301 H302].
assert (* AndElim *) ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))) as H303.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H270.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H303 as [H303 H304].
assert (* Cut *) (False) as H305.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H119 H132).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H306.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H133 H134).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert False.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------exact H306.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- contradiction.

--------------------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.BetS G D E \/ euclidean__axioms.BetS G E D) as H133.
---------------------------------------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133|H133].
----------------------------------------------------------------------------------------------------------------------------- exact H133.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS G D E))) as H134.
------------------------------------------------------------------------------------------------------------------------------ intro H134.
apply (@H120 H133).
------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS G D E)).
-------------------------------------------------------------------------------------------------------------------------------intro H135.
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))))))) as H136.
-------------------------------------------------------------------------------------------------------------------------------- exact H0.
-------------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))))))) as H138.
--------------------------------------------------------------------------------------------------------------------------------- exact H6.
--------------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))))))) as H140.
---------------------------------------------------------------------------------------------------------------------------------- exact H11.
---------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))))) as H142.
----------------------------------------------------------------------------------------------------------------------------------- exact H16.
----------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H144.
------------------------------------------------------------------------------------------------------------------------------------ exact H19.
------------------------------------------------------------------------------------------------------------------------------------ destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))))) as H146.
------------------------------------------------------------------------------------------------------------------------------------- exact H33.
------------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))))) as H148.
-------------------------------------------------------------------------------------------------------------------------------------- exact H36.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))))) as H150.
--------------------------------------------------------------------------------------------------------------------------------------- exact H45.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))))) as H152.
---------------------------------------------------------------------------------------------------------------------------------------- exact H51.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))))) as H154.
----------------------------------------------------------------------------------------------------------------------------------------- exact H52.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))))) as H156.
------------------------------------------------------------------------------------------------------------------------------------------ exact H53.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))))))) as H158.
------------------------------------------------------------------------------------------------------------------------------------------- exact H56.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))))))) as H160.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))))) as H162.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))))))) as H164.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))))) as H166.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H113.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.neq G e) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))))))) as H168.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H168 as [H168 H169].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R)))))) as H170.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H137.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R)))))) as H172.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H139.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R)))))) as H174.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H141.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H174 as [H174 H175].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))))) as H176.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H143.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H176 H177].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H178.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H145.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H178 H179].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))))) as H180.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H147.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H180 as [H180 H181].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))) as H182.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H149.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H182 H183].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))))) as H184.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H151.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H184 H185].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))))) as H186.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H153.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H186 H187].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))))) as H188.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H155.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))))) as H190.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H157.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H190 H191].
assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D)))))) as H192.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H192 as [H192 H193].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B)))))) as H194.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H161.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H194 as [H194 H195].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))))) as H196.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G)))))) as H198.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H165.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [H198 H199].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))))) as H200.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H167.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H200 H201].
assert (* AndElim *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F)))))) as H202.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H169.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H202 H203].
assert (* AndElim *) ((euclidean__axioms.neq B R) /\ ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))))) as H204.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H171.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H204 as [H204 H205].
assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))))) as H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H173.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H206 H207].
assert (* AndElim *) ((euclidean__axioms.neq F R) /\ ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))))) as H208.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H175.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [H208 H209].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))) as H210.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [H210 H211].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H212.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H179.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))))) as H214.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))))) as H216.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H183.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H216 as [H216 H217].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))) as H218.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H185.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H218 as [H218 H219].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))))) as H220.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [H220 H221].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))))) as H222.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H222 as [H222 H223].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))))) as H224.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H224 as [H224 H225].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))))) as H226.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H193.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H226 as [H226 H227].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))))) as H228.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H195.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H228 as [H228 H229].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))) as H230.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H197.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H230 as [H230 H231].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))))) as H232.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H199.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H232 as [H232 H233].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))))) as H234.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H234 as [H234 H235].
assert (* AndElim *) ((euclidean__axioms.neq e F) /\ ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))))) as H236.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H236 as [H236 H237].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B R)) /\ ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R)))) as H238.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H238 as [H238 H239].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A R)) /\ ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R)))) as H240.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H207.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H240 as [H240 H241].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F R)) /\ ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R)))) as H242.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H242 as [H242 H243].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))) as H244.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H244 as [H244 H245].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H246.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H246 as [H246 H247].
assert (* AndElim *) ((~(euclidean__axioms.BetS B F C)) /\ ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C)))) as H248.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H248 as [H248 H249].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))) as H250.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H217.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H250 as [H250 H251].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))) as H252.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H219.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H252 as [H252 H253].
assert (* AndElim *) ((~(euclidean__axioms.BetS C A B)) /\ ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B)))) as H254.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H254 as [H254 H255].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B)))) as H256.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H223.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H256 as [H256 H257].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D)))) as H258.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H225.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H258 as [H258 H259].
assert (* AndElim *) ((~(euclidean__axioms.BetS F B D)) /\ ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D)))) as H260.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H260 as [H260 H261].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A B)) /\ ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B)))) as H262.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H229.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H262 as [H262 H263].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))) as H264.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H231.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H264 as [H264 H265].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A G)) /\ ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G)))) as H266.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H233.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H266 as [H266 H267].
assert (* AndElim *) ((~(euclidean__axioms.BetS D A E)) /\ ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E)))) as H268.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H235.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H268 as [H268 H269].
assert (* AndElim *) ((~(euclidean__axioms.BetS G e F)) /\ ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F)))) as H270.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H237.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H270 as [H270 H271].
assert (* AndElim *) ((~(euclidean__axioms.BetS A R B)) /\ (~(euclidean__axioms.BetS B A R))) as H272.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H239.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H272 as [H272 H273].
assert (* AndElim *) ((~(euclidean__axioms.BetS B R A)) /\ (~(euclidean__axioms.BetS A B R))) as H274.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H241.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H274 as [H274 H275].
assert (* AndElim *) ((~(euclidean__axioms.BetS B R F)) /\ (~(euclidean__axioms.BetS F B R))) as H276.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H243.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H276 as [H276 H277].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))) as H278.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H245.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H278 as [H278 H279].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H280.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H247.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H280 as [H280 H281].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C F)) /\ (~(euclidean__axioms.BetS F B C))) as H282.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H249.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H282 as [H282 H283].
assert (* AndElim *) ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C))) as H284.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H251.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H284 as [H284 H285].
assert (* AndElim *) ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))) as H286.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H253.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H286 as [H286 H287].
assert (* AndElim *) ((~(euclidean__axioms.BetS C B A)) /\ (~(euclidean__axioms.BetS A C B))) as H288.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H255.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H288 as [H288 H289].
assert (* AndElim *) ((~(euclidean__axioms.BetS A B D)) /\ (~(euclidean__axioms.BetS D A B))) as H290.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H257.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H290 as [H290 H291].
assert (* AndElim *) ((~(euclidean__axioms.BetS A D B)) /\ (~(euclidean__axioms.BetS B A D))) as H292.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H259.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H292 as [H292 H293].
assert (* AndElim *) ((~(euclidean__axioms.BetS F D B)) /\ (~(euclidean__axioms.BetS B F D))) as H294.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H261.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H294 as [H294 H295].
assert (* AndElim *) ((~(euclidean__axioms.BetS D B A)) /\ (~(euclidean__axioms.BetS A D B))) as H296.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H263.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H296 as [H296 H297].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))) as H298.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H265.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H298 as [H298 H299].
assert (* AndElim *) ((~(euclidean__axioms.BetS D G A)) /\ (~(euclidean__axioms.BetS A D G))) as H300.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H267.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H300 as [H300 H301].
assert (* AndElim *) ((~(euclidean__axioms.BetS D E A)) /\ (~(euclidean__axioms.BetS A D E))) as H302.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H269.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H302 as [H302 H303].
assert (* AndElim *) ((~(euclidean__axioms.BetS G F e)) /\ (~(euclidean__axioms.BetS e G F))) as H304.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H271.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H304 as [H304 H305].
assert (* Cut *) (False) as H306.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H120 H133).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H307.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H134 H135).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert False.
-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------exact H307.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- contradiction.

----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G D E) as H129.
------------------------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq E D) as H130.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (E) H117).
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E D A) as H131.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (G) (D) (E) (A) (H81) (H129) H130).
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H132.
--------------------------------------------------------------------------------------------------------------------- apply (@proposition__34.proposition__34 (D) (A) (E) (B) H75).
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B D E) as H133.
---------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H133.
----------------------------------------------------------------------------------------------------------------------- exact H132.
----------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H135.
------------------------------------------------------------------------------------------------------------------------ exact H134.
------------------------------------------------------------------------------------------------------------------------ destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H137.
------------------------------------------------------------------------------------------------------------------------- exact H136.
------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H139.
-------------------------------------------------------------------------------------------------------------------------- exact H138.
-------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (D) (E) (B) H135).
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B E D) as H134.
----------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H134.
------------------------------------------------------------------------------------------------------------------------ exact H132.
------------------------------------------------------------------------------------------------------------------------ destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H136.
------------------------------------------------------------------------------------------------------------------------- exact H135.
------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H138.
-------------------------------------------------------------------------------------------------------------------------- exact H137.
-------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H140.
--------------------------------------------------------------------------------------------------------------------------- exact H139.
--------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* Cut *) ((euclidean__axioms.Cong B A E D) /\ ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D))) as H142.
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (D) (E) H133).
---------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A E D) /\ ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D))) as H143.
----------------------------------------------------------------------------------------------------------------------------- exact H142.
----------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D)) as H145.
------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------ destruct H145 as [H145 H146].
exact H146.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A D) as H135.
------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H135.
------------------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H137.
-------------------------------------------------------------------------------------------------------------------------- exact H136.
-------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H139.
--------------------------------------------------------------------------------------------------------------------------- exact H138.
--------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H141.
---------------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (A) (D) (B) H24).
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A D E B) as H136.
------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H136.
-------------------------------------------------------------------------------------------------------------------------- exact H132.
-------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H138.
--------------------------------------------------------------------------------------------------------------------------- exact H137.
--------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H140.
---------------------------------------------------------------------------------------------------------------------------- exact H139.
---------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H142.
----------------------------------------------------------------------------------------------------------------------------- exact H141.
----------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* Cut *) ((euclidean__axioms.Cong A D B E) /\ ((euclidean__axioms.Cong A D E B) /\ (euclidean__axioms.Cong D A B E))) as H144.
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (D) (A) (E) (B) H136).
------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong A D B E) /\ ((euclidean__axioms.Cong A D E B) /\ (euclidean__axioms.Cong D A B E))) as H145.
------------------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.Cong A D E B) /\ (euclidean__axioms.Cong D A B E)) as H147.
-------------------------------------------------------------------------------------------------------------------------------- exact H146.
-------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
exact H147.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B E B) as H137.
-------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H137.
--------------------------------------------------------------------------------------------------------------------------- exact H132.
--------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H139.
---------------------------------------------------------------------------------------------------------------------------- exact H138.
---------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H141.
----------------------------------------------------------------------------------------------------------------------------- exact H140.
----------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H143.
------------------------------------------------------------------------------------------------------------------------------ exact H142.
------------------------------------------------------------------------------------------------------------------------------ destruct H143 as [H143 H144].
apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (B) (A) (D) (E) (B) (H135) H136).
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B B E) as H138.
--------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H138.
---------------------------------------------------------------------------------------------------------------------------- exact H132.
---------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H140.
----------------------------------------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H142.
------------------------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------------------------ destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H144.
------------------------------------------------------------------------------------------------------------------------------- exact H143.
------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* Cut *) ((euclidean__axioms.Cong B A B E) /\ ((euclidean__axioms.Cong B A E B) /\ (euclidean__axioms.Cong A B B E))) as H146.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (E) (B) H137).
-------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A B E) /\ ((euclidean__axioms.Cong B A E B) /\ (euclidean__axioms.Cong A B B E))) as H147.
--------------------------------------------------------------------------------------------------------------------------------- exact H146.
--------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.Cong B A E B) /\ (euclidean__axioms.Cong A B B E)) as H149.
---------------------------------------------------------------------------------------------------------------------------------- exact H148.
---------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
exact H150.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B D A) as H139.
---------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H139.
----------------------------------------------------------------------------------------------------------------------------- exact H132.
----------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H141.
------------------------------------------------------------------------------------------------------------------------------ exact H140.
------------------------------------------------------------------------------------------------------------------------------ destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H143.
------------------------------------------------------------------------------------------------------------------------------- exact H142.
------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H145.
-------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* Cut *) ((euclidean__axioms.Cong B A D A) /\ ((euclidean__axioms.Cong B A A D) /\ (euclidean__axioms.Cong A B D A))) as H147.
--------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (B) (A) (D) H135).
--------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B A D A) /\ ((euclidean__axioms.Cong B A A D) /\ (euclidean__axioms.Cong A B D A))) as H148.
---------------------------------------------------------------------------------------------------------------------------------- exact H147.
---------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.Cong B A A D) /\ (euclidean__axioms.Cong A B D A)) as H150.
----------------------------------------------------------------------------------------------------------------------------------- exact H149.
----------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
exact H151.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B E D D A B) as H140.
----------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H140.
------------------------------------------------------------------------------------------------------------------------------ exact H132.
------------------------------------------------------------------------------------------------------------------------------ destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H142.
------------------------------------------------------------------------------------------------------------------------------- exact H141.
------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H144.
-------------------------------------------------------------------------------------------------------------------------------- exact H143.
-------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H146.
--------------------------------------------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (A) (B) (B) (E) (D) H146).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B E E D A) as H141.
------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H141.
------------------------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H143.
-------------------------------------------------------------------------------------------------------------------------------- exact H142.
-------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H145.
--------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H147.
---------------------------------------------------------------------------------------------------------------------------------- exact H146.
---------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (E) (D) (A) (A) (B) (E) H145).
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Per B E D) as H142.
------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H142.
-------------------------------------------------------------------------------------------------------------------------------- exact H132.
-------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H144.
--------------------------------------------------------------------------------------------------------------------------------- exact H143.
--------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H146.
---------------------------------------------------------------------------------------------------------------------------------- exact H145.
---------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H148.
----------------------------------------------------------------------------------------------------------------------------------- exact H147.
----------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
apply (@lemma__equaltorightisright.lemma__equaltorightisright (D) (A) (B) (B) (E) (D) (H79) H140).
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per A B E) as H143.
-------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H143.
--------------------------------------------------------------------------------------------------------------------------------- exact H132.
--------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H145.
---------------------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H147.
----------------------------------------------------------------------------------------------------------------------------------- exact H146.
----------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H149.
------------------------------------------------------------------------------------------------------------------------------------ exact H148.
------------------------------------------------------------------------------------------------------------------------------------ destruct H149 as [H149 H150].
apply (@lemma__equaltorightisright.lemma__equaltorightisright (E) (D) (A) (A) (B) (E) (H131) H141).
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.SQ A B E D) as H144.
--------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------- exact H134.
---------------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------------- exact H138.
----------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------------- exact H143.
-------------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------------------------------- exact H131.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG B A D E) as H145.
---------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H145.
----------------------------------------------------------------------------------------------------------------------------------- exact H132.
----------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H147.
------------------------------------------------------------------------------------------------------------------------------------ exact H146.
------------------------------------------------------------------------------------------------------------------------------------ destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H149.
------------------------------------------------------------------------------------------------------------------------------------- exact H148.
------------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H151.
-------------------------------------------------------------------------------------------------------------------------------------- exact H150.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
apply (@lemma__PGsymmetric.lemma__PGsymmetric (D) (E) (B) (A) H75).
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG A B E D) as H146.
----------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H146.
------------------------------------------------------------------------------------------------------------------------------------ exact H132.
------------------------------------------------------------------------------------------------------------------------------------ destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)))) as H148.
------------------------------------------------------------------------------------------------------------------------------------- exact H147.
------------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))) as H150.
-------------------------------------------------------------------------------------------------------------------------------------- exact H149.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E)) as H152.
--------------------------------------------------------------------------------------------------------------------------------------- exact H151.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
apply (@lemma__PGflip.lemma__PGflip (B) (A) (D) (E) H145).
----------------------------------------------------------------------------------------------------------------------------------- exists E.
exists D.
split.
------------------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------- exact H44.
------------------------------------------------------------------------------------------------------------------------------------- exact H146.
Qed.
