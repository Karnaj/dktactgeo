Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__rayimpliescollinear.
Require Export lemma__supplements.
Require Export logic.
Require Export proposition__04.
Require Export proposition__07.
Definition proposition__14 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__defs.RT A B C D B E) -> ((euclidean__defs.Out B C D) -> ((euclidean__axioms.TS E D B A) -> ((euclidean__defs.Supp A B C D E) /\ (euclidean__axioms.BetS A B E)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
assert (* Cut *) (exists (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D B E d b e))) as H2.
- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D B E V Y Z))) as H2.
-- exact H.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D B E V Y Z))) as __TmpHyp.
--- exact H2.
--- assert (exists X: euclidean__axioms.Point, (exists (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D B E V Y Z)))) as H3.
---- exact __TmpHyp.
---- destruct H3 as [x H3].
assert (exists Y: euclidean__axioms.Point, (exists (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x Y U V Z) /\ ((euclidean__defs.CongA A B C x Y U) /\ (euclidean__defs.CongA D B E V Y Z)))) as H4.
----- exact H3.
----- destruct H4 as [x0 H4].
assert (exists Z: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V Z) /\ ((euclidean__defs.CongA A B C x x0 U) /\ (euclidean__defs.CongA D B E V x0 Z)))) as H5.
------ exact H4.
------ destruct H5 as [x1 H5].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V x1) /\ ((euclidean__defs.CongA A B C x x0 U) /\ (euclidean__defs.CongA D B E V x0 x1)))) as H6.
------- exact H5.
------- destruct H6 as [x2 H6].
assert (exists V: euclidean__axioms.Point, ((euclidean__defs.Supp x x0 x2 V x1) /\ ((euclidean__defs.CongA A B C x x0 x2) /\ (euclidean__defs.CongA D B E V x0 x1)))) as H7.
-------- exact H6.
-------- destruct H7 as [x3 H7].
assert (* AndElim *) ((euclidean__defs.Supp x x0 x2 x3 x1) /\ ((euclidean__defs.CongA A B C x x0 x2) /\ (euclidean__defs.CongA D B E x3 x0 x1))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.CongA A B C x x0 x2) /\ (euclidean__defs.CongA D B E x3 x0 x1)) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
exists x.
exists x0.
exists x2.
exists x3.
exists x1.
split.
----------- exact H8.
----------- split.
------------ exact H10.
------------ exact H11.
- assert (exists a: euclidean__axioms.Point, (exists (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D B E d b e)))) as H3.
-- exact H2.
-- destruct H3 as [a H3].
assert (exists b: euclidean__axioms.Point, (exists (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D B E d b e)))) as H4.
--- exact H3.
--- destruct H4 as [b H4].
assert (exists c: euclidean__axioms.Point, (exists (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D B E d b e)))) as H5.
---- exact H4.
---- destruct H5 as [c H5].
assert (exists d: euclidean__axioms.Point, (exists (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D B E d b e)))) as H6.
----- exact H5.
----- destruct H6 as [d H6].
assert (exists e: euclidean__axioms.Point, ((euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D B E d b e)))) as H7.
------ exact H6.
------ destruct H7 as [e H7].
assert (* AndElim *) ((euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D B E d b e))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D B E d b e)) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* Cut *) (euclidean__defs.CongA a b c A B C) as H12.
--------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (a) (b) (c) H10).
--------- assert (* Cut *) (euclidean__defs.CongA d b e D B E) as H13.
---------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (B) (E) (d) (b) (e) H11).
---------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H14.
----------- apply (@euclidean__tactics.nCol__notCol (A) (B) (C)).
------------apply (@euclidean__tactics.nCol__not__Col (A) (B) (C)).
-------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (a) (b) (c) (A) (B) (C) H12).


----------- assert (* Cut *) (euclidean__axioms.neq A B) as H15.
------------ assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H15.
------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H14).
------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
exact H16.
------------ assert (* Cut *) (euclidean__axioms.nCol D B E) as H16.
------------- apply (@euclidean__tactics.nCol__notCol (D) (B) (E)).
--------------apply (@euclidean__tactics.nCol__not__Col (D) (B) (E)).
---------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (d) (b) (e) (D) (B) (E) H13).


------------- assert (* Cut *) (euclidean__axioms.neq B E) as H17.
-------------- assert (* Cut *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D)))))) as H17.
--------------- apply (@lemma__NCdistinct.lemma__NCdistinct (D) (B) (E) H16).
--------------- assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D)))))) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D))))) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D)))) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D)) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
exact H20.
-------------- assert (* Cut *) (exists (T: euclidean__axioms.Point), (euclidean__axioms.BetS A B T) /\ (euclidean__axioms.Cong B T B E)) as H18.
--------------- apply (@lemma__extension.lemma__extension (A) (B) (B) (E) (H15) H17).
--------------- assert (exists T: euclidean__axioms.Point, ((euclidean__axioms.BetS A B T) /\ (euclidean__axioms.Cong B T B E))) as H19.
---------------- exact H18.
---------------- destruct H19 as [T H19].
assert (* AndElim *) ((euclidean__axioms.BetS A B T) /\ (euclidean__axioms.Cong B T B E)) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
assert (* Cut *) (euclidean__axioms.Cong B D B D) as H22.
------------------ apply (@euclidean__axioms.cn__congruencereflexive (B) D).
------------------ assert (* Cut *) (euclidean__defs.Supp A B C D T) as H23.
------------------- split.
-------------------- exact H0.
-------------------- exact H20.
------------------- assert (* Cut *) (euclidean__defs.CongA a b c A B C) as H24.
-------------------- exact H12.
-------------------- assert (* Cut *) (euclidean__defs.CongA d b e D B E) as H25.
--------------------- exact H13.
--------------------- assert (* Cut *) (euclidean__defs.CongA d b e D B T) as H26.
---------------------- apply (@lemma__supplements.lemma__supplements (a) (b) (c) (d) (e) (A) (B) (C) (D) (T) (H24) (H8) H23).
---------------------- assert (* Cut *) (euclidean__defs.CongA D B E D B T) as H27.
----------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (D) (B) (E) (d) (b) (e) (D) (B) (T) (H11) H26).
----------------------- assert (* Cut *) (euclidean__defs.CongA D B T D B E) as H28.
------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (B) (E) (D) (B) (T) H27).
------------------------ assert (* Cut *) (euclidean__axioms.Col A B T) as H29.
------------------------- right.
right.
right.
right.
left.
exact H20.
------------------------- assert (* Cut *) (euclidean__axioms.neq B T) as H30.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq B T) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A T))) as H30.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (T) H20).
--------------------------- assert (* AndElim *) ((euclidean__axioms.neq B T) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A T))) as H31.
---------------------------- exact H30.
---------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A T)) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
exact H31.
-------------------------- assert (* Cut *) (euclidean__axioms.neq T B) as H31.
--------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (T) H30).
--------------------------- assert (* Cut *) (B = B) as H32.
---------------------------- apply (@logic.eq__refl (Point) B).
---------------------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H33.
----------------------------- right.
right.
left.
exact H32.
----------------------------- assert (* Cut *) (euclidean__axioms.nCol T B C) as H34.
------------------------------ apply (@euclidean__tactics.nCol__notCol (T) (B) (C)).
-------------------------------apply (@euclidean__tactics.nCol__not__Col (T) (B) (C)).
--------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (B) (C) (T) (B) (H14) (H29) (H33) H31).


------------------------------ assert (* Cut *) (euclidean__axioms.nCol C B T) as H35.
------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B T C) /\ ((euclidean__axioms.nCol B C T) /\ ((euclidean__axioms.nCol C T B) /\ ((euclidean__axioms.nCol T C B) /\ (euclidean__axioms.nCol C B T))))) as H35.
-------------------------------- apply (@lemma__NCorder.lemma__NCorder (T) (B) (C) H34).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B T C) /\ ((euclidean__axioms.nCol B C T) /\ ((euclidean__axioms.nCol C T B) /\ ((euclidean__axioms.nCol T C B) /\ (euclidean__axioms.nCol C B T))))) as H36.
--------------------------------- exact H35.
--------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.nCol B C T) /\ ((euclidean__axioms.nCol C T B) /\ ((euclidean__axioms.nCol T C B) /\ (euclidean__axioms.nCol C B T)))) as H38.
---------------------------------- exact H37.
---------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.nCol C T B) /\ ((euclidean__axioms.nCol T C B) /\ (euclidean__axioms.nCol C B T))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.nCol T C B) /\ (euclidean__axioms.nCol C B T)) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
exact H43.
------------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H36.
-------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (B) (C) (D) H0).
-------------------------------- assert (* Cut *) (euclidean__axioms.Col C B D) as H37.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H37.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (D) H36).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H38.
----------------------------------- exact H37.
----------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)))) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)) as H44.
-------------------------------------- exact H43.
-------------------------------------- destruct H44 as [H44 H45].
exact H38.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H38.
---------------------------------- assert (* Cut *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D)))))) as H38.
----------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (D) (B) (E) H16).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D)))))) as H39.
------------------------------------ exact H38.
------------------------------------ destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D))))) as H41.
------------------------------------- exact H40.
------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D)))) as H43.
-------------------------------------- exact H42.
-------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D))) as H45.
--------------------------------------- exact H44.
--------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E D)) as H47.
---------------------------------------- exact H46.
---------------------------------------- destruct H47 as [H47 H48].
exact H39.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col C B B) as H39.
----------------------------------- right.
right.
left.
exact H32.
----------------------------------- assert (* Cut *) (euclidean__axioms.nCol D B T) as H40.
------------------------------------ apply (@euclidean__tactics.nCol__notCol (D) (B) (T)).
-------------------------------------apply (@euclidean__tactics.nCol__not__Col (D) (B) (T)).
--------------------------------------apply (@lemma__NChelper.lemma__NChelper (C) (B) (T) (D) (B) (H35) (H37) (H39) H38).


------------------------------------ assert (* Cut *) (euclidean__axioms.Cong D T D E) as H41.
------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (a0: euclidean__axioms.Point) (b0: euclidean__axioms.Point) (c0: euclidean__axioms.Point), (euclidean__axioms.Cong A0 B0 a0 b0) -> ((euclidean__axioms.Cong A0 C0 a0 c0) -> ((euclidean__defs.CongA B0 A0 C0 b0 a0 c0) -> (euclidean__axioms.Cong B0 C0 b0 c0)))) as H41.
-------------------------------------- intro A0.
intro B0.
intro C0.
intro a0.
intro b0.
intro c0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b0 c0) /\ ((euclidean__defs.CongA A0 B0 C0 a0 b0 c0) /\ (euclidean__defs.CongA A0 C0 B0 a0 c0 b0))) as __2.
--------------------------------------- apply (@proposition__04.proposition__04 (A0) (B0) (C0) (a0) (b0) (c0) (__) (__0) __1).
--------------------------------------- destruct __2 as [__2 __3].
exact __2.
-------------------------------------- apply (@H41 (B) (D) (T) (B) (D) (E) (H22) (H21) H28).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong T D E D) as H42.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong T D E D) /\ ((euclidean__axioms.Cong T D D E) /\ (euclidean__axioms.Cong D T E D))) as H42.
--------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (D) (T) (D) (E) H41).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong T D E D) /\ ((euclidean__axioms.Cong T D D E) /\ (euclidean__axioms.Cong D T E D))) as H43.
---------------------------------------- exact H42.
---------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Cong T D D E) /\ (euclidean__axioms.Cong D T E D)) as H45.
----------------------------------------- exact H44.
----------------------------------------- destruct H45 as [H45 H46].
exact H43.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong T B E B) as H43.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong T B E B) /\ ((euclidean__axioms.Cong T B B E) /\ (euclidean__axioms.Cong B T E B))) as H43.
---------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (T) (B) (E) H21).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong T B E B) /\ ((euclidean__axioms.Cong T B B E) /\ (euclidean__axioms.Cong B T E B))) as H44.
----------------------------------------- exact H43.
----------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Cong T B B E) /\ (euclidean__axioms.Cong B T E B)) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
exact H44.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B B) as H44.
---------------------------------------- right.
right.
left.
exact H32.
---------------------------------------- assert (* Cut *) (euclidean__axioms.TS A D B E) as H45.
----------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (D) (B) (E) (A) H1).
----------------------------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS A m E) /\ ((euclidean__axioms.Col D B m) /\ (euclidean__axioms.nCol D B A))) as H46.
------------------------------------------ exact H45.
------------------------------------------ assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS A m E) /\ ((euclidean__axioms.Col D B m) /\ (euclidean__axioms.nCol D B A)))) as H47.
------------------------------------------- exact H46.
------------------------------------------- destruct H47 as [m H47].
assert (* AndElim *) ((euclidean__axioms.BetS A m E) /\ ((euclidean__axioms.Col D B m) /\ (euclidean__axioms.nCol D B A))) as H48.
-------------------------------------------- exact H47.
-------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col D B m) /\ (euclidean__axioms.nCol D B A)) as H50.
--------------------------------------------- exact H49.
--------------------------------------------- destruct H50 as [H50 H51].
assert (* Cut *) (euclidean__axioms.BetS E m A) as H52.
---------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (m) (E) H48).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS T B A) as H53.
----------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (T) H20).
----------------------------------------------- assert (* Cut *) (euclidean__defs.OS T E D B) as H54.
------------------------------------------------ exists A.
exists B.
exists m.
split.
------------------------------------------------- exact H44.
------------------------------------------------- split.
-------------------------------------------------- exact H50.
-------------------------------------------------- split.
--------------------------------------------------- exact H53.
--------------------------------------------------- split.
---------------------------------------------------- exact H52.
---------------------------------------------------- split.
----------------------------------------------------- exact H40.
----------------------------------------------------- exact H16.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq B C) as H55.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B T) /\ ((euclidean__axioms.neq C T) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C)))))) as H55.
-------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (C) (B) (T) H35).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B T) /\ ((euclidean__axioms.neq C T) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C)))))) as H56.
--------------------------------------------------- exact H55.
--------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq B T) /\ ((euclidean__axioms.neq C T) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C))))) as H58.
---------------------------------------------------- exact H57.
---------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq C T) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C)))) as H60.
----------------------------------------------------- exact H59.
----------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C))) as H62.
------------------------------------------------------ exact H61.
------------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq T B) /\ (euclidean__axioms.neq T C)) as H64.
------------------------------------------------------- exact H63.
------------------------------------------------------- destruct H64 as [H64 H65].
exact H62.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H56.
-------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H55).
-------------------------------------------------- assert (* Cut *) (T = E) as H57.
--------------------------------------------------- apply (@proposition__07.proposition__07 (D) (B) (T) (E) (H38) (H42) (H43) H54).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A B E) as H58.
---------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun T0: euclidean__axioms.Point => (euclidean__axioms.BetS A B T0) -> ((euclidean__axioms.Cong B T0 B E) -> ((euclidean__defs.Supp A B C D T0) -> ((euclidean__defs.CongA d b e D B T0) -> ((euclidean__defs.CongA D B E D B T0) -> ((euclidean__defs.CongA D B T0 D B E) -> ((euclidean__axioms.Col A B T0) -> ((euclidean__axioms.neq B T0) -> ((euclidean__axioms.neq T0 B) -> ((euclidean__axioms.nCol T0 B C) -> ((euclidean__axioms.nCol C B T0) -> ((euclidean__axioms.nCol D B T0) -> ((euclidean__axioms.Cong D T0 D E) -> ((euclidean__axioms.Cong T0 D E D) -> ((euclidean__axioms.Cong T0 B E B) -> ((euclidean__axioms.BetS T0 B A) -> ((euclidean__defs.OS T0 E D B) -> (euclidean__axioms.BetS A B E))))))))))))))))))) with (x := T).
-----------------------------------------------------intro H58.
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
intro H71.
intro H72.
intro H73.
intro H74.
exact H58.

----------------------------------------------------- exact H57.
----------------------------------------------------- exact H20.
----------------------------------------------------- exact H21.
----------------------------------------------------- exact H23.
----------------------------------------------------- exact H26.
----------------------------------------------------- exact H27.
----------------------------------------------------- exact H28.
----------------------------------------------------- exact H29.
----------------------------------------------------- exact H30.
----------------------------------------------------- exact H31.
----------------------------------------------------- exact H34.
----------------------------------------------------- exact H35.
----------------------------------------------------- exact H40.
----------------------------------------------------- exact H41.
----------------------------------------------------- exact H42.
----------------------------------------------------- exact H43.
----------------------------------------------------- exact H53.
----------------------------------------------------- exact H54.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Supp A B C D E) as H59.
----------------------------------------------------- split.
------------------------------------------------------ exact H0.
------------------------------------------------------ exact H58.
----------------------------------------------------- split.
------------------------------------------------------ exact H59.
------------------------------------------------------ exact H58.
Qed.
