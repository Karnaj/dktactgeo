Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__3.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__PGrectangle.
Require Export lemma__PGrotate.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__collinearright.
Require Export lemma__congruencesymmetric.
Require Export lemma__equaltorightisright.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__oppositesideflip.
Require Export lemma__paste5.
Require Export lemma__rectanglerotate.
Require Export lemma__rightangleNC.
Require Export lemma__squaresequal.
Require Export logic.
Require Export proposition__08.
Require Export proposition__11B.
Require Export proposition__46.
Require Export proposition__47.
Require Export proposition__48A.
Definition proposition__48 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point) (K: euclidean__axioms.Point) (L: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.SQ A B F G) -> ((euclidean__defs.SQ A C K H) -> ((euclidean__defs.SQ B C E D) -> ((euclidean__axioms.BetS B M C) -> ((euclidean__axioms.BetS E L D) -> ((euclidean__axioms.EF A B F G B M L D) -> ((euclidean__axioms.EF A C K H M C E L) -> ((euclidean__defs.RE M C E L) -> (euclidean__defs.Per B A C))))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
intro K.
intro L.
intro M.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
intro H6.
intro H7.
intro H8.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H9.
- exact H0.
- assert (* Cut *) (euclidean__axioms.neq A C) as H10.
-- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H10.
--- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H9).
--- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H11.
---- exact H10.
---- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H13.
----- exact H12.
----- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H15.
------ exact H14.
------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H17.
------- exact H16.
------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H19.
-------- exact H18.
-------- destruct H19 as [H19 H20].
exact H15.
-- assert (* Cut *) (euclidean__axioms.neq A B) as H11.
--- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H11.
---- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H9).
---- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H12.
----- exact H11.
----- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H14.
------ exact H13.
------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H16.
------- exact H15.
------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H18.
-------- exact H17.
-------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H20.
--------- exact H19.
--------- destruct H20 as [H20 H21].
exact H12.
--- assert (* Cut *) (euclidean__axioms.neq B A) as H12.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H11).
---- assert (* Cut *) (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS B A R) /\ (euclidean__axioms.Cong A R A B)) as H13.
----- apply (@lemma__extension.lemma__extension (B) (A) (A) (B) (H12) H11).
----- assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS B A R) /\ (euclidean__axioms.Cong A R A B))) as H14.
------ exact H13.
------ destruct H14 as [R H14].
assert (* AndElim *) ((euclidean__axioms.BetS B A R) /\ (euclidean__axioms.Cong A R A B)) as H15.
------- exact H14.
------- destruct H15 as [H15 H16].
assert (* Cut *) (euclidean__axioms.Col B A R) as H17.
-------- right.
right.
right.
right.
left.
exact H15.
-------- assert (* Cut *) (euclidean__axioms.Col A B R) as H18.
--------- assert (* Cut *) ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B))))) as H18.
---------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (R) H17).
---------- assert (* AndElim *) ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B))))) as H19.
----------- exact H18.
----------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B)))) as H21.
------------ exact H20.
------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B))) as H23.
------------- exact H22.
------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B)) as H25.
-------------- exact H24.
-------------- destruct H25 as [H25 H26].
exact H19.
--------- assert (* Cut *) (B = B) as H19.
---------- apply (@logic.eq__refl (Point) B).
---------- assert (* Cut *) (euclidean__axioms.Col A B B) as H20.
----------- right.
right.
left.
exact H19.
----------- assert (* Cut *) (euclidean__axioms.neq B R) as H21.
------------ assert (* Cut *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B R))) as H21.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (A) (R) H15).
------------- assert (* AndElim *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B R))) as H22.
-------------- exact H21.
-------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B R)) as H24.
--------------- exact H23.
--------------- destruct H24 as [H24 H25].
exact H25.
------------ assert (* Cut *) (euclidean__axioms.neq R B) as H22.
------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (R) H21).
------------- assert (* Cut *) (euclidean__axioms.nCol R B C) as H23.
-------------- apply (@euclidean__tactics.nCol__notCol (R) (B) (C)).
---------------apply (@euclidean__tactics.nCol__not__Col (R) (B) (C)).
----------------apply (@lemma__NChelper.lemma__NChelper (A) (B) (C) (R) (B) (H9) (H18) (H20) H22).


-------------- assert (* Cut *) (euclidean__axioms.nCol B R C) as H24.
--------------- assert (* Cut *) ((euclidean__axioms.nCol B R C) /\ ((euclidean__axioms.nCol B C R) /\ ((euclidean__axioms.nCol C R B) /\ ((euclidean__axioms.nCol R C B) /\ (euclidean__axioms.nCol C B R))))) as H24.
---------------- apply (@lemma__NCorder.lemma__NCorder (R) (B) (C) H23).
---------------- assert (* AndElim *) ((euclidean__axioms.nCol B R C) /\ ((euclidean__axioms.nCol B C R) /\ ((euclidean__axioms.nCol C R B) /\ ((euclidean__axioms.nCol R C B) /\ (euclidean__axioms.nCol C B R))))) as H25.
----------------- exact H24.
----------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.nCol B C R) /\ ((euclidean__axioms.nCol C R B) /\ ((euclidean__axioms.nCol R C B) /\ (euclidean__axioms.nCol C B R)))) as H27.
------------------ exact H26.
------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.nCol C R B) /\ ((euclidean__axioms.nCol R C B) /\ (euclidean__axioms.nCol C B R))) as H29.
------------------- exact H28.
------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.nCol R C B) /\ (euclidean__axioms.nCol C B R)) as H31.
-------------------- exact H30.
-------------------- destruct H31 as [H31 H32].
exact H25.
--------------- assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__defs.Per B A Q) /\ (euclidean__axioms.TS Q B R C)) as H25.
---------------- apply (@proposition__11B.proposition__11B (B) (R) (A) (C) (H15) H24).
---------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__defs.Per B A Q) /\ (euclidean__axioms.TS Q B R C))) as H26.
----------------- exact H25.
----------------- destruct H26 as [Q H26].
assert (* AndElim *) ((euclidean__defs.Per B A Q) /\ (euclidean__axioms.TS Q B R C)) as H27.
------------------ exact H26.
------------------ destruct H27 as [H27 H28].
assert (* Cut *) (euclidean__axioms.nCol B A Q) as H29.
------------------- apply (@lemma__rightangleNC.lemma__rightangleNC (B) (A) (Q) H27).
------------------- assert (* Cut *) (euclidean__axioms.neq A Q) as H30.
-------------------- assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q B)))))) as H30.
--------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (B) (A) (Q) H29).
--------------------- assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q B)))))) as H31.
---------------------- exact H30.
---------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q B))))) as H33.
----------------------- exact H32.
----------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q B)))) as H35.
------------------------ exact H34.
------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q B))) as H37.
------------------------- exact H36.
------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q B)) as H39.
-------------------------- exact H38.
-------------------------- destruct H39 as [H39 H40].
exact H33.
-------------------- assert (* Cut *) (exists (c: euclidean__axioms.Point), (euclidean__defs.Out A Q c) /\ (euclidean__axioms.Cong A c A C)) as H31.
--------------------- apply (@lemma__layoff.lemma__layoff (A) (Q) (A) (C) (H30) H10).
--------------------- assert (exists c: euclidean__axioms.Point, ((euclidean__defs.Out A Q c) /\ (euclidean__axioms.Cong A c A C))) as H32.
---------------------- exact H31.
---------------------- destruct H32 as [c H32].
assert (* AndElim *) ((euclidean__defs.Out A Q c) /\ (euclidean__axioms.Cong A c A C)) as H33.
----------------------- exact H32.
----------------------- destruct H33 as [H33 H34].
assert (* Cut *) (euclidean__defs.Per B A c) as H35.
------------------------ apply (@lemma__8__3.lemma__8__3 (B) (A) (Q) (c) (H27) H33).
------------------------ assert (* Cut *) (euclidean__axioms.nCol B A c) as H36.
------------------------- apply (@lemma__rightangleNC.lemma__rightangleNC (B) (A) (c) H35).
------------------------- assert (* Cut *) (euclidean__axioms.nCol A B c) as H37.
-------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B c) /\ ((euclidean__axioms.nCol A c B) /\ ((euclidean__axioms.nCol c B A) /\ ((euclidean__axioms.nCol B c A) /\ (euclidean__axioms.nCol c A B))))) as H37.
--------------------------- apply (@lemma__NCorder.lemma__NCorder (B) (A) (c) H36).
--------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A B c) /\ ((euclidean__axioms.nCol A c B) /\ ((euclidean__axioms.nCol c B A) /\ ((euclidean__axioms.nCol B c A) /\ (euclidean__axioms.nCol c A B))))) as H38.
---------------------------- exact H37.
---------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.nCol A c B) /\ ((euclidean__axioms.nCol c B A) /\ ((euclidean__axioms.nCol B c A) /\ (euclidean__axioms.nCol c A B)))) as H40.
----------------------------- exact H39.
----------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.nCol c B A) /\ ((euclidean__axioms.nCol B c A) /\ (euclidean__axioms.nCol c A B))) as H42.
------------------------------ exact H41.
------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.nCol B c A) /\ (euclidean__axioms.nCol c A B)) as H44.
------------------------------- exact H43.
------------------------------- destruct H44 as [H44 H45].
exact H38.
-------------------------- assert (* Cut *) (exists (f: euclidean__axioms.Point) (g: euclidean__axioms.Point), (euclidean__defs.SQ A B f g) /\ ((euclidean__axioms.TS g A B c) /\ (euclidean__defs.PG A B f g))) as H38.
--------------------------- apply (@proposition__46.proposition__46 (A) (B) (c) (H11) H37).
--------------------------- assert (exists f: euclidean__axioms.Point, (exists (g: euclidean__axioms.Point), (euclidean__defs.SQ A B f g) /\ ((euclidean__axioms.TS g A B c) /\ (euclidean__defs.PG A B f g)))) as H39.
---------------------------- exact H38.
---------------------------- destruct H39 as [f H39].
assert (exists g: euclidean__axioms.Point, ((euclidean__defs.SQ A B f g) /\ ((euclidean__axioms.TS g A B c) /\ (euclidean__defs.PG A B f g)))) as H40.
----------------------------- exact H39.
----------------------------- destruct H40 as [g H40].
assert (* AndElim *) ((euclidean__defs.SQ A B f g) /\ ((euclidean__axioms.TS g A B c) /\ (euclidean__defs.PG A B f g))) as H41.
------------------------------ exact H40.
------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.TS g A B c) /\ (euclidean__defs.PG A B f g)) as H43.
------------------------------- exact H42.
------------------------------- destruct H43 as [H43 H44].
assert (* Cut *) (euclidean__axioms.neq A c) as H45.
-------------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B c) /\ ((euclidean__axioms.neq A c) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq c B) /\ (euclidean__axioms.neq c A)))))) as H45.
--------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (c) H37).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B c) /\ ((euclidean__axioms.neq A c) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq c B) /\ (euclidean__axioms.neq c A)))))) as H46.
---------------------------------- exact H45.
---------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq B c) /\ ((euclidean__axioms.neq A c) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq c B) /\ (euclidean__axioms.neq c A))))) as H48.
----------------------------------- exact H47.
----------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq A c) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq c B) /\ (euclidean__axioms.neq c A)))) as H50.
------------------------------------ exact H49.
------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq c B) /\ (euclidean__axioms.neq c A))) as H52.
------------------------------------- exact H51.
------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq c B) /\ (euclidean__axioms.neq c A)) as H54.
-------------------------------------- exact H53.
-------------------------------------- destruct H54 as [H54 H55].
exact H50.
-------------------------------- assert (* Cut *) (euclidean__axioms.nCol A c B) as H46.
--------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A c) /\ ((euclidean__axioms.nCol B c A) /\ ((euclidean__axioms.nCol c A B) /\ ((euclidean__axioms.nCol A c B) /\ (euclidean__axioms.nCol c B A))))) as H46.
---------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (c) H37).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A c) /\ ((euclidean__axioms.nCol B c A) /\ ((euclidean__axioms.nCol c A B) /\ ((euclidean__axioms.nCol A c B) /\ (euclidean__axioms.nCol c B A))))) as H47.
----------------------------------- exact H46.
----------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.nCol B c A) /\ ((euclidean__axioms.nCol c A B) /\ ((euclidean__axioms.nCol A c B) /\ (euclidean__axioms.nCol c B A)))) as H49.
------------------------------------ exact H48.
------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol c A B) /\ ((euclidean__axioms.nCol A c B) /\ (euclidean__axioms.nCol c B A))) as H51.
------------------------------------- exact H50.
------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol A c B) /\ (euclidean__axioms.nCol c B A)) as H53.
-------------------------------------- exact H52.
-------------------------------------- destruct H53 as [H53 H54].
exact H53.
--------------------------------- assert (* Cut *) (exists (k: euclidean__axioms.Point) (h: euclidean__axioms.Point), (euclidean__defs.SQ A c k h) /\ ((euclidean__axioms.TS h A c B) /\ (euclidean__defs.PG A c k h))) as H47.
---------------------------------- apply (@proposition__46.proposition__46 (A) (c) (B) (H45) H46).
---------------------------------- assert (exists k: euclidean__axioms.Point, (exists (h: euclidean__axioms.Point), (euclidean__defs.SQ A c k h) /\ ((euclidean__axioms.TS h A c B) /\ (euclidean__defs.PG A c k h)))) as H48.
----------------------------------- exact H47.
----------------------------------- destruct H48 as [k H48].
assert (exists h: euclidean__axioms.Point, ((euclidean__defs.SQ A c k h) /\ ((euclidean__axioms.TS h A c B) /\ (euclidean__defs.PG A c k h)))) as H49.
------------------------------------ exact H48.
------------------------------------ destruct H49 as [h H49].
assert (* AndElim *) ((euclidean__defs.SQ A c k h) /\ ((euclidean__axioms.TS h A c B) /\ (euclidean__defs.PG A c k h))) as H50.
------------------------------------- exact H49.
------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.TS h A c B) /\ (euclidean__defs.PG A c k h)) as H52.
-------------------------------------- exact H51.
-------------------------------------- destruct H52 as [H52 H53].
assert (* Cut *) (euclidean__axioms.neq B c) as H54.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A c) /\ ((euclidean__axioms.neq c B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c A) /\ ((euclidean__axioms.neq B c) /\ (euclidean__axioms.neq B A)))))) as H54.
---------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (c) (B) H46).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A c) /\ ((euclidean__axioms.neq c B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c A) /\ ((euclidean__axioms.neq B c) /\ (euclidean__axioms.neq B A)))))) as H55.
----------------------------------------- exact H54.
----------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq c B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c A) /\ ((euclidean__axioms.neq B c) /\ (euclidean__axioms.neq B A))))) as H57.
------------------------------------------ exact H56.
------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c A) /\ ((euclidean__axioms.neq B c) /\ (euclidean__axioms.neq B A)))) as H59.
------------------------------------------- exact H58.
------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.neq c A) /\ ((euclidean__axioms.neq B c) /\ (euclidean__axioms.neq B A))) as H61.
-------------------------------------------- exact H60.
-------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq B c) /\ (euclidean__axioms.neq B A)) as H63.
--------------------------------------------- exact H62.
--------------------------------------------- destruct H63 as [H63 H64].
exact H63.
--------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B c A) as H55.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol c A B) /\ ((euclidean__axioms.nCol c B A) /\ ((euclidean__axioms.nCol B A c) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol B c A))))) as H55.
----------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (c) (B) H46).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol c A B) /\ ((euclidean__axioms.nCol c B A) /\ ((euclidean__axioms.nCol B A c) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol B c A))))) as H56.
------------------------------------------ exact H55.
------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.nCol c B A) /\ ((euclidean__axioms.nCol B A c) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol B c A)))) as H58.
------------------------------------------- exact H57.
------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.nCol B A c) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol B c A))) as H60.
-------------------------------------------- exact H59.
-------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol B c A)) as H62.
--------------------------------------------- exact H61.
--------------------------------------------- destruct H62 as [H62 H63].
exact H63.
---------------------------------------- assert (* Cut *) (exists (e: euclidean__axioms.Point) (d: euclidean__axioms.Point), (euclidean__defs.SQ B c e d) /\ ((euclidean__axioms.TS d B c A) /\ (euclidean__defs.PG B c e d))) as H56.
----------------------------------------- apply (@proposition__46.proposition__46 (B) (c) (A) (H54) H55).
----------------------------------------- assert (exists e: euclidean__axioms.Point, (exists (d: euclidean__axioms.Point), (euclidean__defs.SQ B c e d) /\ ((euclidean__axioms.TS d B c A) /\ (euclidean__defs.PG B c e d)))) as H57.
------------------------------------------ exact H56.
------------------------------------------ destruct H57 as [e H57].
assert (exists d: euclidean__axioms.Point, ((euclidean__defs.SQ B c e d) /\ ((euclidean__axioms.TS d B c A) /\ (euclidean__defs.PG B c e d)))) as H58.
------------------------------------------- exact H57.
------------------------------------------- destruct H58 as [d H58].
assert (* AndElim *) ((euclidean__defs.SQ B c e d) /\ ((euclidean__axioms.TS d B c A) /\ (euclidean__defs.PG B c e d))) as H59.
-------------------------------------------- exact H58.
-------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.TS d B c A) /\ (euclidean__defs.PG B c e d)) as H61.
--------------------------------------------- exact H60.
--------------------------------------------- destruct H61 as [H61 H62].
assert (* Cut *) (euclidean__axioms.Triangle A B c) as H63.
---------------------------------------------- exact H37.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.TS g B A c) as H64.
----------------------------------------------- apply (@lemma__oppositesideflip.lemma__oppositesideflip (A) (B) (g) (c) H43).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.TS h c A B) as H65.
------------------------------------------------ apply (@lemma__oppositesideflip.lemma__oppositesideflip (A) (c) (h) (B) H52).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS d c B A) as H66.
------------------------------------------------- apply (@lemma__oppositesideflip.lemma__oppositesideflip (B) (c) (d) (A) H61).
------------------------------------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point) (l: euclidean__axioms.Point), (euclidean__defs.PG B m l d) /\ ((euclidean__axioms.BetS B m c) /\ ((euclidean__defs.PG m c e l) /\ ((euclidean__axioms.BetS d l e) /\ ((euclidean__axioms.EF A B f g B m l d) /\ (euclidean__axioms.EF A c k h m c e l)))))) as H67.
-------------------------------------------------- apply (@proposition__47.proposition__47 (A) (B) (c) (d) (e) (f) (g) (h) (k) (H63) (H35) (H41) (H64) (H50) (H65) (H59) H66).
-------------------------------------------------- assert (exists m: euclidean__axioms.Point, (exists (l: euclidean__axioms.Point), (euclidean__defs.PG B m l d) /\ ((euclidean__axioms.BetS B m c) /\ ((euclidean__defs.PG m c e l) /\ ((euclidean__axioms.BetS d l e) /\ ((euclidean__axioms.EF A B f g B m l d) /\ (euclidean__axioms.EF A c k h m c e l))))))) as H68.
--------------------------------------------------- exact H67.
--------------------------------------------------- destruct H68 as [m H68].
assert (exists l: euclidean__axioms.Point, ((euclidean__defs.PG B m l d) /\ ((euclidean__axioms.BetS B m c) /\ ((euclidean__defs.PG m c e l) /\ ((euclidean__axioms.BetS d l e) /\ ((euclidean__axioms.EF A B f g B m l d) /\ (euclidean__axioms.EF A c k h m c e l))))))) as H69.
---------------------------------------------------- exact H68.
---------------------------------------------------- destruct H69 as [l H69].
assert (* AndElim *) ((euclidean__defs.PG B m l d) /\ ((euclidean__axioms.BetS B m c) /\ ((euclidean__defs.PG m c e l) /\ ((euclidean__axioms.BetS d l e) /\ ((euclidean__axioms.EF A B f g B m l d) /\ (euclidean__axioms.EF A c k h m c e l)))))) as H70.
----------------------------------------------------- exact H69.
----------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.BetS B m c) /\ ((euclidean__defs.PG m c e l) /\ ((euclidean__axioms.BetS d l e) /\ ((euclidean__axioms.EF A B f g B m l d) /\ (euclidean__axioms.EF A c k h m c e l))))) as H72.
------------------------------------------------------ exact H71.
------------------------------------------------------ destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__defs.PG m c e l) /\ ((euclidean__axioms.BetS d l e) /\ ((euclidean__axioms.EF A B f g B m l d) /\ (euclidean__axioms.EF A c k h m c e l)))) as H74.
------------------------------------------------------- exact H73.
------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.BetS d l e) /\ ((euclidean__axioms.EF A B f g B m l d) /\ (euclidean__axioms.EF A c k h m c e l))) as H76.
-------------------------------------------------------- exact H75.
-------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.EF A B f g B m l d) /\ (euclidean__axioms.EF A c k h m c e l)) as H78.
--------------------------------------------------------- exact H77.
--------------------------------------------------------- destruct H78 as [H78 H79].
assert (* Cut *) (euclidean__axioms.Cong A C A c) as H80.
---------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (A) (c) (C) H34).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A C K H A c k h) as H81.
----------------------------------------------------------- apply (@lemma__squaresequal.lemma__squaresequal (A) (C) (K) (H) (A) (c) (k) (h) (H80) (H2) H50).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H82.
------------------------------------------------------------ apply (@euclidean__axioms.cn__congruencereflexive (A) B).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF A B F G A B f g) as H83.
------------------------------------------------------------- apply (@lemma__squaresequal.lemma__squaresequal (A) (B) (F) (G) (A) (B) (f) (g) (H82) (H1) H41).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B F G B m l d) as H84.
-------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFtransitive (A) (B) (F) (G) (B) (m) (l) (d) (A) (B) (f) (g) (H83) H78).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B M L D A B F G) as H85.
--------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (A) (B) (F) (G) (B) (M) (L) (D) H6).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B M L D B m l d) as H86.
---------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFtransitive (B) (M) (L) (D) (B) (m) (l) (d) (A) (B) (F) (G) (H85) H84).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF M C E L A C K H) as H87.
----------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (A) (C) (K) (H) (M) (C) (E) (L) H7).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF M C E L A c k h) as H88.
------------------------------------------------------------------ apply (@euclidean__axioms.axiom__EFtransitive (M) (C) (E) (L) (A) (c) (k) (h) (A) (C) (K) (H) (H87) H81).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF M C E L m c e l) as H89.
------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFtransitive (M) (C) (E) (L) (m) (c) (e) (l) (A) (c) (k) (h) (H88) H79).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS e l d) as H90.
-------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (d) (l) (e) H76).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B c e) as H91.
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B c e d) /\ ((euclidean__axioms.Cong B c c e) /\ ((euclidean__axioms.Cong B c d B) /\ ((euclidean__defs.Per d B c) /\ ((euclidean__defs.Per B c e) /\ ((euclidean__defs.Per c e d) /\ (euclidean__defs.Per e d B))))))) as H91.
---------------------------------------------------------------------- exact H59.
---------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Cong B c c e) /\ ((euclidean__axioms.Cong B c d B) /\ ((euclidean__defs.Per d B c) /\ ((euclidean__defs.Per B c e) /\ ((euclidean__defs.Per c e d) /\ (euclidean__defs.Per e d B)))))) as H93.
----------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Cong B c d B) /\ ((euclidean__defs.Per d B c) /\ ((euclidean__defs.Per B c e) /\ ((euclidean__defs.Per c e d) /\ (euclidean__defs.Per e d B))))) as H95.
------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__defs.Per d B c) /\ ((euclidean__defs.Per B c e) /\ ((euclidean__defs.Per c e d) /\ (euclidean__defs.Per e d B)))) as H97.
------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__defs.Per B c e) /\ ((euclidean__defs.Per c e d) /\ (euclidean__defs.Per e d B))) as H99.
-------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__defs.Per c e d) /\ (euclidean__defs.Per e d B)) as H101.
--------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((euclidean__axioms.Cong A c k h) /\ ((euclidean__axioms.Cong A c c k) /\ ((euclidean__axioms.Cong A c h A) /\ ((euclidean__defs.Per h A c) /\ ((euclidean__defs.Per A c k) /\ ((euclidean__defs.Per c k h) /\ (euclidean__defs.Per k h A))))))) as H103.
---------------------------------------------------------------------------- exact H50.
---------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.Cong A c c k) /\ ((euclidean__axioms.Cong A c h A) /\ ((euclidean__defs.Per h A c) /\ ((euclidean__defs.Per A c k) /\ ((euclidean__defs.Per c k h) /\ (euclidean__defs.Per k h A)))))) as H105.
----------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Cong A c h A) /\ ((euclidean__defs.Per h A c) /\ ((euclidean__defs.Per A c k) /\ ((euclidean__defs.Per c k h) /\ (euclidean__defs.Per k h A))))) as H107.
------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------ destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__defs.Per h A c) /\ ((euclidean__defs.Per A c k) /\ ((euclidean__defs.Per c k h) /\ (euclidean__defs.Per k h A)))) as H109.
------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__defs.Per A c k) /\ ((euclidean__defs.Per c k h) /\ (euclidean__defs.Per k h A))) as H111.
-------------------------------------------------------------------------------- exact H110.
-------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__defs.Per c k h) /\ (euclidean__defs.Per k h A)) as H113.
--------------------------------------------------------------------------------- exact H112.
--------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Cong A B f g) /\ ((euclidean__axioms.Cong A B B f) /\ ((euclidean__axioms.Cong A B g A) /\ ((euclidean__defs.Per g A B) /\ ((euclidean__defs.Per A B f) /\ ((euclidean__defs.Per B f g) /\ (euclidean__defs.Per f g A))))))) as H115.
---------------------------------------------------------------------------------- exact H41.
---------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Cong A B B f) /\ ((euclidean__axioms.Cong A B g A) /\ ((euclidean__defs.Per g A B) /\ ((euclidean__defs.Per A B f) /\ ((euclidean__defs.Per B f g) /\ (euclidean__defs.Per f g A)))))) as H117.
----------------------------------------------------------------------------------- exact H116.
----------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Cong A B g A) /\ ((euclidean__defs.Per g A B) /\ ((euclidean__defs.Per A B f) /\ ((euclidean__defs.Per B f g) /\ (euclidean__defs.Per f g A))))) as H119.
------------------------------------------------------------------------------------ exact H118.
------------------------------------------------------------------------------------ destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__defs.Per g A B) /\ ((euclidean__defs.Per A B f) /\ ((euclidean__defs.Per B f g) /\ (euclidean__defs.Per f g A)))) as H121.
------------------------------------------------------------------------------------- exact H120.
------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__defs.Per A B f) /\ ((euclidean__defs.Per B f g) /\ (euclidean__defs.Per f g A))) as H123.
-------------------------------------------------------------------------------------- exact H122.
-------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__defs.Per B f g) /\ (euclidean__defs.Per f g A)) as H125.
--------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Cong B C E D) /\ ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))))) as H127.
---------------------------------------------------------------------------------------- exact H3.
---------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))))) as H129.
----------------------------------------------------------------------------------------- exact H128.
----------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))) as H131.
------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------ destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))) as H133.
------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))) as H135.
-------------------------------------------------------------------------------------------- exact H134.
-------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)) as H137.
--------------------------------------------------------------------------------------------- exact H136.
--------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.Cong A C K H) /\ ((euclidean__axioms.Cong A C C K) /\ ((euclidean__axioms.Cong A C H A) /\ ((euclidean__defs.Per H A C) /\ ((euclidean__defs.Per A C K) /\ ((euclidean__defs.Per C K H) /\ (euclidean__defs.Per K H A))))))) as H139.
---------------------------------------------------------------------------------------------- exact H2.
---------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.Cong A C C K) /\ ((euclidean__axioms.Cong A C H A) /\ ((euclidean__defs.Per H A C) /\ ((euclidean__defs.Per A C K) /\ ((euclidean__defs.Per C K H) /\ (euclidean__defs.Per K H A)))))) as H141.
----------------------------------------------------------------------------------------------- exact H140.
----------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Cong A C H A) /\ ((euclidean__defs.Per H A C) /\ ((euclidean__defs.Per A C K) /\ ((euclidean__defs.Per C K H) /\ (euclidean__defs.Per K H A))))) as H143.
------------------------------------------------------------------------------------------------ exact H142.
------------------------------------------------------------------------------------------------ destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__defs.Per H A C) /\ ((euclidean__defs.Per A C K) /\ ((euclidean__defs.Per C K H) /\ (euclidean__defs.Per K H A)))) as H145.
------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__defs.Per A C K) /\ ((euclidean__defs.Per C K H) /\ (euclidean__defs.Per K H A))) as H147.
-------------------------------------------------------------------------------------------------- exact H146.
-------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__defs.Per C K H) /\ (euclidean__defs.Per K H A)) as H149.
--------------------------------------------------------------------------------------------------- exact H148.
--------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.Cong A B F G) /\ ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))))) as H151.
---------------------------------------------------------------------------------------------------- exact H1.
---------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.Cong A B B F) /\ ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))))) as H153.
----------------------------------------------------------------------------------------------------- exact H152.
----------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((euclidean__axioms.Cong A B G A) /\ ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))))) as H155.
------------------------------------------------------------------------------------------------------ exact H154.
------------------------------------------------------------------------------------------------------ destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__defs.Per G A B) /\ ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)))) as H157.
------------------------------------------------------------------------------------------------------- exact H156.
------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__defs.Per A B F) /\ ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A))) as H159.
-------------------------------------------------------------------------------------------------------- exact H158.
-------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__defs.Per B F G) /\ (euclidean__defs.Per F G A)) as H161.
--------------------------------------------------------------------------------------------------------- exact H160.
--------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
exact H99.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq m c) as H92.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq B m) /\ (euclidean__axioms.neq B c))) as H92.
----------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (m) (c) H72).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq B m) /\ (euclidean__axioms.neq B c))) as H93.
------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------ destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq B m) /\ (euclidean__axioms.neq B c)) as H95.
------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------- destruct H95 as [H95 H96].
exact H93.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B m c) as H93.
----------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H72.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B c m) as H94.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col m B c) /\ ((euclidean__axioms.Col m c B) /\ ((euclidean__axioms.Col c B m) /\ ((euclidean__axioms.Col B c m) /\ (euclidean__axioms.Col c m B))))) as H94.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (m) (c) H93).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m B c) /\ ((euclidean__axioms.Col m c B) /\ ((euclidean__axioms.Col c B m) /\ ((euclidean__axioms.Col B c m) /\ (euclidean__axioms.Col c m B))))) as H95.
-------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col m c B) /\ ((euclidean__axioms.Col c B m) /\ ((euclidean__axioms.Col B c m) /\ (euclidean__axioms.Col c m B)))) as H97.
--------------------------------------------------------------------------- exact H96.
--------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col c B m) /\ ((euclidean__axioms.Col B c m) /\ (euclidean__axioms.Col c m B))) as H99.
---------------------------------------------------------------------------- exact H98.
---------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.Col B c m) /\ (euclidean__axioms.Col c m B)) as H101.
----------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------- destruct H101 as [H101 H102].
exact H101.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Per m c e) as H95.
------------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (B) (c) (m) (e) (H91) (H94) H92).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG c e l m) as H96.
-------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate (m) (c) (e) (l) H74).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.RE c e l m) as H97.
--------------------------------------------------------------------------- apply (@lemma__PGrectangle.lemma__PGrectangle (c) (m) (e) (l) (H96) H95).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.RE e l m c) as H98.
---------------------------------------------------------------------------- apply (@lemma__rectanglerotate.lemma__rectanglerotate (c) (e) (l) (m) H97).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.RE l m c e) as H99.
----------------------------------------------------------------------------- apply (@lemma__rectanglerotate.lemma__rectanglerotate (e) (l) (m) (c) H98).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.RE m c e l) as H100.
------------------------------------------------------------------------------ apply (@lemma__rectanglerotate.lemma__rectanglerotate (l) (m) (c) (e) H99).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF B C E D B c e d) as H101.
------------------------------------------------------------------------------- apply (@lemma__paste5.lemma__paste5 (B) (C) (D) (E) (L) (M) (B) (c) (d) (e) (l) (m) (H86) (H89) (H4) (H72) (H5) (H90) (H8) H100).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C B c) as H102.
-------------------------------------------------------------------------------- apply (@proposition__48A.proposition__48A (B) (C) (E) (D) (B) (c) (e) (d) (H3) (H59) H101).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C A c) as H103.
--------------------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle A B c) as H104.
---------------------------------------------------------------------------------- exact H63.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B A C B A c) as H105.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.Triangle A B c) -> ((euclidean__axioms.Cong A B A B) -> ((euclidean__axioms.Cong A C A c) -> ((euclidean__axioms.Cong B C B c) -> (euclidean__defs.CongA B A C B A c)))))) as H105.
------------------------------------------------------------------------------------ intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.CongA B A C B A c) /\ ((euclidean__defs.CongA C B A c B A) /\ (euclidean__defs.CongA A C B A c B))) as __4.
------------------------------------------------------------------------------------- apply (@proposition__08.proposition__08 (A) (B) (C) (A) (B) (c) (__) (__0) (__1) (__2) __3).
------------------------------------------------------------------------------------- destruct __4 as [__4 __5].
exact __4.
------------------------------------------------------------------------------------ apply (@H105 (H0) (H104) (H82) (H103) H102).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B A C) as H106.
------------------------------------------------------------------------------------ apply (@lemma__equaltorightisright.lemma__equaltorightisright (B) (A) (c) (B) (A) (C) (H35) H105).
------------------------------------------------------------------------------------ exact H106.
Qed.
