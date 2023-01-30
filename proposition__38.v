Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__PGrotate.
Require Export lemma__collinear5.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel2.
Require Export lemma__congruenceflip.
Require Export lemma__diagonalsmeet.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__triangletoparallelogram.
Require Export logic.
Require Export proposition__34.
Require Export proposition__36.
Definition proposition__38 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point), (euclidean__defs.Par P Q B C) -> ((euclidean__axioms.Col P Q A) -> ((euclidean__axioms.Col P Q D) -> ((euclidean__axioms.Cong B C E F) -> ((euclidean__axioms.Col B C E) -> ((euclidean__axioms.Col B C F) -> (euclidean__axioms.ET A B C D E F)))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro P.
intro Q.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
assert (* Cut *) (euclidean__defs.Par B C P Q) as H5.
- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (P) (Q) (B) (C) H).
- assert (* Cut *) (euclidean__defs.Par C B P Q) as H6.
-- assert (* Cut *) ((euclidean__defs.Par C B P Q) /\ ((euclidean__defs.Par B C Q P) /\ (euclidean__defs.Par C B Q P))) as H6.
--- apply (@lemma__parallelflip.lemma__parallelflip (B) (C) (P) (Q) H5).
--- assert (* AndElim *) ((euclidean__defs.Par C B P Q) /\ ((euclidean__defs.Par B C Q P) /\ (euclidean__defs.Par C B Q P))) as H7.
---- exact H6.
---- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Par B C Q P) /\ (euclidean__defs.Par C B Q P)) as H9.
----- exact H8.
----- destruct H9 as [H9 H10].
exact H7.
-- assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__defs.PG A G B C) /\ (euclidean__axioms.Col P Q G)) as H7.
--- apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram (A) (B) (C) (P) (Q) (H6) H0).
--- assert (exists G: euclidean__axioms.Point, ((euclidean__defs.PG A G B C) /\ (euclidean__axioms.Col P Q G))) as H8.
---- exact H7.
---- destruct H8 as [G H8].
assert (* AndElim *) ((euclidean__defs.PG A G B C) /\ (euclidean__axioms.Col P Q G)) as H9.
----- exact H8.
----- destruct H9 as [H9 H10].
assert (* Cut *) (euclidean__defs.PG G B C A) as H11.
------ apply (@lemma__PGrotate.lemma__PGrotate (A) (G) (B) (C) H9).
------ assert (* Cut *) (euclidean__axioms.nCol P B C) as H12.
------- assert (* Cut *) ((euclidean__axioms.nCol P Q B) /\ ((euclidean__axioms.nCol P B C) /\ ((euclidean__axioms.nCol Q B C) /\ (euclidean__axioms.nCol P Q C)))) as H12.
-------- apply (@lemma__parallelNC.lemma__parallelNC (P) (Q) (B) (C) H).
-------- assert (* AndElim *) ((euclidean__axioms.nCol P Q B) /\ ((euclidean__axioms.nCol P B C) /\ ((euclidean__axioms.nCol Q B C) /\ (euclidean__axioms.nCol P Q C)))) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.nCol P B C) /\ ((euclidean__axioms.nCol Q B C) /\ (euclidean__axioms.nCol P Q C))) as H15.
---------- exact H14.
---------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.nCol Q B C) /\ (euclidean__axioms.nCol P Q C)) as H17.
----------- exact H16.
----------- destruct H17 as [H17 H18].
exact H15.
------- assert (* Cut *) (euclidean__axioms.neq B C) as H13.
-------- assert (* Cut *) ((euclidean__axioms.neq P B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq P C) /\ ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C P)))))) as H13.
--------- apply (@lemma__NCdistinct.lemma__NCdistinct (P) (B) (C) H12).
--------- assert (* AndElim *) ((euclidean__axioms.neq P B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq P C) /\ ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C P)))))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq P C) /\ ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C P))))) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq P C) /\ ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C P)))) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C P))) as H20.
------------- exact H19.
------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C P)) as H22.
-------------- exact H21.
-------------- destruct H22 as [H22 H23].
exact H16.
-------- assert (* Cut *) (euclidean__axioms.neq E F) as H14.
--------- apply (@euclidean__axioms.axiom__nocollapse (B) (C) (E) (F) (H13) H2).
--------- assert (* Cut *) (euclidean__defs.Par P Q E F) as H15.
---------- apply (@lemma__collinearparallel2.lemma__collinearparallel2 (P) (Q) (B) (C) (E) (F) (H) (H3) (H4) H14).
---------- assert (* Cut *) (euclidean__defs.Par E F P Q) as H16.
----------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (P) (Q) (E) (F) H15).
----------- assert (* Cut *) (exists (H17: euclidean__axioms.Point), (euclidean__defs.PG D H17 F E) /\ (euclidean__axioms.Col P Q H17)) as H17.
------------ apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram (D) (F) (E) (P) (Q) (H16) H1).
------------ assert (exists H18: euclidean__axioms.Point, ((euclidean__defs.PG D H18 F E) /\ (euclidean__axioms.Col P Q H18))) as H19.
------------- exact H17.
------------- destruct H19 as [H18 H19].
assert (* AndElim *) ((euclidean__defs.PG D H18 F E) /\ (euclidean__axioms.Col P Q H18)) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* Cut *) (euclidean__defs.PG H18 F E D) as H22.
--------------- apply (@lemma__PGrotate.lemma__PGrotate (D) (H18) (F) (E) H20).
--------------- assert (* Cut *) (euclidean__axioms.Cong B C F E) as H23.
---------------- assert (* Cut *) ((euclidean__axioms.Cong C B F E) /\ ((euclidean__axioms.Cong C B E F) /\ (euclidean__axioms.Cong B C F E))) as H23.
----------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (C) (E) (F) H2).
----------------- assert (* AndElim *) ((euclidean__axioms.Cong C B F E) /\ ((euclidean__axioms.Cong C B E F) /\ (euclidean__axioms.Cong B C F E))) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Cong C B E F) /\ (euclidean__axioms.Cong B C F E)) as H26.
------------------- exact H25.
------------------- destruct H26 as [H26 H27].
exact H27.
---------------- assert (* Cut *) (euclidean__axioms.nCol P Q B) as H24.
----------------- assert (* Cut *) ((euclidean__axioms.nCol P Q B) /\ ((euclidean__axioms.nCol P B C) /\ ((euclidean__axioms.nCol Q B C) /\ (euclidean__axioms.nCol P Q C)))) as H24.
------------------ apply (@lemma__parallelNC.lemma__parallelNC (P) (Q) (B) (C) H).
------------------ assert (* AndElim *) ((euclidean__axioms.nCol P Q B) /\ ((euclidean__axioms.nCol P B C) /\ ((euclidean__axioms.nCol Q B C) /\ (euclidean__axioms.nCol P Q C)))) as H25.
------------------- exact H24.
------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.nCol P B C) /\ ((euclidean__axioms.nCol Q B C) /\ (euclidean__axioms.nCol P Q C))) as H27.
-------------------- exact H26.
-------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.nCol Q B C) /\ (euclidean__axioms.nCol P Q C)) as H29.
--------------------- exact H28.
--------------------- destruct H29 as [H29 H30].
exact H25.
----------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H25.
------------------ assert (* Cut *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q B) /\ ((euclidean__axioms.neq P B) /\ ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B P)))))) as H25.
------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (P) (Q) (B) H24).
------------------- assert (* AndElim *) ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq Q B) /\ ((euclidean__axioms.neq P B) /\ ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B P)))))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq Q B) /\ ((euclidean__axioms.neq P B) /\ ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B P))))) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq P B) /\ ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B P)))) as H30.
---------------------- exact H29.
---------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq Q P) /\ ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B P))) as H32.
----------------------- exact H31.
----------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq B Q) /\ (euclidean__axioms.neq B P)) as H34.
------------------------ exact H33.
------------------------ destruct H34 as [H34 H35].
exact H26.
------------------ assert (* Cut *) (euclidean__axioms.Col G A H18) as H26.
------------------- apply (@euclidean__tactics.not__nCol__Col (G) (A) (H18)).
--------------------intro H26.
apply (@euclidean__tactics.Col__nCol__False (G) (A) (H18) (H26)).
---------------------apply (@lemma__collinear5.lemma__collinear5 (P) (Q) (G) (A) (H18) (H25) (H10) (H0) H21).


------------------- assert (* Cut *) (euclidean__axioms.Col G A D) as H27.
-------------------- apply (@euclidean__tactics.not__nCol__Col (G) (A) (D)).
---------------------intro H27.
apply (@euclidean__tactics.Col__nCol__False (G) (A) (D) (H27)).
----------------------apply (@lemma__collinear5.lemma__collinear5 (P) (Q) (G) (A) (D) (H25) (H10) (H0) H1).


-------------------- assert (* Cut *) (euclidean__axioms.EF G B C A H18 F E D) as H28.
--------------------- apply (@proposition__36.proposition__36 (G) (B) (C) (A) (H18) (F) (E) (D) (H11) (H22) (H26) (H27) (H4) (H3) H23).
--------------------- assert (* Cut *) (euclidean__axioms.EF G B C A E F H18 D) as H29.
---------------------- assert (* Cut *) ((euclidean__axioms.EF G B C A F E D H18) /\ ((euclidean__axioms.EF G B C A D E F H18) /\ ((euclidean__axioms.EF G B C A E D H18 F) /\ ((euclidean__axioms.EF G B C A F H18 D E) /\ ((euclidean__axioms.EF G B C A D H18 F E) /\ ((euclidean__axioms.EF G B C A E F H18 D) /\ (euclidean__axioms.EF G B C A H18 D E F))))))) as H29.
----------------------- apply (@euclidean__axioms.axiom__EFpermutation (G) (B) (C) (A) (H18) (F) (E) (D) H28).
----------------------- assert (* AndElim *) ((euclidean__axioms.EF G B C A F E D H18) /\ ((euclidean__axioms.EF G B C A D E F H18) /\ ((euclidean__axioms.EF G B C A E D H18 F) /\ ((euclidean__axioms.EF G B C A F H18 D E) /\ ((euclidean__axioms.EF G B C A D H18 F E) /\ ((euclidean__axioms.EF G B C A E F H18 D) /\ (euclidean__axioms.EF G B C A H18 D E F))))))) as H30.
------------------------ exact H29.
------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.EF G B C A D E F H18) /\ ((euclidean__axioms.EF G B C A E D H18 F) /\ ((euclidean__axioms.EF G B C A F H18 D E) /\ ((euclidean__axioms.EF G B C A D H18 F E) /\ ((euclidean__axioms.EF G B C A E F H18 D) /\ (euclidean__axioms.EF G B C A H18 D E F)))))) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.EF G B C A E D H18 F) /\ ((euclidean__axioms.EF G B C A F H18 D E) /\ ((euclidean__axioms.EF G B C A D H18 F E) /\ ((euclidean__axioms.EF G B C A E F H18 D) /\ (euclidean__axioms.EF G B C A H18 D E F))))) as H34.
-------------------------- exact H33.
-------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.EF G B C A F H18 D E) /\ ((euclidean__axioms.EF G B C A D H18 F E) /\ ((euclidean__axioms.EF G B C A E F H18 D) /\ (euclidean__axioms.EF G B C A H18 D E F)))) as H36.
--------------------------- exact H35.
--------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.EF G B C A D H18 F E) /\ ((euclidean__axioms.EF G B C A E F H18 D) /\ (euclidean__axioms.EF G B C A H18 D E F))) as H38.
---------------------------- exact H37.
---------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.EF G B C A E F H18 D) /\ (euclidean__axioms.EF G B C A H18 D E F)) as H40.
----------------------------- exact H39.
----------------------------- destruct H40 as [H40 H41].
exact H40.
---------------------- assert (* Cut *) (euclidean__axioms.EF E F H18 D G B C A) as H30.
----------------------- apply (@euclidean__axioms.axiom__EFsymmetric (G) (B) (C) (A) (E) (F) (H18) (D) H29).
----------------------- assert (* Cut *) (euclidean__axioms.EF E F H18 D C B G A) as H31.
------------------------ assert (* Cut *) ((euclidean__axioms.EF E F H18 D B C A G) /\ ((euclidean__axioms.EF E F H18 D A C B G) /\ ((euclidean__axioms.EF E F H18 D C A G B) /\ ((euclidean__axioms.EF E F H18 D B G A C) /\ ((euclidean__axioms.EF E F H18 D A G B C) /\ ((euclidean__axioms.EF E F H18 D C B G A) /\ (euclidean__axioms.EF E F H18 D G A C B))))))) as H31.
------------------------- apply (@euclidean__axioms.axiom__EFpermutation (E) (F) (H18) (D) (G) (B) (C) (A) H30).
------------------------- assert (* AndElim *) ((euclidean__axioms.EF E F H18 D B C A G) /\ ((euclidean__axioms.EF E F H18 D A C B G) /\ ((euclidean__axioms.EF E F H18 D C A G B) /\ ((euclidean__axioms.EF E F H18 D B G A C) /\ ((euclidean__axioms.EF E F H18 D A G B C) /\ ((euclidean__axioms.EF E F H18 D C B G A) /\ (euclidean__axioms.EF E F H18 D G A C B))))))) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.EF E F H18 D A C B G) /\ ((euclidean__axioms.EF E F H18 D C A G B) /\ ((euclidean__axioms.EF E F H18 D B G A C) /\ ((euclidean__axioms.EF E F H18 D A G B C) /\ ((euclidean__axioms.EF E F H18 D C B G A) /\ (euclidean__axioms.EF E F H18 D G A C B)))))) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.EF E F H18 D C A G B) /\ ((euclidean__axioms.EF E F H18 D B G A C) /\ ((euclidean__axioms.EF E F H18 D A G B C) /\ ((euclidean__axioms.EF E F H18 D C B G A) /\ (euclidean__axioms.EF E F H18 D G A C B))))) as H36.
---------------------------- exact H35.
---------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.EF E F H18 D B G A C) /\ ((euclidean__axioms.EF E F H18 D A G B C) /\ ((euclidean__axioms.EF E F H18 D C B G A) /\ (euclidean__axioms.EF E F H18 D G A C B)))) as H38.
----------------------------- exact H37.
----------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.EF E F H18 D A G B C) /\ ((euclidean__axioms.EF E F H18 D C B G A) /\ (euclidean__axioms.EF E F H18 D G A C B))) as H40.
------------------------------ exact H39.
------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.EF E F H18 D C B G A) /\ (euclidean__axioms.EF E F H18 D G A C B)) as H42.
------------------------------- exact H41.
------------------------------- destruct H42 as [H42 H43].
exact H42.
------------------------ assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS D M F) /\ (euclidean__axioms.BetS H18 M E)) as H32.
------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (D) (H18) (F) (E) H20).
------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS D M F) /\ (euclidean__axioms.BetS H18 M E))) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [M H33].
assert (* AndElim *) ((euclidean__axioms.BetS D M F) /\ (euclidean__axioms.BetS H18 M E)) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [H34 H35].
assert (* Cut *) (euclidean__axioms.Col D M F) as H36.
---------------------------- right.
right.
right.
right.
left.
exact H34.
---------------------------- assert (* Cut *) (euclidean__axioms.Col F D M) as H37.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col M D F) /\ ((euclidean__axioms.Col M F D) /\ ((euclidean__axioms.Col F D M) /\ ((euclidean__axioms.Col D F M) /\ (euclidean__axioms.Col F M D))))) as H37.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (D) (M) (F) H36).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col M D F) /\ ((euclidean__axioms.Col M F D) /\ ((euclidean__axioms.Col F D M) /\ ((euclidean__axioms.Col D F M) /\ (euclidean__axioms.Col F M D))))) as H38.
------------------------------- exact H37.
------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col M F D) /\ ((euclidean__axioms.Col F D M) /\ ((euclidean__axioms.Col D F M) /\ (euclidean__axioms.Col F M D)))) as H40.
-------------------------------- exact H39.
-------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col F D M) /\ ((euclidean__axioms.Col D F M) /\ (euclidean__axioms.Col F M D))) as H42.
--------------------------------- exact H41.
--------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col D F M) /\ (euclidean__axioms.Col F M D)) as H44.
---------------------------------- exact H43.
---------------------------------- destruct H44 as [H44 H45].
exact H42.
----------------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS A m B) /\ (euclidean__axioms.BetS G m C)) as H38.
------------------------------ apply (@lemma__diagonalsmeet.lemma__diagonalsmeet (A) (G) (B) (C) H9).
------------------------------ assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS A m B) /\ (euclidean__axioms.BetS G m C))) as H39.
------------------------------- exact H38.
------------------------------- destruct H39 as [m H39].
assert (* AndElim *) ((euclidean__axioms.BetS A m B) /\ (euclidean__axioms.BetS G m C)) as H40.
-------------------------------- exact H39.
-------------------------------- destruct H40 as [H40 H41].
assert (* Cut *) (euclidean__axioms.Col A m B) as H42.
--------------------------------- right.
right.
right.
right.
left.
exact H40.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col B A m) as H43.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H43.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (m) (B) H42).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H44.
------------------------------------ exact H43.
------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A)))) as H46.
------------------------------------- exact H45.
------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))) as H48.
-------------------------------------- exact H47.
-------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A)) as H50.
--------------------------------------- exact H49.
--------------------------------------- destruct H50 as [H50 H51].
exact H48.
---------------------------------- assert (* Cut *) (euclidean__defs.Par A G B C) as H44.
----------------------------------- assert (* AndElim *) ((euclidean__defs.Par H18 F E D) /\ (euclidean__defs.Par H18 D F E)) as H44.
------------------------------------ exact H22.
------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.Par D H18 F E) /\ (euclidean__defs.Par D E H18 F)) as H46.
------------------------------------- exact H20.
------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.Par G B C A) /\ (euclidean__defs.Par G A B C)) as H48.
-------------------------------------- exact H11.
-------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Par A G B C) /\ (euclidean__defs.Par A C G B)) as H50.
--------------------------------------- exact H9.
--------------------------------------- destruct H50 as [H50 H51].
exact H50.
----------------------------------- assert (* Cut *) (euclidean__axioms.nCol A G B) as H45.
------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol A G B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol G B C) /\ (euclidean__axioms.nCol A G C)))) as H45.
------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (G) (B) (C) H44).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A G B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol G B C) /\ (euclidean__axioms.nCol A G C)))) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol G B C) /\ (euclidean__axioms.nCol A G C))) as H48.
--------------------------------------- exact H47.
--------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.nCol G B C) /\ (euclidean__axioms.nCol A G C)) as H50.
---------------------------------------- exact H49.
---------------------------------------- destruct H50 as [H50 H51].
exact H46.
------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B A G) as H46.
------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G A B) /\ ((euclidean__axioms.nCol G B A) /\ ((euclidean__axioms.nCol B A G) /\ ((euclidean__axioms.nCol A B G) /\ (euclidean__axioms.nCol B G A))))) as H46.
-------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (G) (B) H45).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol G A B) /\ ((euclidean__axioms.nCol G B A) /\ ((euclidean__axioms.nCol B A G) /\ ((euclidean__axioms.nCol A B G) /\ (euclidean__axioms.nCol B G A))))) as H47.
--------------------------------------- exact H46.
--------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.nCol G B A) /\ ((euclidean__axioms.nCol B A G) /\ ((euclidean__axioms.nCol A B G) /\ (euclidean__axioms.nCol B G A)))) as H49.
---------------------------------------- exact H48.
---------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol B A G) /\ ((euclidean__axioms.nCol A B G) /\ (euclidean__axioms.nCol B G A))) as H51.
----------------------------------------- exact H50.
----------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol A B G) /\ (euclidean__axioms.nCol B G A)) as H53.
------------------------------------------ exact H52.
------------------------------------------ destruct H53 as [H53 H54].
exact H51.
------------------------------------- assert (* Cut *) (euclidean__defs.Par D H18 F E) as H47.
-------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H18 F E D) /\ (euclidean__defs.Par H18 D F E)) as H47.
--------------------------------------- exact H22.
--------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.Par D H18 F E) /\ (euclidean__defs.Par D E H18 F)) as H49.
---------------------------------------- exact H20.
---------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__defs.Par G B C A) /\ (euclidean__defs.Par G A B C)) as H51.
----------------------------------------- exact H11.
----------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__defs.Par A G B C) /\ (euclidean__defs.Par A C G B)) as H53.
------------------------------------------ exact H9.
------------------------------------------ destruct H53 as [H53 H54].
exact H49.
-------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D H18 F) as H48.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D H18 F) /\ ((euclidean__axioms.nCol D F E) /\ ((euclidean__axioms.nCol H18 F E) /\ (euclidean__axioms.nCol D H18 E)))) as H48.
---------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (D) (H18) (F) (E) H47).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol D H18 F) /\ ((euclidean__axioms.nCol D F E) /\ ((euclidean__axioms.nCol H18 F E) /\ (euclidean__axioms.nCol D H18 E)))) as H49.
----------------------------------------- exact H48.
----------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol D F E) /\ ((euclidean__axioms.nCol H18 F E) /\ (euclidean__axioms.nCol D H18 E))) as H51.
------------------------------------------ exact H50.
------------------------------------------ destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol H18 F E) /\ (euclidean__axioms.nCol D H18 E)) as H53.
------------------------------------------- exact H52.
------------------------------------------- destruct H53 as [H53 H54].
exact H49.
--------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F D H18) as H49.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H18 D F) /\ ((euclidean__axioms.nCol H18 F D) /\ ((euclidean__axioms.nCol F D H18) /\ ((euclidean__axioms.nCol D F H18) /\ (euclidean__axioms.nCol F H18 D))))) as H49.
----------------------------------------- apply (@lemma__NCorder.lemma__NCorder (D) (H18) (F) H48).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol H18 D F) /\ ((euclidean__axioms.nCol H18 F D) /\ ((euclidean__axioms.nCol F D H18) /\ ((euclidean__axioms.nCol D F H18) /\ (euclidean__axioms.nCol F H18 D))))) as H50.
------------------------------------------ exact H49.
------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.nCol H18 F D) /\ ((euclidean__axioms.nCol F D H18) /\ ((euclidean__axioms.nCol D F H18) /\ (euclidean__axioms.nCol F H18 D)))) as H52.
------------------------------------------- exact H51.
------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.nCol F D H18) /\ ((euclidean__axioms.nCol D F H18) /\ (euclidean__axioms.nCol F H18 D))) as H54.
-------------------------------------------- exact H53.
-------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.nCol D F H18) /\ (euclidean__axioms.nCol F H18 D)) as H56.
--------------------------------------------- exact H55.
--------------------------------------------- destruct H56 as [H56 H57].
exact H54.
---------------------------------------- assert (* Cut *) (euclidean__axioms.TS G B A C) as H50.
----------------------------------------- exists m.
split.
------------------------------------------ exact H41.
------------------------------------------ split.
------------------------------------------- exact H43.
------------------------------------------- exact H46.
----------------------------------------- assert (* Cut *) (euclidean__axioms.TS C B A G) as H51.
------------------------------------------ apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (B) (A) (G) (C) H50).
------------------------------------------ assert (* Cut *) (euclidean__axioms.TS H18 F D E) as H52.
------------------------------------------- exists M.
split.
-------------------------------------------- exact H35.
-------------------------------------------- split.
--------------------------------------------- exact H37.
--------------------------------------------- exact H49.
------------------------------------------- assert (* Cut *) (euclidean__axioms.TS E F D H18) as H53.
-------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (F) (D) (H18) (E) H52).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 F H18 D D E F) as H54.
--------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H54.
---------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
----------------------------------------------- apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
----------------------------------------------- destruct __0 as [__0 __1].
exact __1.
---------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H55.
----------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
------------------------------------------------ apply (@H54 (A0) (B0) (C0) (D0) __).
------------------------------------------------ destruct __0 as [__0 __1].
exact __1.
----------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H56.
------------------------------------------------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
------------------------------------------------- apply (@H55 (A0) (B0) (C0) (D0) __).
------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------ assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H57.
------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
-------------------------------------------------- apply (@H56 (A0) (B0) (C0) (D0) __).
-------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------- apply (@H57 (H18) (D) (F) (E) H22).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F H18 D D E F) as H55.
---------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal (F) (H18) (D) (D) (E) (F) H54).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F H18 D E F D) as H56.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F H18 D E F D) /\ ((euclidean__axioms.ET F H18 D D F E) /\ ((euclidean__axioms.ET F H18 D E D F) /\ ((euclidean__axioms.ET F H18 D F E D) /\ (euclidean__axioms.ET F H18 D F D E))))) as H56.
------------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation (F) (H18) (D) (D) (E) (F) H55).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.ET F H18 D E F D) /\ ((euclidean__axioms.ET F H18 D D F E) /\ ((euclidean__axioms.ET F H18 D E D F) /\ ((euclidean__axioms.ET F H18 D F E D) /\ (euclidean__axioms.ET F H18 D F D E))))) as H57.
------------------------------------------------- exact H56.
------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.ET F H18 D D F E) /\ ((euclidean__axioms.ET F H18 D E D F) /\ ((euclidean__axioms.ET F H18 D F E D) /\ (euclidean__axioms.ET F H18 D F D E)))) as H59.
-------------------------------------------------- exact H58.
-------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.ET F H18 D E D F) /\ ((euclidean__axioms.ET F H18 D F E D) /\ (euclidean__axioms.ET F H18 D F D E))) as H61.
--------------------------------------------------- exact H60.
--------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.ET F H18 D F E D) /\ (euclidean__axioms.ET F H18 D F D E)) as H63.
---------------------------------------------------- exact H62.
---------------------------------------------------- destruct H63 as [H63 H64].
exact H57.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.ET E F D F H18 D) as H57.
------------------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric (F) (H18) (D) (E) (F) (D) H56).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET E F D F D H18) as H58.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET E F D H18 D F) /\ ((euclidean__axioms.ET E F D F D H18) /\ ((euclidean__axioms.ET E F D H18 F D) /\ ((euclidean__axioms.ET E F D D H18 F) /\ (euclidean__axioms.ET E F D D F H18))))) as H58.
-------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (E) (F) (D) (F) (H18) (D) H57).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET E F D H18 D F) /\ ((euclidean__axioms.ET E F D F D H18) /\ ((euclidean__axioms.ET E F D H18 F D) /\ ((euclidean__axioms.ET E F D D H18 F) /\ (euclidean__axioms.ET E F D D F H18))))) as H59.
--------------------------------------------------- exact H58.
--------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.ET E F D F D H18) /\ ((euclidean__axioms.ET E F D H18 F D) /\ ((euclidean__axioms.ET E F D D H18 F) /\ (euclidean__axioms.ET E F D D F H18)))) as H61.
---------------------------------------------------- exact H60.
---------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.ET E F D H18 F D) /\ ((euclidean__axioms.ET E F D D H18 F) /\ (euclidean__axioms.ET E F D D F H18))) as H63.
----------------------------------------------------- exact H62.
----------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.ET E F D D H18 F) /\ (euclidean__axioms.ET E F D D F H18)) as H65.
------------------------------------------------------ exact H64.
------------------------------------------------------ destruct H65 as [H65 H66].
exact H61.
------------------------------------------------- assert (* Cut *) (euclidean__defs.PG G B C A) as H59.
-------------------------------------------------- exact H11.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 B G A A C B) as H60.
--------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H60.
---------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
----------------------------------------------------- apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
----------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
---------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H61.
----------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
------------------------------------------------------ apply (@H60 (A0) (B0) (C0) (D0) __).
------------------------------------------------------ destruct __0 as [__0 __1].
exact __1.
----------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H62.
------------------------------------------------------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
------------------------------------------------------- apply (@H61 (A0) (B0) (C0) (D0) __).
------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------------ assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H63.
------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
-------------------------------------------------------- apply (@H62 (A0) (B0) (C0) (D0) __).
-------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------------- apply (@H63 (G) (A) (B) (C) H59).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET B G A A C B) as H61.
---------------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal (B) (G) (A) (A) (C) (B) H60).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET B G A C B A) as H62.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET B G A C B A) /\ ((euclidean__axioms.ET B G A A B C) /\ ((euclidean__axioms.ET B G A C A B) /\ ((euclidean__axioms.ET B G A B C A) /\ (euclidean__axioms.ET B G A B A C))))) as H62.
------------------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation (B) (G) (A) (A) (C) (B) H61).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.ET B G A C B A) /\ ((euclidean__axioms.ET B G A A B C) /\ ((euclidean__axioms.ET B G A C A B) /\ ((euclidean__axioms.ET B G A B C A) /\ (euclidean__axioms.ET B G A B A C))))) as H63.
------------------------------------------------------- exact H62.
------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.ET B G A A B C) /\ ((euclidean__axioms.ET B G A C A B) /\ ((euclidean__axioms.ET B G A B C A) /\ (euclidean__axioms.ET B G A B A C)))) as H65.
-------------------------------------------------------- exact H64.
-------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.ET B G A C A B) /\ ((euclidean__axioms.ET B G A B C A) /\ (euclidean__axioms.ET B G A B A C))) as H67.
--------------------------------------------------------- exact H66.
--------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.ET B G A B C A) /\ (euclidean__axioms.ET B G A B A C)) as H69.
---------------------------------------------------------- exact H68.
---------------------------------------------------------- destruct H69 as [H69 H70].
exact H63.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET C B A B G A) as H63.
------------------------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric (B) (G) (A) (C) (B) (A) H62).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET C B A B A G) as H64.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET C B A G A B) /\ ((euclidean__axioms.ET C B A B A G) /\ ((euclidean__axioms.ET C B A G B A) /\ ((euclidean__axioms.ET C B A A G B) /\ (euclidean__axioms.ET C B A A B G))))) as H64.
-------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (C) (B) (A) (B) (G) (A) H63).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET C B A G A B) /\ ((euclidean__axioms.ET C B A B A G) /\ ((euclidean__axioms.ET C B A G B A) /\ ((euclidean__axioms.ET C B A A G B) /\ (euclidean__axioms.ET C B A A B G))))) as H65.
--------------------------------------------------------- exact H64.
--------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.ET C B A B A G) /\ ((euclidean__axioms.ET C B A G B A) /\ ((euclidean__axioms.ET C B A A G B) /\ (euclidean__axioms.ET C B A A B G)))) as H67.
---------------------------------------------------------- exact H66.
---------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.ET C B A G B A) /\ ((euclidean__axioms.ET C B A A G B) /\ (euclidean__axioms.ET C B A A B G))) as H69.
----------------------------------------------------------- exact H68.
----------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.ET C B A A G B) /\ (euclidean__axioms.ET C B A A B G)) as H71.
------------------------------------------------------------ exact H70.
------------------------------------------------------------ destruct H71 as [H71 H72].
exact H67.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET E F D C B A) as H65.
-------------------------------------------------------- apply (@euclidean__axioms.axiom__halvesofequals (E) (F) (D) (H18) (C) (B) (A) (G) (H58) (H53) (H64) (H51) H31).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET E F D A B C) as H66.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET E F D B A C) /\ ((euclidean__axioms.ET E F D C A B) /\ ((euclidean__axioms.ET E F D B C A) /\ ((euclidean__axioms.ET E F D A B C) /\ (euclidean__axioms.ET E F D A C B))))) as H66.
---------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation (E) (F) (D) (C) (B) (A) H65).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.ET E F D B A C) /\ ((euclidean__axioms.ET E F D C A B) /\ ((euclidean__axioms.ET E F D B C A) /\ ((euclidean__axioms.ET E F D A B C) /\ (euclidean__axioms.ET E F D A C B))))) as H67.
----------------------------------------------------------- exact H66.
----------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.ET E F D C A B) /\ ((euclidean__axioms.ET E F D B C A) /\ ((euclidean__axioms.ET E F D A B C) /\ (euclidean__axioms.ET E F D A C B)))) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.ET E F D B C A) /\ ((euclidean__axioms.ET E F D A B C) /\ (euclidean__axioms.ET E F D A C B))) as H71.
------------------------------------------------------------- exact H70.
------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.ET E F D A B C) /\ (euclidean__axioms.ET E F D A C B)) as H73.
-------------------------------------------------------------- exact H72.
-------------------------------------------------------------- destruct H73 as [H73 H74].
exact H73.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B C E F D) as H67.
---------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric (E) (F) (D) (A) (B) (C) H66).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B C D E F) as H68.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET A B C F D E) /\ ((euclidean__axioms.ET A B C E D F) /\ ((euclidean__axioms.ET A B C F E D) /\ ((euclidean__axioms.ET A B C D F E) /\ (euclidean__axioms.ET A B C D E F))))) as H68.
------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation (A) (B) (C) (E) (F) (D) H67).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.ET A B C F D E) /\ ((euclidean__axioms.ET A B C E D F) /\ ((euclidean__axioms.ET A B C F E D) /\ ((euclidean__axioms.ET A B C D F E) /\ (euclidean__axioms.ET A B C D E F))))) as H69.
------------------------------------------------------------- exact H68.
------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.ET A B C E D F) /\ ((euclidean__axioms.ET A B C F E D) /\ ((euclidean__axioms.ET A B C D F E) /\ (euclidean__axioms.ET A B C D E F)))) as H71.
-------------------------------------------------------------- exact H70.
-------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.ET A B C F E D) /\ ((euclidean__axioms.ET A B C D F E) /\ (euclidean__axioms.ET A B C D E F))) as H73.
--------------------------------------------------------------- exact H72.
--------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.ET A B C D F E) /\ (euclidean__axioms.ET A B C D E F)) as H75.
---------------------------------------------------------------- exact H74.
---------------------------------------------------------------- destruct H75 as [H75 H76].
exact H76.
----------------------------------------------------------- exact H68.
Qed.
