Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel2.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__crisscross.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Require Export proposition__33.
Require Export proposition__34.
Require Export proposition__35.
Definition proposition__36 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point), (euclidean__defs.PG A B C D) -> ((euclidean__defs.PG E F G H) -> ((euclidean__axioms.Col A D E) -> ((euclidean__axioms.Col A D H) -> ((euclidean__axioms.Col B C F) -> ((euclidean__axioms.Col B C G) -> ((euclidean__axioms.Cong B C F G) -> (euclidean__axioms.EF A B C D E F G H))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
intro H6.
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H7.
- assert (* Cut *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H7.
-- exact H1.
-- assert (* Cut *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as __TmpHyp.
--- exact H7.
--- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H8.
---- exact __TmpHyp.
---- destruct H8 as [H8 H9].
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H10.
----- exact H0.
----- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp0.
------ exact H10.
------ assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H11.
------- exact __TmpHyp0.
------- destruct H11 as [H11 H12].
split.
-------- exact H11.
-------- exact H12.
- assert (* Cut *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H8.
-- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H8.
--- exact H7.
--- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp.
---- exact H8.
---- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H9.
----- exact __TmpHyp.
----- destruct H9 as [H9 H10].
assert (* Cut *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H11.
------ exact H1.
------ assert (* Cut *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as __TmpHyp0.
------- exact H11.
------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H12.
-------- exact __TmpHyp0.
-------- destruct H12 as [H12 H13].
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H14.
--------- exact H0.
--------- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp1.
---------- exact H14.
---------- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H15.
----------- exact __TmpHyp1.
----------- destruct H15 as [H15 H16].
split.
------------ exact H12.
------------ exact H13.
-- assert (* Cut *) (euclidean__axioms.nCol E H G) as H9.
--- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H9.
---- exact H8.
---- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H11.
----- exact H7.
----- destruct H11 as [H11 H12].
assert (* Cut *) ((euclidean__axioms.nCol E H F) /\ ((euclidean__axioms.nCol E F G) /\ ((euclidean__axioms.nCol H F G) /\ (euclidean__axioms.nCol E H G)))) as H13.
------ apply (@lemma__parallelNC.lemma__parallelNC (E) (H) (F) (G) H10).
------ assert (* AndElim *) ((euclidean__axioms.nCol E H F) /\ ((euclidean__axioms.nCol E F G) /\ ((euclidean__axioms.nCol H F G) /\ (euclidean__axioms.nCol E H G)))) as H14.
------- exact H13.
------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.nCol E F G) /\ ((euclidean__axioms.nCol H F G) /\ (euclidean__axioms.nCol E H G))) as H16.
-------- exact H15.
-------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol H F G) /\ (euclidean__axioms.nCol E H G)) as H18.
--------- exact H17.
--------- destruct H18 as [H18 H19].
exact H19.
--- assert (* Cut *) (euclidean__axioms.neq E H) as H10.
---- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H10.
----- exact H8.
----- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H12.
------ exact H7.
------ destruct H12 as [H12 H13].
assert (* Cut *) ((euclidean__axioms.neq E H) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G E)))))) as H14.
------- apply (@lemma__NCdistinct.lemma__NCdistinct (E) (H) (G) H9).
------- assert (* AndElim *) ((euclidean__axioms.neq E H) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G E)))))) as H15.
-------- exact H14.
-------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G E))))) as H17.
--------- exact H16.
--------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G E)))) as H19.
---------- exact H18.
---------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G E))) as H21.
----------- exact H20.
----------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G E)) as H23.
------------ exact H22.
------------ destruct H23 as [H23 H24].
exact H15.
---- assert (* Cut *) (euclidean__axioms.nCol A B C) as H11.
----- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H11.
------ exact H8.
------ destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H13.
------- exact H7.
------- destruct H13 as [H13 H14].
assert (* Cut *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H15.
-------- apply (@lemma__parallelNC.lemma__parallelNC (A) (D) (B) (C) H14).
-------- assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H16.
--------- exact H15.
--------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C))) as H18.
---------- exact H17.
---------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)) as H20.
----------- exact H19.
----------- destruct H20 as [H20 H21].
exact H18.
----- assert (* Cut *) (euclidean__axioms.neq B C) as H12.
------ assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H12.
------- exact H8.
------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H14.
-------- exact H7.
-------- destruct H14 as [H14 H15].
assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H16.
--------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H11).
--------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H17.
---------- exact H16.
---------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H19.
----------- exact H18.
----------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H21.
------------ exact H20.
------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H23.
------------- exact H22.
------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H25.
-------------- exact H24.
-------------- destruct H25 as [H25 H26].
exact H19.
------ assert (* Cut *) (euclidean__axioms.Cong E H F G) as H13.
------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H13.
-------- exact H8.
-------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H15.
--------- exact H7.
--------- destruct H15 as [H15 H16].
assert (* Cut *) ((euclidean__axioms.Cong E H F G) /\ ((euclidean__axioms.Cong E F H G) /\ ((euclidean__defs.CongA F E H H G F) /\ ((euclidean__defs.CongA E H G G F E) /\ (euclidean__axioms.Cong__3 F E H H G F))))) as H17.
---------- apply (@proposition__34.proposition__34 (E) (H) (F) (G) H1).
---------- assert (* AndElim *) ((euclidean__axioms.Cong E H F G) /\ ((euclidean__axioms.Cong E F H G) /\ ((euclidean__defs.CongA F E H H G F) /\ ((euclidean__defs.CongA E H G G F E) /\ (euclidean__axioms.Cong__3 F E H H G F))))) as H18.
----------- exact H17.
----------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Cong E F H G) /\ ((euclidean__defs.CongA F E H H G F) /\ ((euclidean__defs.CongA E H G G F E) /\ (euclidean__axioms.Cong__3 F E H H G F)))) as H20.
------------ exact H19.
------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__defs.CongA F E H H G F) /\ ((euclidean__defs.CongA E H G G F E) /\ (euclidean__axioms.Cong__3 F E H H G F))) as H22.
------------- exact H21.
------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.CongA E H G G F E) /\ (euclidean__axioms.Cong__3 F E H H G F)) as H24.
-------------- exact H23.
-------------- destruct H24 as [H24 H25].
exact H18.
------- assert (* Cut *) (euclidean__axioms.Cong F G E H) as H14.
-------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H14.
--------- exact H8.
--------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H16.
---------- exact H7.
---------- destruct H16 as [H16 H17].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (F) (E) (H) (G) H13).
-------- assert (* Cut *) (euclidean__axioms.Cong B C E H) as H15.
--------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H15.
---------- exact H8.
---------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H17.
----------- exact H7.
----------- destruct H17 as [H17 H18].
apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (C) (F) (G) (E) (H) (H6) H14).
--------- assert (* Cut *) (euclidean__defs.Par B C A D) as H16.
---------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H16.
----------- exact H8.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H18.
------------ exact H7.
------------ destruct H18 as [H18 H19].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (D) (B) (C) H19).
---------- assert (* Cut *) (euclidean__defs.Par B C E H) as H17.
----------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H17.
------------ exact H8.
------------ destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H19.
------------- exact H7.
------------- destruct H19 as [H19 H20].
apply (@lemma__collinearparallel2.lemma__collinearparallel2 (B) (C) (A) (D) (E) (H) (H16) (H2) (H3) H10).
----------- assert (* Cut *) (euclidean__defs.Par E H B C) as H18.
------------ assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H18.
------------- exact H8.
------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H20.
-------------- exact H7.
-------------- destruct H20 as [H20 H21].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (B) (C) (E) (H) H17).
------------ assert (* Cut *) (euclidean__axioms.Cong E H B C) as H19.
------------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H19.
-------------- exact H8.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H21.
--------------- exact H7.
--------------- destruct H21 as [H21 H22].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (B) (C) (H) H15).
------------- assert (* Cut *) (~(~((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)))) as H20.
-------------- intro H20.
assert (* Cut *) (euclidean__defs.CR E C B H) as H21.
--------------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H21.
---------------- exact H8.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H23.
----------------- exact H7.
----------------- destruct H23 as [H23 H24].
apply (@lemma__crisscross.lemma__crisscross (E) (B) (H) (C) (H18)).
------------------intro H25.
apply (@H20).
-------------------right.
exact H25.


--------------- apply (@H20).
----------------left.
exact H21.

-------------- assert (* Cut *) (euclidean__axioms.EF A B C D E F G H) as H21.
--------------- assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H21.
---------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C))).
-----------------intro H21.
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H22.
------------------ exact H7.
------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H24.
------------------- exact H8.
------------------- destruct H24 as [H24 H25].
assert (* Cut *) (False) as H26.
-------------------- apply (@H20 H21).
-------------------- assert (* Cut *) ((euclidean__defs.CR E C B H) -> False) as H27.
--------------------- intro H27.
apply (@H21).
----------------------left.
exact H27.

--------------------- assert (* Cut *) ((euclidean__defs.CR E B H C) -> False) as H28.
---------------------- intro H28.
apply (@H21).
-----------------------right.
exact H28.

---------------------- assert False.
-----------------------exact H26.
----------------------- contradiction.

---------------- assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H22.
----------------- exact H21.
----------------- assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as __TmpHyp.
------------------ exact H22.
------------------ assert (euclidean__defs.CR E C B H \/ euclidean__defs.CR E B H C) as H23.
------------------- exact __TmpHyp.
------------------- destruct H23 as [H23|H23].
-------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS E M C) /\ (euclidean__axioms.BetS B M H)) as H24.
--------------------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H24.
---------------------- exact H8.
---------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H26.
----------------------- exact H7.
----------------------- destruct H26 as [H26 H27].
exact H23.
--------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS E M C) /\ (euclidean__axioms.BetS B M H))) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [M H25].
assert (* AndElim *) ((euclidean__axioms.BetS E M C) /\ (euclidean__axioms.BetS B M H)) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H28.
------------------------ exact H8.
------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H30.
------------------------- exact H7.
------------------------- destruct H30 as [H30 H31].
assert (* Cut *) (euclidean__axioms.BetS H M B) as H32.
-------------------------- assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H32.
--------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
--------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (M) (H) H27).
-------------------------- assert (* Cut *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H33.
--------------------------- assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H33.
---------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
---------------------------- apply (@proposition__33.proposition__33 (E) (H) (B) (C) (M) (H18) (H19) (H26) H32).
--------------------------- assert (* Cut *) (euclidean__defs.Par E B C H) as H34.
---------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H34.
----------------------------- exact H33.
----------------------------- destruct H34 as [H34 H35].
assert (* Cut *) ((euclidean__defs.Par B E H C) /\ ((euclidean__defs.Par E B C H) /\ (euclidean__defs.Par B E C H))) as H36.
------------------------------ apply (@lemma__parallelflip.lemma__parallelflip (E) (B) (H) (C) H34).
------------------------------ assert (* AndElim *) ((euclidean__defs.Par B E H C) /\ ((euclidean__defs.Par E B C H) /\ (euclidean__defs.Par B E C H))) as H37.
------------------------------- exact H36.
------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__defs.Par E B C H) /\ (euclidean__defs.Par B E C H)) as H39.
-------------------------------- exact H38.
-------------------------------- destruct H39 as [H39 H40].
exact H39.
---------------------------- assert (* Cut *) (euclidean__defs.PG E B C H) as H35.
----------------------------- assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H35.
------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
------------------------------ split.
------------------------------- exact H34.
------------------------------- exact H18.
----------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E B C H) as H36.
------------------------------ assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H36.
------------------------------- exact H33.
------------------------------- destruct H36 as [H36 H37].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H38.
-------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
-------------------------------- apply (@proposition__35.proposition__35 (A) (B) (C) (D) (E) (H) (H0) (H35) (H2) H3).
------------------------------ assert (* Cut *) (euclidean__axioms.Col C F G) as H37.
------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H37.
-------------------------------- exact H33.
-------------------------------- destruct H37 as [H37 H38].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H39.
--------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
--------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (F) (G)).
----------------------------------intro H40.
apply (@euclidean__tactics.Col__nCol__False (C) (F) (G) (H40)).
-----------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (C) (F) (G) (H4) (H5) H12).


------------------------------- assert (* Cut *) (euclidean__axioms.Col G F C) as H38.
-------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H38.
--------------------------------- exact H33.
--------------------------------- destruct H38 as [H38 H39].
assert (* Cut *) ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col F G C) /\ ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C G F) /\ (euclidean__axioms.Col G F C))))) as H40.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (G) H37).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col F G C) /\ ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C G F) /\ (euclidean__axioms.Col G F C))))) as H41.
----------------------------------- exact H40.
----------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col F G C) /\ ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C G F) /\ (euclidean__axioms.Col G F C)))) as H43.
------------------------------------ exact H42.
------------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C G F) /\ (euclidean__axioms.Col G F C))) as H45.
------------------------------------- exact H44.
------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col C G F) /\ (euclidean__axioms.Col G F C)) as H47.
-------------------------------------- exact H46.
-------------------------------------- destruct H47 as [H47 H48].
exact H48.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col C B F) as H39.
--------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H39.
---------------------------------- exact H33.
---------------------------------- destruct H39 as [H39 H40].
assert (* Cut *) ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col C F B) /\ ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B))))) as H41.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (F) H4).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col C F B) /\ ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B))))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col C F B) /\ ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B)))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B))) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B)) as H48.
--------------------------------------- exact H47.
--------------------------------------- destruct H48 as [H48 H49].
exact H42.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col C B G) as H40.
---------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H40.
----------------------------------- exact H33.
----------------------------------- destruct H40 as [H40 H41].
assert (* Cut *) ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))))) as H42.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (G) H5).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))))) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B)))) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))) as H47.
--------------------------------------- exact H46.
--------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B)) as H49.
---------------------------------------- exact H48.
---------------------------------------- destruct H49 as [H49 H50].
exact H43.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H41.
----------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H41.
------------------------------------ exact H33.
------------------------------------ destruct H41 as [H41 H42].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H43.
------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H12).
----------------------------------- assert (* Cut *) (euclidean__axioms.Col B F G) as H42.
------------------------------------ assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H42.
------------------------------------- exact H33.
------------------------------------- destruct H42 as [H42 H43].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H44.
-------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
-------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (F) (G)).
---------------------------------------intro H45.
apply (@euclidean__tactics.Col__nCol__False (B) (F) (G) (H45)).
----------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (B) (F) (G) (H39) (H40) H41).


------------------------------------ assert (* Cut *) (euclidean__axioms.Col G F B) as H43.
------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H43.
-------------------------------------- exact H33.
-------------------------------------- destruct H43 as [H43 H44].
assert (* Cut *) ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col F G B) /\ ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B))))) as H45.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (G) H42).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col F G B) /\ ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B))))) as H46.
---------------------------------------- exact H45.
---------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col F G B) /\ ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B)))) as H48.
----------------------------------------- exact H47.
----------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B))) as H50.
------------------------------------------ exact H49.
------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B)) as H52.
------------------------------------------- exact H51.
------------------------------------------- destruct H52 as [H52 H53].
exact H53.
------------------------------------- assert (* Cut *) (euclidean__defs.Par F G E H) as H44.
-------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H44.
--------------------------------------- exact H33.
--------------------------------------- destruct H44 as [H44 H45].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H46.
---------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
---------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (E) (H) (F) (G) H29).
-------------------------------------- assert (* Cut *) (euclidean__defs.Par G F H E) as H45.
--------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H45.
---------------------------------------- exact H33.
---------------------------------------- destruct H45 as [H45 H46].
assert (* Cut *) ((euclidean__defs.Par G F E H) /\ ((euclidean__defs.Par F G H E) /\ (euclidean__defs.Par G F H E))) as H47.
----------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (F) (G) (E) (H) H44).
----------------------------------------- assert (* AndElim *) ((euclidean__defs.Par G F E H) /\ ((euclidean__defs.Par F G H E) /\ (euclidean__defs.Par G F H E))) as H48.
------------------------------------------ exact H47.
------------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Par F G H E) /\ (euclidean__defs.Par G F H E)) as H50.
------------------------------------------- exact H49.
------------------------------------------- destruct H50 as [H50 H51].
exact H51.
--------------------------------------- assert (* Cut *) (euclidean__defs.Par E F G H) as H46.
---------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B C H) /\ (euclidean__defs.Par E H B C)) as H46.
----------------------------------------- exact H35.
----------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H48.
------------------------------------------ exact H33.
------------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H50.
------------------------------------------- exact H1.
------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H52.
-------------------------------------------- exact H0.
-------------------------------------------- destruct H52 as [H52 H53].
exact H28.
---------------------------------------- assert (* Cut *) (euclidean__defs.Par G H E F) as H47.
----------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H47.
------------------------------------------ exact H33.
------------------------------------------ destruct H47 as [H47 H48].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H49.
------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (E) (F) (G) (H) H46).
----------------------------------------- assert (* Cut *) (euclidean__defs.PG G H E F) as H48.
------------------------------------------ assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H48.
------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
------------------------------------------- split.
-------------------------------------------- exact H47.
-------------------------------------------- exact H45.
------------------------------------------ assert (* Cut *) (euclidean__defs.Par C H E B) as H49.
------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H49.
-------------------------------------------- exact H33.
-------------------------------------------- destruct H49 as [H49 H50].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H51.
--------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
--------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (E) (B) (C) (H) H34).
------------------------------------------- assert (* Cut *) (euclidean__defs.Par B C E H) as H50.
-------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H50.
--------------------------------------------- exact H33.
--------------------------------------------- destruct H50 as [H50 H51].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H52.
---------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
---------------------------------------------- exact H17.
-------------------------------------------- assert (* Cut *) (euclidean__defs.Par C B H E) as H51.
--------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H51.
---------------------------------------------- exact H33.
---------------------------------------------- destruct H51 as [H51 H52].
assert (* Cut *) ((euclidean__defs.Par C B E H) /\ ((euclidean__defs.Par B C H E) /\ (euclidean__defs.Par C B H E))) as H53.
----------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (C) (E) (H) H50).
----------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par C B E H) /\ ((euclidean__defs.Par B C H E) /\ (euclidean__defs.Par C B H E))) as H54.
------------------------------------------------ exact H53.
------------------------------------------------ destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__defs.Par B C H E) /\ (euclidean__defs.Par C B H E)) as H56.
------------------------------------------------- exact H55.
------------------------------------------------- destruct H56 as [H56 H57].
exact H57.
--------------------------------------------- assert (* Cut *) (euclidean__defs.PG C H E B) as H52.
---------------------------------------------- assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H52.
----------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
----------------------------------------------- split.
------------------------------------------------ exact H49.
------------------------------------------------ exact H51.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.EF G H E F C H E B) as H53.
----------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H53.
------------------------------------------------ exact H33.
------------------------------------------------ destruct H53 as [H53 H54].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H55.
------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
------------------------------------------------- apply (@proposition__35.proposition__35 (G) (H) (E) (F) (C) (B) (H48) (H52) (H38) H43).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.EF G H E F E B C H) as H54.
------------------------------------------------ assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H54.
------------------------------------------------- exact H33.
------------------------------------------------- destruct H54 as [H54 H55].
assert (* Cut *) ((euclidean__axioms.EF G H E F H E B C) /\ ((euclidean__axioms.EF G H E F B E H C) /\ ((euclidean__axioms.EF G H E F E B C H) /\ ((euclidean__axioms.EF G H E F H C B E) /\ ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H))))))) as H56.
-------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (G) (H) (E) (F) (C) (H) (E) (B) H53).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF G H E F H E B C) /\ ((euclidean__axioms.EF G H E F B E H C) /\ ((euclidean__axioms.EF G H E F E B C H) /\ ((euclidean__axioms.EF G H E F H C B E) /\ ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H))))))) as H57.
--------------------------------------------------- exact H56.
--------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.EF G H E F B E H C) /\ ((euclidean__axioms.EF G H E F E B C H) /\ ((euclidean__axioms.EF G H E F H C B E) /\ ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H)))))) as H59.
---------------------------------------------------- exact H58.
---------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.EF G H E F E B C H) /\ ((euclidean__axioms.EF G H E F H C B E) /\ ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H))))) as H61.
----------------------------------------------------- exact H60.
----------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.EF G H E F H C B E) /\ ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H)))) as H63.
------------------------------------------------------ exact H62.
------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H))) as H65.
------------------------------------------------------- exact H64.
------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H)) as H67.
-------------------------------------------------------- exact H66.
-------------------------------------------------------- destruct H67 as [H67 H68].
exact H61.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF E B C H G H E F) as H55.
------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H55.
-------------------------------------------------- exact H33.
-------------------------------------------------- destruct H55 as [H55 H56].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H57.
--------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
--------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (G) (H) (E) (F) (E) (B) (C) (H) H54).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D G H E F) as H56.
-------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H56.
--------------------------------------------------- exact H33.
--------------------------------------------------- destruct H56 as [H56 H57].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H58.
---------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
---------------------------------------------------- apply (@euclidean__axioms.axiom__EFtransitive (A) (B) (C) (D) (G) (H) (E) (F) (E) (B) (C) (H) (H36) H55).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E F G H) as H57.
--------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E B H C) /\ (euclidean__axioms.Cong E B H C)) as H57.
---------------------------------------------------- exact H33.
---------------------------------------------------- destruct H57 as [H57 H58].
assert (* Cut *) ((euclidean__axioms.EF A B C D H E F G) /\ ((euclidean__axioms.EF A B C D F E H G) /\ ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H))))))) as H59.
----------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (A) (B) (C) (D) (G) (H) (E) (F) H56).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF A B C D H E F G) /\ ((euclidean__axioms.EF A B C D F E H G) /\ ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H))))))) as H60.
------------------------------------------------------ exact H59.
------------------------------------------------------ destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.EF A B C D F E H G) /\ ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H)))))) as H62.
------------------------------------------------------- exact H61.
------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H))))) as H64.
-------------------------------------------------------- exact H63.
-------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H)))) as H66.
--------------------------------------------------------- exact H65.
--------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H))) as H68.
---------------------------------------------------------- exact H67.
---------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H)) as H70.
----------------------------------------------------------- exact H69.
----------------------------------------------------------- destruct H70 as [H70 H71].
exact H64.
--------------------------------------------------- exact H57.
-------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS E M B) /\ (euclidean__axioms.BetS H M C)) as H24.
--------------------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H24.
---------------------- exact H8.
---------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H26.
----------------------- exact H7.
----------------------- destruct H26 as [H26 H27].
exact H23.
--------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS E M B) /\ (euclidean__axioms.BetS H M C))) as H25.
---------------------- exact H24.
---------------------- destruct H25 as [M H25].
assert (* AndElim *) ((euclidean__axioms.BetS E M B) /\ (euclidean__axioms.BetS H M C)) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H28.
------------------------ exact H8.
------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H30.
------------------------- exact H7.
------------------------- destruct H30 as [H30 H31].
assert (* Cut *) (euclidean__defs.Par H E B C) as H32.
-------------------------- assert (* Cut *) ((euclidean__defs.Par H E B C) /\ ((euclidean__defs.Par E H C B) /\ (euclidean__defs.Par H E C B))) as H32.
--------------------------- apply (@lemma__parallelflip.lemma__parallelflip (E) (H) (B) (C) H18).
--------------------------- assert (* AndElim *) ((euclidean__defs.Par H E B C) /\ ((euclidean__defs.Par E H C B) /\ (euclidean__defs.Par H E C B))) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.Par E H C B) /\ (euclidean__defs.Par H E C B)) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
exact H33.
-------------------------- assert (* Cut *) (euclidean__axioms.Cong H E B C) as H33.
--------------------------- assert (* Cut *) ((euclidean__axioms.Cong H E C B) /\ ((euclidean__axioms.Cong H E B C) /\ (euclidean__axioms.Cong E H C B))) as H33.
---------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (E) (H) (B) (C) H19).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H E C B) /\ ((euclidean__axioms.Cong H E B C) /\ (euclidean__axioms.Cong E H C B))) as H34.
----------------------------- exact H33.
----------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Cong H E B C) /\ (euclidean__axioms.Cong E H C B)) as H36.
------------------------------ exact H35.
------------------------------ destruct H36 as [H36 H37].
exact H36.
--------------------------- assert (* Cut *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H34.
---------------------------- assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H34.
----------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
----------------------------- apply (@proposition__33.proposition__33 (H) (E) (B) (C) (M) (H32) (H33) (H27) H26).
---------------------------- assert (* Cut *) (euclidean__defs.Par H B C E) as H35.
----------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
assert (* Cut *) ((euclidean__defs.Par B H E C) /\ ((euclidean__defs.Par H B C E) /\ (euclidean__defs.Par B H C E))) as H37.
------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (H) (B) (E) (C) H35).
------------------------------- assert (* AndElim *) ((euclidean__defs.Par B H E C) /\ ((euclidean__defs.Par H B C E) /\ (euclidean__defs.Par B H C E))) as H38.
-------------------------------- exact H37.
-------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__defs.Par H B C E) /\ (euclidean__defs.Par B H C E)) as H40.
--------------------------------- exact H39.
--------------------------------- destruct H40 as [H40 H41].
exact H40.
----------------------------- assert (* Cut *) (euclidean__defs.PG H B C E) as H36.
------------------------------ assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H36.
------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
------------------------------- split.
-------------------------------- exact H35.
-------------------------------- exact H32.
------------------------------ assert (* Cut *) (euclidean__axioms.EF A B C D H B C E) as H37.
------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H37.
-------------------------------- exact H34.
-------------------------------- destruct H37 as [H37 H38].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H39.
--------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
--------------------------------- apply (@proposition__35.proposition__35 (A) (B) (C) (D) (H) (E) (H0) (H36) (H3) H2).
------------------------------- assert (* Cut *) (euclidean__axioms.Col C G F) as H38.
-------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H38.
--------------------------------- exact H34.
--------------------------------- destruct H38 as [H38 H39].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H40.
---------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
---------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (G) (F)).
-----------------------------------intro H41.
apply (@euclidean__tactics.Col__nCol__False (C) (G) (F) (H41)).
------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (C) (G) (F) (H5) (H4) H12).


-------------------------------- assert (* Cut *) (euclidean__axioms.Col F G C) as H39.
--------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H39.
---------------------------------- exact H34.
---------------------------------- destruct H39 as [H39 H40].
assert (* Cut *) ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C))))) as H41.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (G) (F) H38).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C))))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C)))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C))) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C)) as H48.
--------------------------------------- exact H47.
--------------------------------------- destruct H48 as [H48 H49].
exact H49.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col C B G) as H40.
---------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H40.
----------------------------------- exact H34.
----------------------------------- destruct H40 as [H40 H41].
assert (* Cut *) ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))))) as H42.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (G) H5).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))))) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B)))) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))) as H47.
--------------------------------------- exact H46.
--------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B)) as H49.
---------------------------------------- exact H48.
---------------------------------------- destruct H49 as [H49 H50].
exact H43.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col C B F) as H41.
----------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H41.
------------------------------------ exact H34.
------------------------------------ destruct H41 as [H41 H42].
assert (* Cut *) ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col C F B) /\ ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B))))) as H43.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (F) H4).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col C F B) /\ ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B))))) as H44.
-------------------------------------- exact H43.
-------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col C F B) /\ ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B)))) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B))) as H48.
---------------------------------------- exact H47.
---------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B)) as H50.
----------------------------------------- exact H49.
----------------------------------------- destruct H50 as [H50 H51].
exact H44.
----------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H42.
------------------------------------ assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H42.
------------------------------------- exact H34.
------------------------------------- destruct H42 as [H42 H43].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H44.
-------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
-------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H12).
------------------------------------ assert (* Cut *) (euclidean__axioms.Col B G F) as H43.
------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H43.
-------------------------------------- exact H34.
-------------------------------------- destruct H43 as [H43 H44].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H45.
--------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
--------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (G) (F)).
----------------------------------------intro H46.
apply (@euclidean__tactics.Col__nCol__False (B) (G) (F) (H46)).
-----------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (B) (G) (F) (H40) (H41) H42).


------------------------------------- assert (* Cut *) (euclidean__axioms.Col F G B) as H44.
-------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H44.
--------------------------------------- exact H34.
--------------------------------------- destruct H44 as [H44 H45].
assert (* Cut *) ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))))) as H46.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (G) (F) H43).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))))) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col G F B) /\ ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B)))) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B))) as H51.
------------------------------------------- exact H50.
------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col B F G) /\ (euclidean__axioms.Col F G B)) as H53.
-------------------------------------------- exact H52.
-------------------------------------------- destruct H53 as [H53 H54].
exact H54.
-------------------------------------- assert (* Cut *) (euclidean__defs.Par H E F G) as H45.
--------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H45.
---------------------------------------- exact H34.
---------------------------------------- destruct H45 as [H45 H46].
assert (* Cut *) ((euclidean__defs.Par H E F G) /\ ((euclidean__defs.Par E H G F) /\ (euclidean__defs.Par H E G F))) as H47.
----------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (E) (H) (F) (G) H29).
----------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H E F G) /\ ((euclidean__defs.Par E H G F) /\ (euclidean__defs.Par H E G F))) as H48.
------------------------------------------ exact H47.
------------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Par E H G F) /\ (euclidean__defs.Par H E G F)) as H50.
------------------------------------------- exact H49.
------------------------------------------- destruct H50 as [H50 H51].
exact H48.
--------------------------------------- assert (* Cut *) (euclidean__defs.Par F G H E) as H46.
---------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H46.
----------------------------------------- exact H34.
----------------------------------------- destruct H46 as [H46 H47].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H48.
------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (H) (E) (F) (G) H45).
---------------------------------------- assert (* Cut *) (euclidean__defs.Par F G E H) as H47.
----------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H47.
------------------------------------------ exact H34.
------------------------------------------ destruct H47 as [H47 H48].
assert (* Cut *) ((euclidean__defs.Par G F H E) /\ ((euclidean__defs.Par F G E H) /\ (euclidean__defs.Par G F E H))) as H49.
------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (F) (G) (H) (E) H46).
------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par G F H E) /\ ((euclidean__defs.Par F G E H) /\ (euclidean__defs.Par G F E H))) as H50.
-------------------------------------------- exact H49.
-------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__defs.Par F G E H) /\ (euclidean__defs.Par G F E H)) as H52.
--------------------------------------------- exact H51.
--------------------------------------------- destruct H52 as [H52 H53].
exact H52.
----------------------------------------- assert (* Cut *) (euclidean__defs.Par F E H G) as H48.
------------------------------------------ assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H48.
------------------------------------------- exact H34.
------------------------------------------- destruct H48 as [H48 H49].
assert (* Cut *) ((euclidean__defs.Par F E G H) /\ ((euclidean__defs.Par E F H G) /\ (euclidean__defs.Par F E H G))) as H50.
-------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (E) (F) (G) (H) H28).
-------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par F E G H) /\ ((euclidean__defs.Par E F H G) /\ (euclidean__defs.Par F E H G))) as H51.
--------------------------------------------- exact H50.
--------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__defs.Par E F H G) /\ (euclidean__defs.Par F E H G)) as H53.
---------------------------------------------- exact H52.
---------------------------------------------- destruct H53 as [H53 H54].
exact H54.
------------------------------------------ assert (* Cut *) (euclidean__defs.PG F E H G) as H49.
------------------------------------------- assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H49.
-------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
-------------------------------------------- split.
--------------------------------------------- exact H48.
--------------------------------------------- exact H47.
------------------------------------------- assert (* Cut *) (euclidean__defs.Par C E H B) as H50.
-------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H50.
--------------------------------------------- exact H34.
--------------------------------------------- destruct H50 as [H50 H51].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H52.
---------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
---------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (H) (B) (C) (E) H35).
-------------------------------------------- assert (* Cut *) (euclidean__defs.Par C B E H) as H51.
--------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H51.
---------------------------------------------- exact H34.
---------------------------------------------- destruct H51 as [H51 H52].
assert (* Cut *) ((euclidean__defs.Par C B E H) /\ ((euclidean__defs.Par B C H E) /\ (euclidean__defs.Par C B H E))) as H53.
----------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (C) (E) (H) H17).
----------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par C B E H) /\ ((euclidean__defs.Par B C H E) /\ (euclidean__defs.Par C B H E))) as H54.
------------------------------------------------ exact H53.
------------------------------------------------ destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__defs.Par B C H E) /\ (euclidean__defs.Par C B H E)) as H56.
------------------------------------------------- exact H55.
------------------------------------------------- destruct H56 as [H56 H57].
exact H54.
--------------------------------------------- assert (* Cut *) (euclidean__defs.PG C E H B) as H52.
---------------------------------------------- assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H52.
----------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
----------------------------------------------- split.
------------------------------------------------ exact H50.
------------------------------------------------ exact H51.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.EF F E H G C E H B) as H53.
----------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H53.
------------------------------------------------ exact H34.
------------------------------------------------ destruct H53 as [H53 H54].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H55.
------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
------------------------------------------------- apply (@proposition__35.proposition__35 (F) (E) (H) (G) (C) (B) (H49) (H52) (H39) H44).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.EF F E H G H B C E) as H54.
------------------------------------------------ assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H54.
------------------------------------------------- exact H34.
------------------------------------------------- destruct H54 as [H54 H55].
assert (* Cut *) ((euclidean__axioms.EF F E H G E H B C) /\ ((euclidean__axioms.EF F E H G B H E C) /\ ((euclidean__axioms.EF F E H G H B C E) /\ ((euclidean__axioms.EF F E H G E C B H) /\ ((euclidean__axioms.EF F E H G B C E H) /\ ((euclidean__axioms.EF F E H G H E C B) /\ (euclidean__axioms.EF F E H G C B H E))))))) as H56.
-------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (F) (E) (H) (G) (C) (E) (H) (B) H53).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF F E H G E H B C) /\ ((euclidean__axioms.EF F E H G B H E C) /\ ((euclidean__axioms.EF F E H G H B C E) /\ ((euclidean__axioms.EF F E H G E C B H) /\ ((euclidean__axioms.EF F E H G B C E H) /\ ((euclidean__axioms.EF F E H G H E C B) /\ (euclidean__axioms.EF F E H G C B H E))))))) as H57.
--------------------------------------------------- exact H56.
--------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.EF F E H G B H E C) /\ ((euclidean__axioms.EF F E H G H B C E) /\ ((euclidean__axioms.EF F E H G E C B H) /\ ((euclidean__axioms.EF F E H G B C E H) /\ ((euclidean__axioms.EF F E H G H E C B) /\ (euclidean__axioms.EF F E H G C B H E)))))) as H59.
---------------------------------------------------- exact H58.
---------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.EF F E H G H B C E) /\ ((euclidean__axioms.EF F E H G E C B H) /\ ((euclidean__axioms.EF F E H G B C E H) /\ ((euclidean__axioms.EF F E H G H E C B) /\ (euclidean__axioms.EF F E H G C B H E))))) as H61.
----------------------------------------------------- exact H60.
----------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.EF F E H G E C B H) /\ ((euclidean__axioms.EF F E H G B C E H) /\ ((euclidean__axioms.EF F E H G H E C B) /\ (euclidean__axioms.EF F E H G C B H E)))) as H63.
------------------------------------------------------ exact H62.
------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.EF F E H G B C E H) /\ ((euclidean__axioms.EF F E H G H E C B) /\ (euclidean__axioms.EF F E H G C B H E))) as H65.
------------------------------------------------------- exact H64.
------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.EF F E H G H E C B) /\ (euclidean__axioms.EF F E H G C B H E)) as H67.
-------------------------------------------------------- exact H66.
-------------------------------------------------------- destruct H67 as [H67 H68].
exact H61.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF H B C E F E H G) as H55.
------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H55.
-------------------------------------------------- exact H34.
-------------------------------------------------- destruct H55 as [H55 H56].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H57.
--------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
--------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (F) (E) (H) (G) (H) (B) (C) (E) H54).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D F E H G) as H56.
-------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H56.
--------------------------------------------------- exact H34.
--------------------------------------------------- destruct H56 as [H56 H57].
assert (* Cut *) ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) as H58.
---------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR E C B H) \/ (euclidean__defs.CR E B H C)) H20).
---------------------------------------------------- apply (@euclidean__axioms.axiom__EFtransitive (A) (B) (C) (D) (F) (E) (H) (G) (H) (B) (C) (E) (H37) H55).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E F G H) as H57.
--------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par H B E C) /\ (euclidean__axioms.Cong H B E C)) as H57.
---------------------------------------------------- exact H34.
---------------------------------------------------- destruct H57 as [H57 H58].
assert (* Cut *) ((euclidean__axioms.EF A B C D E H G F) /\ ((euclidean__axioms.EF A B C D G H E F) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D G F E H) /\ ((euclidean__axioms.EF A B C D H E F G) /\ (euclidean__axioms.EF A B C D F G H E))))))) as H59.
----------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (A) (B) (C) (D) (F) (E) (H) (G) H56).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF A B C D E H G F) /\ ((euclidean__axioms.EF A B C D G H E F) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D G F E H) /\ ((euclidean__axioms.EF A B C D H E F G) /\ (euclidean__axioms.EF A B C D F G H E))))))) as H60.
------------------------------------------------------ exact H59.
------------------------------------------------------ destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.EF A B C D G H E F) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D G F E H) /\ ((euclidean__axioms.EF A B C D H E F G) /\ (euclidean__axioms.EF A B C D F G H E)))))) as H62.
------------------------------------------------------- exact H61.
------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D G F E H) /\ ((euclidean__axioms.EF A B C D H E F G) /\ (euclidean__axioms.EF A B C D F G H E))))) as H64.
-------------------------------------------------------- exact H63.
-------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D G F E H) /\ ((euclidean__axioms.EF A B C D H E F G) /\ (euclidean__axioms.EF A B C D F G H E)))) as H66.
--------------------------------------------------------- exact H65.
--------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.EF A B C D G F E H) /\ ((euclidean__axioms.EF A B C D H E F G) /\ (euclidean__axioms.EF A B C D F G H E))) as H68.
---------------------------------------------------------- exact H67.
---------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.EF A B C D H E F G) /\ (euclidean__axioms.EF A B C D F G H E)) as H70.
----------------------------------------------------------- exact H69.
----------------------------------------------------------- destruct H70 as [H70 H71].
exact H66.
--------------------------------------------------- exact H57.
--------------- exact H21.
Qed.
