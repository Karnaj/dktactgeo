Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__PGsymmetric.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel2.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Require Export proposition__33.
Require Export proposition__34.
Require Export proposition__35.
Definition proposition__36A : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__defs.PG A B C D) -> ((euclidean__defs.PG E F G H) -> ((euclidean__axioms.Col A D E) -> ((euclidean__axioms.Col A D H) -> ((euclidean__axioms.Col B C F) -> ((euclidean__axioms.Col B C G) -> ((euclidean__axioms.Cong B C F G) -> ((euclidean__axioms.BetS B M H) -> ((euclidean__axioms.BetS C M E) -> (euclidean__axioms.EF A B C D E F G H))))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
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
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H9.
- assert (* Cut *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H9.
-- exact H1.
-- assert (* Cut *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as __TmpHyp.
--- exact H9.
--- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H10.
---- exact __TmpHyp.
---- destruct H10 as [H10 H11].
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H12.
----- exact H0.
----- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp0.
------ exact H12.
------ assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H13.
------- exact __TmpHyp0.
------- destruct H13 as [H13 H14].
split.
-------- exact H13.
-------- exact H14.
- assert (* Cut *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H10.
-- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H10.
--- exact H9.
--- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp.
---- exact H10.
---- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H11.
----- exact __TmpHyp.
----- destruct H11 as [H11 H12].
assert (* Cut *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H13.
------ exact H1.
------ assert (* Cut *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as __TmpHyp0.
------- exact H13.
------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H14.
-------- exact __TmpHyp0.
-------- destruct H14 as [H14 H15].
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H16.
--------- exact H0.
--------- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp1.
---------- exact H16.
---------- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H17.
----------- exact __TmpHyp1.
----------- destruct H17 as [H17 H18].
split.
------------ exact H14.
------------ exact H15.
-- assert (* Cut *) (euclidean__axioms.nCol A C D) as H11.
--- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H11.
---- exact H10.
---- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H13.
----- exact H9.
----- destruct H13 as [H13 H14].
assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H15.
------ apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (C) (D) H13).
------ assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H16.
------- exact H15.
------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D))) as H18.
-------- exact H17.
-------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)) as H20.
--------- exact H19.
--------- destruct H20 as [H20 H21].
exact H18.
--- assert (* Cut *) (euclidean__axioms.neq A D) as H12.
---- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H12.
----- exact H10.
----- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H14.
------ exact H9.
------ destruct H14 as [H14 H15].
assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))))) as H16.
------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (C) (D) H11).
------- assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))))) as H17.
-------- exact H16.
-------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A))))) as H19.
--------- exact H18.
--------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))) as H21.
---------- exact H20.
---------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A))) as H23.
----------- exact H22.
----------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)) as H25.
------------ exact H24.
------------ destruct H25 as [H25 H26].
exact H21.
---- assert (* Cut *) (euclidean__axioms.Cong A D B C) as H13.
----- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H13.
------ exact H10.
------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H15.
------- exact H9.
------- destruct H15 as [H15 H16].
assert (* Cut *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H17.
-------- apply (@proposition__34.proposition__34 (A) (D) (B) (C) H0).
-------- assert (* AndElim *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H18.
--------- exact H17.
--------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B)))) as H20.
---------- exact H19.
---------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))) as H22.
----------- exact H21.
----------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B)) as H24.
------------ exact H23.
------------ destruct H24 as [H24 H25].
exact H18.
----- assert (* Cut *) (euclidean__axioms.Cong E H F G) as H14.
------ assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H14.
------- exact H10.
------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H16.
-------- exact H9.
-------- destruct H16 as [H16 H17].
assert (* Cut *) ((euclidean__axioms.Cong E H F G) /\ ((euclidean__axioms.Cong E F H G) /\ ((euclidean__defs.CongA F E H H G F) /\ ((euclidean__defs.CongA E H G G F E) /\ (euclidean__axioms.Cong__3 F E H H G F))))) as H18.
--------- apply (@proposition__34.proposition__34 (E) (H) (F) (G) H1).
--------- assert (* AndElim *) ((euclidean__axioms.Cong E H F G) /\ ((euclidean__axioms.Cong E F H G) /\ ((euclidean__defs.CongA F E H H G F) /\ ((euclidean__defs.CongA E H G G F E) /\ (euclidean__axioms.Cong__3 F E H H G F))))) as H19.
---------- exact H18.
---------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Cong E F H G) /\ ((euclidean__defs.CongA F E H H G F) /\ ((euclidean__defs.CongA E H G G F E) /\ (euclidean__axioms.Cong__3 F E H H G F)))) as H21.
----------- exact H20.
----------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__defs.CongA F E H H G F) /\ ((euclidean__defs.CongA E H G G F E) /\ (euclidean__axioms.Cong__3 F E H H G F))) as H23.
------------ exact H22.
------------ destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__defs.CongA E H G G F E) /\ (euclidean__axioms.Cong__3 F E H H G F)) as H25.
------------- exact H24.
------------- destruct H25 as [H25 H26].
exact H19.
------ assert (* Cut *) (euclidean__axioms.Cong F G E H) as H15.
------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H15.
-------- exact H10.
-------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H17.
--------- exact H9.
--------- destruct H17 as [H17 H18].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (F) (E) (H) (G) H14).
------- assert (* Cut *) (euclidean__axioms.Cong B C E H) as H16.
-------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H16.
--------- exact H10.
--------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H18.
---------- exact H9.
---------- destruct H18 as [H18 H19].
apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (C) (F) (G) (E) (H) (H6) H15).
-------- assert (* Cut *) (euclidean__defs.Par B C A D) as H17.
--------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H17.
---------- exact H10.
---------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H19.
----------- exact H9.
----------- destruct H19 as [H19 H20].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (D) (B) (C) H20).
--------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H18.
---------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H18.
----------- exact H10.
----------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H20.
------------ exact H9.
------------ destruct H20 as [H20 H21].
assert (* Cut *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H22.
------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (D) (B) (C) H21).
------------- assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H23.
-------------- exact H22.
-------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C))) as H25.
--------------- exact H24.
--------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)) as H27.
---------------- exact H26.
---------------- destruct H27 as [H27 H28].
exact H25.
---------- assert (* Cut *) (euclidean__axioms.neq B C) as H19.
----------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H19.
------------ exact H10.
------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H21.
------------- exact H9.
------------- destruct H21 as [H21 H22].
assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H23.
-------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H18).
-------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H24.
--------------- exact H23.
--------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H26.
---------------- exact H25.
---------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H28.
----------------- exact H27.
----------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H30.
------------------ exact H29.
------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H32.
------------------- exact H31.
------------------- destruct H32 as [H32 H33].
exact H26.
----------- assert (* Cut *) (euclidean__axioms.neq E H) as H20.
------------ assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H20.
------------- exact H10.
------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H22.
-------------- exact H9.
-------------- destruct H22 as [H22 H23].
apply (@euclidean__axioms.axiom__nocollapse (B) (C) (E) (H) (H19) H16).
------------ assert (* Cut *) (euclidean__defs.Par B C E H) as H21.
------------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H21.
-------------- exact H10.
-------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H23.
--------------- exact H9.
--------------- destruct H23 as [H23 H24].
apply (@lemma__collinearparallel2.lemma__collinearparallel2 (B) (C) (A) (D) (E) (H) (H17) (H2) (H3) H20).
------------- assert (* Cut *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H22.
-------------- assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H22.
--------------- exact H10.
--------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H24.
---------------- exact H9.
---------------- destruct H24 as [H24 H25].
apply (@proposition__33.proposition__33 (B) (C) (E) (H) (M) (H21) (H16) (H7) H8).
-------------- assert (* Cut *) (euclidean__defs.Par E B C H) as H23.
--------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H23.
---------------- exact H22.
---------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H25.
----------------- exact H10.
----------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H27.
------------------ exact H9.
------------------ destruct H27 as [H27 H28].
assert (* Cut *) ((euclidean__defs.Par E B C H) /\ ((euclidean__defs.Par B E H C) /\ (euclidean__defs.Par E B H C))) as H29.
------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (E) (C) (H) H23).
------------------- assert (* AndElim *) ((euclidean__defs.Par E B C H) /\ ((euclidean__defs.Par B E H C) /\ (euclidean__defs.Par E B H C))) as H30.
-------------------- exact H29.
-------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.Par B E H C) /\ (euclidean__defs.Par E B H C)) as H32.
--------------------- exact H31.
--------------------- destruct H32 as [H32 H33].
exact H30.
--------------- assert (* Cut *) (euclidean__defs.Par E H B C) as H24.
---------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H24.
----------------- exact H22.
----------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H26.
------------------ exact H10.
------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H28.
------------------- exact H9.
------------------- destruct H28 as [H28 H29].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (B) (C) (E) (H) H21).
---------------- assert (* Cut *) (euclidean__defs.PG E B C H) as H25.
----------------- split.
------------------ exact H23.
------------------ exact H24.
----------------- assert (* Cut *) (euclidean__axioms.EF A B C D E B C H) as H26.
------------------ assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H26.
------------------- exact H22.
------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H28.
-------------------- exact H10.
-------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H30.
--------------------- exact H9.
--------------------- destruct H30 as [H30 H31].
apply (@proposition__35.proposition__35 (A) (B) (C) (D) (E) (H) (H0) (H25) (H2) H3).
------------------ assert (* Cut *) (euclidean__axioms.Cong F G B C) as H27.
------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H27.
-------------------- exact H22.
-------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H29.
--------------------- exact H10.
--------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H31.
---------------------- exact H9.
---------------------- destruct H31 as [H31 H32].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (F) (B) (C) (G) H6).
------------------- assert (* Cut *) (euclidean__axioms.Cong G F C B) as H28.
-------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H28.
--------------------- exact H22.
--------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H30.
---------------------- exact H10.
---------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H32.
----------------------- exact H9.
----------------------- destruct H32 as [H32 H33].
assert (* Cut *) ((euclidean__axioms.Cong G F C B) /\ ((euclidean__axioms.Cong G F B C) /\ (euclidean__axioms.Cong F G C B))) as H34.
------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (F) (G) (B) (C) H27).
------------------------ assert (* AndElim *) ((euclidean__axioms.Cong G F C B) /\ ((euclidean__axioms.Cong G F B C) /\ (euclidean__axioms.Cong F G C B))) as H35.
------------------------- exact H34.
------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Cong G F B C) /\ (euclidean__axioms.Cong F G C B)) as H37.
-------------------------- exact H36.
-------------------------- destruct H37 as [H37 H38].
exact H35.
-------------------- assert (* Cut *) (euclidean__defs.PG C H E B) as H29.
--------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H29.
---------------------- exact H22.
---------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H31.
----------------------- exact H10.
----------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H33.
------------------------ exact H9.
------------------------ destruct H33 as [H33 H34].
apply (@lemma__PGsymmetric.lemma__PGsymmetric (E) (B) (C) (H) H25).
--------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H30.
---------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H30.
----------------------- exact H22.
----------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H32.
------------------------ exact H10.
------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H34.
------------------------- exact H9.
------------------------- destruct H34 as [H34 H35].
assert (* Cut *) ((euclidean__axioms.nCol E H B) /\ ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol H B C) /\ (euclidean__axioms.nCol E H C)))) as H36.
-------------------------- apply (@lemma__parallelNC.lemma__parallelNC (E) (H) (B) (C) H24).
-------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E H B) /\ ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol H B C) /\ (euclidean__axioms.nCol E H C)))) as H37.
--------------------------- exact H36.
--------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol H B C) /\ (euclidean__axioms.nCol E H C))) as H39.
---------------------------- exact H38.
---------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.nCol H B C) /\ (euclidean__axioms.nCol E H C)) as H41.
----------------------------- exact H40.
----------------------------- destruct H41 as [H41 H42].
exact H18.
---------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H31.
----------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H31.
------------------------ exact H22.
------------------------ destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H33.
------------------------- exact H10.
------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H35.
-------------------------- exact H9.
-------------------------- destruct H35 as [H35 H36].
assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H37.
--------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H30).
--------------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H38.
---------------------------- exact H37.
---------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H40.
----------------------------- exact H39.
----------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H42.
------------------------------ exact H41.
------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H44.
------------------------------- exact H43.
------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H46.
-------------------------------- exact H45.
-------------------------------- destruct H46 as [H46 H47].
exact H40.
----------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H32.
------------------------ assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H32.
------------------------- exact H22.
------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H34.
-------------------------- exact H10.
-------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H36.
--------------------------- exact H9.
--------------------------- destruct H36 as [H36 H37].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H31).
------------------------ assert (* Cut *) (euclidean__axioms.Col C F G) as H33.
------------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H33.
-------------------------- exact H22.
-------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H35.
--------------------------- exact H10.
--------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H37.
---------------------------- exact H9.
---------------------------- destruct H37 as [H37 H38].
apply (@euclidean__tactics.not__nCol__Col (C) (F) (G)).
-----------------------------intro H39.
apply (@euclidean__tactics.Col__nCol__False (C) (F) (G) (H39)).
------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (C) (F) (G) (H4) (H5) H31).


------------------------- assert (* Cut *) (euclidean__axioms.Col G F C) as H34.
-------------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H34.
--------------------------- exact H22.
--------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H36.
---------------------------- exact H10.
---------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H38.
----------------------------- exact H9.
----------------------------- destruct H38 as [H38 H39].
assert (* Cut *) ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col F G C) /\ ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C G F) /\ (euclidean__axioms.Col G F C))))) as H40.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (F) (G) H33).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col F G C) /\ ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C G F) /\ (euclidean__axioms.Col G F C))))) as H41.
------------------------------- exact H40.
------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col F G C) /\ ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C G F) /\ (euclidean__axioms.Col G F C)))) as H43.
-------------------------------- exact H42.
-------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C G F) /\ (euclidean__axioms.Col G F C))) as H45.
--------------------------------- exact H44.
--------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col C G F) /\ (euclidean__axioms.Col G F C)) as H47.
---------------------------------- exact H46.
---------------------------------- destruct H47 as [H47 H48].
exact H48.
-------------------------- assert (* Cut *) (euclidean__axioms.Col C B F) as H35.
--------------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H35.
---------------------------- exact H22.
---------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H37.
----------------------------- exact H10.
----------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H39.
------------------------------ exact H9.
------------------------------ destruct H39 as [H39 H40].
assert (* Cut *) ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col C F B) /\ ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B))))) as H41.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (F) H4).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col C F B) /\ ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B))))) as H42.
-------------------------------- exact H41.
-------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col C F B) /\ ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B)))) as H44.
--------------------------------- exact H43.
--------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B))) as H46.
---------------------------------- exact H45.
---------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B)) as H48.
----------------------------------- exact H47.
----------------------------------- destruct H48 as [H48 H49].
exact H42.
--------------------------- assert (* Cut *) (euclidean__axioms.Col C B G) as H36.
---------------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H36.
----------------------------- exact H22.
----------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H38.
------------------------------ exact H10.
------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H40.
------------------------------- exact H9.
------------------------------- destruct H40 as [H40 H41].
assert (* Cut *) ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))))) as H42.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (G) H5).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))))) as H43.
--------------------------------- exact H42.
--------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B)))) as H45.
---------------------------------- exact H44.
---------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))) as H47.
----------------------------------- exact H46.
----------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B)) as H49.
------------------------------------ exact H48.
------------------------------------ destruct H49 as [H49 H50].
exact H43.
---------------------------- assert (* Cut *) (euclidean__axioms.Col B F G) as H37.
----------------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H37.
------------------------------ exact H22.
------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H39.
------------------------------- exact H10.
------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H41.
-------------------------------- exact H9.
-------------------------------- destruct H41 as [H41 H42].
apply (@euclidean__tactics.not__nCol__Col (B) (F) (G)).
---------------------------------intro H43.
apply (@euclidean__tactics.Col__nCol__False (B) (F) (G) (H43)).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (B) (F) (G) (H35) (H36) H32).


----------------------------- assert (* Cut *) (euclidean__axioms.Col G F B) as H38.
------------------------------ assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H38.
------------------------------- exact H22.
------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H40.
-------------------------------- exact H10.
-------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H42.
--------------------------------- exact H9.
--------------------------------- destruct H42 as [H42 H43].
assert (* Cut *) ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col F G B) /\ ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B))))) as H44.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (G) H37).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col F G B) /\ ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B))))) as H45.
----------------------------------- exact H44.
----------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col F G B) /\ ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B)))) as H47.
------------------------------------ exact H46.
------------------------------------ destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B))) as H49.
------------------------------------- exact H48.
------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B)) as H51.
-------------------------------------- exact H50.
-------------------------------------- destruct H51 as [H51 H52].
exact H52.
------------------------------ assert (* Cut *) (euclidean__defs.PG G H E F) as H39.
------------------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H39.
-------------------------------- exact H22.
-------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H41.
--------------------------------- exact H10.
--------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H43.
---------------------------------- exact H9.
---------------------------------- destruct H43 as [H43 H44].
apply (@lemma__PGsymmetric.lemma__PGsymmetric (E) (F) (G) (H) H1).
------------------------------- assert (* Cut *) (euclidean__axioms.EF G H E F C H E B) as H40.
-------------------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H40.
--------------------------------- exact H22.
--------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H42.
---------------------------------- exact H10.
---------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H44.
----------------------------------- exact H9.
----------------------------------- destruct H44 as [H44 H45].
apply (@proposition__35.proposition__35 (G) (H) (E) (F) (C) (B) (H39) (H29) (H34) H38).
-------------------------------- assert (* Cut *) (euclidean__axioms.EF G H E F E B C H) as H41.
--------------------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H41.
---------------------------------- exact H22.
---------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H43.
----------------------------------- exact H10.
----------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H45.
------------------------------------ exact H9.
------------------------------------ destruct H45 as [H45 H46].
assert (* Cut *) ((euclidean__axioms.EF G H E F H E B C) /\ ((euclidean__axioms.EF G H E F B E H C) /\ ((euclidean__axioms.EF G H E F E B C H) /\ ((euclidean__axioms.EF G H E F H C B E) /\ ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H))))))) as H47.
------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (G) (H) (E) (F) (C) (H) (E) (B) H40).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF G H E F H E B C) /\ ((euclidean__axioms.EF G H E F B E H C) /\ ((euclidean__axioms.EF G H E F E B C H) /\ ((euclidean__axioms.EF G H E F H C B E) /\ ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H))))))) as H48.
-------------------------------------- exact H47.
-------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.EF G H E F B E H C) /\ ((euclidean__axioms.EF G H E F E B C H) /\ ((euclidean__axioms.EF G H E F H C B E) /\ ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H)))))) as H50.
--------------------------------------- exact H49.
--------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.EF G H E F E B C H) /\ ((euclidean__axioms.EF G H E F H C B E) /\ ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H))))) as H52.
---------------------------------------- exact H51.
---------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.EF G H E F H C B E) /\ ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H)))) as H54.
----------------------------------------- exact H53.
----------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H))) as H56.
------------------------------------------ exact H55.
------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H)) as H58.
------------------------------------------- exact H57.
------------------------------------------- destruct H58 as [H58 H59].
exact H52.
--------------------------------- assert (* Cut *) (euclidean__axioms.EF E B C H G H E F) as H42.
---------------------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H42.
----------------------------------- exact H22.
----------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H44.
------------------------------------ exact H10.
------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H46.
------------------------------------- exact H9.
------------------------------------- destruct H46 as [H46 H47].
apply (@euclidean__axioms.axiom__EFsymmetric (G) (H) (E) (F) (E) (B) (C) (H) H41).
---------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D G H E F) as H43.
----------------------------------- assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H43.
------------------------------------ exact H22.
------------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H45.
------------------------------------- exact H10.
------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H47.
-------------------------------------- exact H9.
-------------------------------------- destruct H47 as [H47 H48].
apply (@euclidean__axioms.axiom__EFtransitive (A) (B) (C) (D) (G) (H) (E) (F) (E) (B) (C) (H) (H26) H42).
----------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E F G H) as H44.
------------------------------------ assert (* AndElim *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H44.
------------------------------------- exact H22.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H46.
-------------------------------------- exact H10.
-------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H48.
--------------------------------------- exact H9.
--------------------------------------- destruct H48 as [H48 H49].
assert (* Cut *) ((euclidean__axioms.EF A B C D H E F G) /\ ((euclidean__axioms.EF A B C D F E H G) /\ ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H))))))) as H50.
---------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (A) (B) (C) (D) (G) (H) (E) (F) H43).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.EF A B C D H E F G) /\ ((euclidean__axioms.EF A B C D F E H G) /\ ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H))))))) as H51.
----------------------------------------- exact H50.
----------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.EF A B C D F E H G) /\ ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H)))))) as H53.
------------------------------------------ exact H52.
------------------------------------------ destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H))))) as H55.
------------------------------------------- exact H54.
------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H)))) as H57.
-------------------------------------------- exact H56.
-------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H))) as H59.
--------------------------------------------- exact H58.
--------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H)) as H61.
---------------------------------------------- exact H60.
---------------------------------------------- destruct H61 as [H61 H62].
exact H55.
------------------------------------ exact H44.
Qed.
