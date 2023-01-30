Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__3__6a.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__sameside2.
Require Export lemma__samesidecollinear.
Require Export lemma__samesideflip.
Require Export lemma__samesidesymmetric.
Require Export lemma__samesidetransitive.
Require Export lemma__supplements2.
Require Export logic.
Require Export proposition__28D.
Require Export proposition__29C.
Definition proposition__43B : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point) (K: euclidean__axioms.Point), (euclidean__defs.PG A B C D) -> ((euclidean__axioms.BetS A H D) -> ((euclidean__axioms.BetS A E B) -> ((euclidean__axioms.BetS D F C) -> ((euclidean__axioms.BetS B G C) -> ((euclidean__defs.PG E A H K) -> ((euclidean__defs.PG G K F C) -> (euclidean__defs.PG E K G B))))))).
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
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
intro H6.
assert (* Cut *) (euclidean__defs.Par A D B C) as H7.
- assert (* AndElim *) ((euclidean__defs.Par G K F C) /\ (euclidean__defs.Par G C K F)) as H7.
-- exact H6.
-- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Par E A H K) /\ (euclidean__defs.Par E K A H)) as H9.
--- exact H5.
--- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H11.
---- exact H0.
---- destruct H11 as [H11 H12].
exact H12.
- assert (* Cut *) (euclidean__defs.Par A B C D) as H8.
-- assert (* AndElim *) ((euclidean__defs.Par G K F C) /\ (euclidean__defs.Par G C K F)) as H8.
--- exact H6.
--- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.Par E A H K) /\ (euclidean__defs.Par E K A H)) as H10.
---- exact H5.
---- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H12.
----- exact H0.
----- destruct H12 as [H12 H13].
exact H12.
-- assert (* Cut *) (euclidean__defs.Par E A H K) as H9.
--- assert (* AndElim *) ((euclidean__defs.Par G K F C) /\ (euclidean__defs.Par G C K F)) as H9.
---- exact H6.
---- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Par E A H K) /\ (euclidean__defs.Par E K A H)) as H11.
----- exact H5.
----- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H13.
------ exact H0.
------ destruct H13 as [H13 H14].
exact H11.
--- assert (* Cut *) (euclidean__defs.Par E K A H) as H10.
---- assert (* AndElim *) ((euclidean__defs.Par G K F C) /\ (euclidean__defs.Par G C K F)) as H10.
----- exact H6.
----- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.Par E A H K) /\ (euclidean__defs.Par E K A H)) as H12.
------ exact H5.
------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H14.
------- exact H0.
------- destruct H14 as [H14 H15].
exact H13.
---- assert (* Cut *) (euclidean__defs.Par G K F C) as H11.
----- assert (* AndElim *) ((euclidean__defs.Par G K F C) /\ (euclidean__defs.Par G C K F)) as H11.
------ exact H6.
------ destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Par E A H K) /\ (euclidean__defs.Par E K A H)) as H13.
------- exact H5.
------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H15.
-------- exact H0.
-------- destruct H15 as [H15 H16].
exact H11.
----- assert (* Cut *) (euclidean__defs.Par F C G K) as H12.
------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (G) (K) (F) (C) H11).
------ assert (* Cut *) (euclidean__defs.Par C F G K) as H13.
------- assert (* Cut *) ((euclidean__defs.Par C F G K) /\ ((euclidean__defs.Par F C K G) /\ (euclidean__defs.Par C F K G))) as H13.
-------- apply (@lemma__parallelflip.lemma__parallelflip (F) (C) (G) (K) H12).
-------- assert (* AndElim *) ((euclidean__defs.Par C F G K) /\ ((euclidean__defs.Par F C K G) /\ (euclidean__defs.Par C F K G))) as H14.
--------- exact H13.
--------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__defs.Par F C K G) /\ (euclidean__defs.Par C F K G)) as H16.
---------- exact H15.
---------- destruct H16 as [H16 H17].
exact H14.
------- assert (* Cut *) (euclidean__defs.Par G C K F) as H14.
-------- assert (* AndElim *) ((euclidean__defs.Par G K F C) /\ (euclidean__defs.Par G C K F)) as H14.
--------- exact H6.
--------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__defs.Par E A H K) /\ (euclidean__defs.Par E K A H)) as H16.
---------- exact H5.
---------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H18.
----------- exact H0.
----------- destruct H18 as [H18 H19].
exact H15.
-------- assert (* Cut *) (euclidean__defs.Par B C A D) as H15.
--------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (D) (B) (C) H7).
--------- assert (* Cut *) (euclidean__defs.Par C D A B) as H16.
---------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (B) (C) (D) H8).
---------- assert (* Cut *) (euclidean__defs.Par A H E K) as H17.
----------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (E) (K) (A) (H) H10).
----------- assert (* Cut *) (euclidean__defs.TP A B C D) as H18.
------------ apply (@lemma__paralleldef2B.lemma__paralleldef2B (A) (B) (C) (D) H8).
------------ assert (* Cut *) (euclidean__defs.TP E A H K) as H19.
------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B (E) (A) (H) (K) H9).
------------- assert (* Cut *) (euclidean__defs.TP G C K F) as H20.
-------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B (G) (C) (K) (F) H14).
-------------- assert (* Cut *) (euclidean__defs.TP B C A D) as H21.
--------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B (B) (C) (A) (D) H15).
--------------- assert (* Cut *) (euclidean__defs.OS A D B C) as H22.
---------------- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A D) /\ ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C)))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C))) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
assert (* AndElim *) ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C)) as H26.
------------------- exact H25.
------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)))) as H28.
-------------------- exact H20.
-------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C))) as H30.
--------------------- exact H29.
--------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)) as H32.
---------------------- exact H31.
---------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq H K) /\ ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A)))) as H34.
----------------------- exact H19.
----------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A))) as H36.
------------------------ exact H35.
------------------------ destruct H36 as [H36 H37].
assert (* AndElim *) ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A)) as H38.
------------------------- exact H37.
------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H40.
-------------------------- exact H18.
-------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H42.
--------------------------- exact H41.
--------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H44.
---------------------------- exact H43.
---------------------------- destruct H44 as [H44 H45].
exact H27.
---------------- assert (* Cut *) (euclidean__defs.OS A D C B) as H23.
----------------- apply (@lemma__samesideflip.lemma__samesideflip (B) (C) (A) (D) H22).
----------------- assert (* Cut *) (euclidean__defs.OS D A C B) as H24.
------------------ assert (* Cut *) ((euclidean__defs.OS D A C B) /\ ((euclidean__defs.OS A D B C) /\ (euclidean__defs.OS D A B C))) as H24.
------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (C) (B) (A) (D) H23).
------------------- assert (* AndElim *) ((euclidean__defs.OS D A C B) /\ ((euclidean__defs.OS A D B C) /\ (euclidean__defs.OS D A B C))) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__defs.OS A D B C) /\ (euclidean__defs.OS D A B C)) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
exact H25.
------------------ assert (* Cut *) (euclidean__defs.OS C D A B) as H25.
------------------- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A D) /\ ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C)))) as H25.
-------------------- exact H21.
-------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C))) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C)) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)))) as H31.
----------------------- exact H20.
----------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C))) as H33.
------------------------ exact H32.
------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)) as H35.
------------------------- exact H34.
------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq H K) /\ ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A)))) as H37.
-------------------------- exact H19.
-------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A))) as H39.
--------------------------- exact H38.
--------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A)) as H41.
---------------------------- exact H40.
---------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H43.
----------------------------- exact H18.
----------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H45.
------------------------------ exact H44.
------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H47.
------------------------------- exact H46.
------------------------------- destruct H47 as [H47 H48].
exact H48.
------------------- assert (* Cut *) (euclidean__defs.OS H K E A) as H26.
-------------------- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A D) /\ ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C)))) as H26.
--------------------- exact H21.
--------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C))) as H28.
---------------------- exact H27.
---------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C)) as H30.
----------------------- exact H29.
----------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)))) as H32.
------------------------ exact H20.
------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C))) as H34.
------------------------- exact H33.
------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)) as H36.
-------------------------- exact H35.
-------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq H K) /\ ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A)))) as H38.
--------------------------- exact H19.
--------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A))) as H40.
---------------------------- exact H39.
---------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A)) as H42.
----------------------------- exact H41.
----------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H44.
------------------------------ exact H18.
------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H46.
------------------------------- exact H45.
------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H48.
-------------------------------- exact H47.
-------------------------------- destruct H48 as [H48 H49].
exact H43.
-------------------- assert (* Cut *) (euclidean__defs.OS K F G C) as H27.
--------------------- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A D) /\ ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C)))) as H27.
---------------------- exact H21.
---------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C))) as H29.
----------------------- exact H28.
----------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C)) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)))) as H33.
------------------------- exact H20.
------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C))) as H35.
-------------------------- exact H34.
-------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)) as H37.
--------------------------- exact H36.
--------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq H K) /\ ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A)))) as H39.
---------------------------- exact H19.
---------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A))) as H41.
----------------------------- exact H40.
----------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A)) as H43.
------------------------------ exact H42.
------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H45.
------------------------------- exact H18.
------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H47.
-------------------------------- exact H46.
-------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H49.
--------------------------------- exact H48.
--------------------------------- destruct H49 as [H49 H50].
exact H38.
--------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H28.
---------------------- assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H28.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (B) H2).
----------------------- assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B)) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
exact H31.
---------------------- assert (* Cut *) (euclidean__axioms.neq A H) as H29.
----------------------- assert (* Cut *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq A H) /\ (euclidean__axioms.neq A D))) as H29.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (H) (D) H1).
------------------------ assert (* AndElim *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq A H) /\ (euclidean__axioms.neq A D))) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq A H) /\ (euclidean__axioms.neq A D)) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
exact H32.
----------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H30.
------------------------ assert (* Cut *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B C))) as H30.
------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (G) (C) H4).
------------------------- assert (* AndElim *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B C))) as H31.
-------------------------- exact H30.
-------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B C)) as H33.
--------------------------- exact H32.
--------------------------- destruct H33 as [H33 H34].
exact H33.
------------------------ assert (* Cut *) (euclidean__axioms.neq A B) as H31.
------------------------- assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H31.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (B) H2).
-------------------------- assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B)) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
exact H35.
------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H32.
-------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H31).
-------------------------- assert (* Cut *) (exists (e: euclidean__axioms.Point), (euclidean__axioms.BetS B A e) /\ (euclidean__axioms.Cong A e B A)) as H33.
--------------------------- apply (@lemma__extension.lemma__extension (B) (A) (B) (A) (H32) H32).
--------------------------- assert (exists e: euclidean__axioms.Point, ((euclidean__axioms.BetS B A e) /\ (euclidean__axioms.Cong A e B A))) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [e H34].
assert (* AndElim *) ((euclidean__axioms.BetS B A e) /\ (euclidean__axioms.Cong A e B A)) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
assert (* Cut *) (euclidean__axioms.BetS e A B) as H37.
------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (A) (e) H35).
------------------------------ assert (* Cut *) (euclidean__defs.OS D C A B) as H38.
------------------------------- assert (* Cut *) ((euclidean__defs.OS D C A B) /\ ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A))) as H38.
-------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (A) (B) (C) (D) H25).
-------------------------------- assert (* AndElim *) ((euclidean__defs.OS D C A B) /\ ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A))) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__defs.OS C D B A) /\ (euclidean__defs.OS D C B A)) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
exact H39.
------------------------------- assert (* Cut *) (euclidean__defs.RT D A B A B C) as H39.
-------------------------------- assert (* Cut *) (forall (B0: euclidean__axioms.Point) (D0: euclidean__axioms.Point) (E0: euclidean__axioms.Point) (G0: euclidean__axioms.Point) (H39: euclidean__axioms.Point), (euclidean__defs.Par G0 B0 H39 D0) -> ((euclidean__defs.OS B0 D0 G0 H39) -> ((euclidean__axioms.BetS E0 G0 H39) -> (euclidean__defs.RT B0 G0 H39 G0 H39 D0)))) as H39.
--------------------------------- intro B0.
intro D0.
intro E0.
intro G0.
intro H39.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA E0 G0 B0 G0 H39 D0) /\ (euclidean__defs.RT B0 G0 H39 G0 H39 D0)) as __2.
---------------------------------- apply (@proposition__29C.proposition__29C (B0) (D0) (E0) (G0) (H39) (__) (__0) __1).
---------------------------------- destruct __2 as [__2 __3].
exact __3.
--------------------------------- apply (@H39 (D) (C) (e) (A) (B) (H7) (H38) H37).
-------------------------------- assert (* Cut *) (euclidean__axioms.BetS B E A) as H40.
--------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (E) (B) H2).
--------------------------------- assert (* Cut *) (euclidean__axioms.BetS E A e) as H41.
---------------------------------- apply (@lemma__3__6a.lemma__3__6a (B) (E) (A) (e) (H40) H35).
---------------------------------- assert (* Cut *) (euclidean__axioms.BetS e A E) as H42.
----------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (A) (e) H41).
----------------------------------- assert (* Cut *) (euclidean__defs.OS H K A E) as H43.
------------------------------------ assert (* Cut *) ((euclidean__defs.OS K H E A) /\ ((euclidean__defs.OS H K A E) /\ (euclidean__defs.OS K H A E))) as H43.
------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (E) (A) (H) (K) H26).
------------------------------------- assert (* AndElim *) ((euclidean__defs.OS K H E A) /\ ((euclidean__defs.OS H K A E) /\ (euclidean__defs.OS K H A E))) as H44.
-------------------------------------- exact H43.
-------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.OS H K A E) /\ (euclidean__defs.OS K H A E)) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [H46 H47].
exact H46.
------------------------------------ assert (* Cut *) (euclidean__defs.RT H A E A E K) as H44.
------------------------------------- assert (* Cut *) (forall (B0: euclidean__axioms.Point) (D0: euclidean__axioms.Point) (E0: euclidean__axioms.Point) (G0: euclidean__axioms.Point) (H44: euclidean__axioms.Point), (euclidean__defs.Par G0 B0 H44 D0) -> ((euclidean__defs.OS B0 D0 G0 H44) -> ((euclidean__axioms.BetS E0 G0 H44) -> (euclidean__defs.RT B0 G0 H44 G0 H44 D0)))) as H44.
-------------------------------------- intro B0.
intro D0.
intro E0.
intro G0.
intro H44.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA E0 G0 B0 G0 H44 D0) /\ (euclidean__defs.RT B0 G0 H44 G0 H44 D0)) as __2.
--------------------------------------- apply (@proposition__29C.proposition__29C (B0) (D0) (E0) (G0) (H44) (__) (__0) __1).
--------------------------------------- destruct __2 as [__2 __3].
exact __3.
-------------------------------------- apply (@H44 (H) (K) (e) (A) (E) (H17) (H43) H42).
------------------------------------- assert (* Cut *) (euclidean__defs.Out A E B) as H45.
-------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (E) (B)).
---------------------------------------right.
right.
exact H2.

--------------------------------------- exact H28.
-------------------------------------- assert (* Cut *) (euclidean__defs.Out A H D) as H46.
--------------------------------------- apply (@lemma__ray4.lemma__ray4 (A) (H) (D)).
----------------------------------------right.
right.
exact H1.

---------------------------------------- exact H29.
--------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A H E) as H47.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A H E) /\ ((euclidean__axioms.nCol A E K) /\ ((euclidean__axioms.nCol H E K) /\ (euclidean__axioms.nCol A H K)))) as H47.
----------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (H) (E) (K) H17).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A H E) /\ ((euclidean__axioms.nCol A E K) /\ ((euclidean__axioms.nCol H E K) /\ (euclidean__axioms.nCol A H K)))) as H48.
------------------------------------------ exact H47.
------------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.nCol A E K) /\ ((euclidean__axioms.nCol H E K) /\ (euclidean__axioms.nCol A H K))) as H50.
------------------------------------------- exact H49.
------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.nCol H E K) /\ (euclidean__axioms.nCol A H K)) as H52.
-------------------------------------------- exact H51.
-------------------------------------------- destruct H52 as [H52 H53].
exact H48.
---------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E A H) as H48.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H A E) /\ ((euclidean__axioms.nCol H E A) /\ ((euclidean__axioms.nCol E A H) /\ ((euclidean__axioms.nCol A E H) /\ (euclidean__axioms.nCol E H A))))) as H48.
------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (A) (H) (E) H47).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol H A E) /\ ((euclidean__axioms.nCol H E A) /\ ((euclidean__axioms.nCol E A H) /\ ((euclidean__axioms.nCol A E H) /\ (euclidean__axioms.nCol E H A))))) as H49.
------------------------------------------- exact H48.
------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.nCol H E A) /\ ((euclidean__axioms.nCol E A H) /\ ((euclidean__axioms.nCol A E H) /\ (euclidean__axioms.nCol E H A)))) as H51.
-------------------------------------------- exact H50.
-------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.nCol E A H) /\ ((euclidean__axioms.nCol A E H) /\ (euclidean__axioms.nCol E H A))) as H53.
--------------------------------------------- exact H52.
--------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.nCol A E H) /\ (euclidean__axioms.nCol E H A)) as H55.
---------------------------------------------- exact H54.
---------------------------------------------- destruct H55 as [H55 H56].
exact H53.
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA E A H E A H) as H49.
------------------------------------------ apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (E) (A) (H) H48).
------------------------------------------ assert (* Cut *) (euclidean__defs.CongA E A H B A D) as H50.
------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (E) (A) (H) (E) (A) (H) (B) (D) (H49) (H45) H46).
------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H A E D A B) as H51.
-------------------------------------------- apply (@lemma__equalanglesflip.lemma__equalanglesflip (E) (A) (H) (B) (A) (D) H50).
-------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A E K A B C) as H52.
--------------------------------------------- assert (* Cut *) ((euclidean__defs.RT H A E A E K) -> ((euclidean__defs.CongA H A E D A B) -> ((euclidean__defs.RT D A B A B C) -> (euclidean__defs.CongA A E K A B C)))) as H52.
---------------------------------------------- intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA A E K A B C) /\ (euclidean__defs.CongA A B C A E K)) as __2.
----------------------------------------------- apply (@lemma__supplements2.lemma__supplements2 (H) (A) (E) (A) (B) (C) (D) (A) (B) (A) (E) (K) (__) (__0) __1).
----------------------------------------------- destruct __2 as [__2 __3].
exact __2.
---------------------------------------------- apply (@H52 (H44) (H51) H39).
--------------------------------------------- assert (* Cut *) (euclidean__defs.OS C D B A) as H53.
---------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip (A) (B) (C) (D) H25).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E B) as H54.
----------------------------------------------- right.
right.
right.
right.
left.
exact H2.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A E) as H55.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H55.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (B) H54).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H56.
-------------------------------------------------- exact H55.
-------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)))) as H58.
--------------------------------------------------- exact H57.
--------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))) as H60.
---------------------------------------------------- exact H59.
---------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A)) as H62.
----------------------------------------------------- exact H61.
----------------------------------------------------- destruct H62 as [H62 H63].
exact H60.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq E B) as H56.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H56.
-------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (E) (B) H2).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H57.
--------------------------------------------------- exact H56.
--------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B)) as H59.
---------------------------------------------------- exact H58.
---------------------------------------------------- destruct H59 as [H59 H60].
exact H57.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H57.
-------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (B) H56).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.OS C D B E) as H58.
--------------------------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear (B) (A) (E) (C) (D) (H53) (H55) H57).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A H D) as H59.
---------------------------------------------------- exact H46.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A D H) as H60.
----------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (A) (H) (D) H59).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.OS C H B E) as H61.
------------------------------------------------------ apply (@lemma__sameside2.lemma__sameside2 (B) (A) (E) (C) (D) (H) (H58) (H55) H60).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E A B) as H62.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B))))) as H62.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (E) H55).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B))))) as H63.
--------------------------------------------------------- exact H62.
--------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B)))) as H65.
---------------------------------------------------------- exact H64.
---------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B))) as H67.
----------------------------------------------------------- exact H66.
----------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ (euclidean__axioms.Col E A B)) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [H69 H70].
exact H70.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS H K E B) as H63.
-------------------------------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear (E) (A) (B) (H) (K) (H26) (H62) H56).
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS H K B E) as H64.
--------------------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip (E) (B) (H) (K) H63).
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS C K B E) as H65.
---------------------------------------------------------- apply (@lemma__samesidetransitive.lemma__samesidetransitive (B) (E) (C) (H) (K) (H61) H64).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS K C B E) as H66.
----------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS K C B E) /\ ((euclidean__defs.OS C K E B) /\ (euclidean__defs.OS K C E B))) as H66.
------------------------------------------------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (B) (E) (C) (K) H65).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__defs.OS K C B E) /\ ((euclidean__defs.OS C K E B) /\ (euclidean__defs.OS K C E B))) as H67.
------------------------------------------------------------- exact H66.
------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__defs.OS C K E B) /\ (euclidean__defs.OS K C E B)) as H69.
-------------------------------------------------------------- exact H68.
-------------------------------------------------------------- destruct H69 as [H69 H70].
exact H67.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B G C) as H67.
------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 (B) (G) (C)).
-------------------------------------------------------------right.
right.
exact H4.

------------------------------------------------------------- exact H30.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B C G) as H68.
------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (B) (G) (C) H67).
------------------------------------------------------------- assert (* Cut *) (B = B) as H69.
-------------------------------------------------------------- apply (@logic.eq__refl (Point) B).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B B E) as H70.
--------------------------------------------------------------- left.
exact H69.
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS K G B E) as H71.
---------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 (B) (B) (E) (K) (C) (G) (H66) (H70) H68).
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS K G E B) as H72.
----------------------------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip (B) (E) (K) (G) H71).
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B E A) as H73.
------------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 (B) (E) (A)).
-------------------------------------------------------------------right.
right.
exact H40.

------------------------------------------------------------------- exact H57.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B A E) as H74.
------------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (B) (E) (A) H73).
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A E K E B G) as H75.
-------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (E) (K) (A) (B) (C) (E) (G) (H52) (H74) H68).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E K B G) as H76.
--------------------------------------------------------------------- apply (@proposition__28D.proposition__28D (K) (G) (A) (E) (B) (H2) (H75) H72).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E K G B) as H77.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par K E B G) /\ ((euclidean__defs.Par E K G B) /\ (euclidean__defs.Par K E G B))) as H77.
----------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (E) (K) (B) (G) H76).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par K E B G) /\ ((euclidean__defs.Par E K G B) /\ (euclidean__defs.Par K E G B))) as H78.
------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------ destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__defs.Par E K G B) /\ (euclidean__defs.Par K E G B)) as H80.
------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------- destruct H80 as [H80 H81].
exact H80.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H78.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B C))) as H78.
------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (B) (G) (C) H4).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B C))) as H79.
------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B C)) as H81.
-------------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H82.
----------------------------------------------------------------------- assert (* Cut *) (exists (c: euclidean__axioms.Point), (euclidean__axioms.BetS B C c) /\ (euclidean__axioms.Cong C c B C)) as H79.
------------------------------------------------------------------------ apply (@lemma__extension.lemma__extension (B) (C) (B) (C) (H78) H78).
------------------------------------------------------------------------ assert (exists c: euclidean__axioms.Point, ((euclidean__axioms.BetS B C c) /\ (euclidean__axioms.Cong C c B C))) as H80.
------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------- destruct H80 as [c H80].
assert (* AndElim *) ((euclidean__axioms.BetS B C c) /\ (euclidean__axioms.Cong C c B C)) as H81.
-------------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* Cut *) (euclidean__axioms.BetS c C B) as H83.
--------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (C) (c) H81).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C D B A) as H84.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par D C A B) /\ ((euclidean__defs.Par C D B A) /\ (euclidean__defs.Par D C B A))) as H84.
----------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (C) (D) (A) (B) H16).
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par D C A B) /\ ((euclidean__defs.Par C D B A) /\ (euclidean__defs.Par D C B A))) as H85.
------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------ destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__defs.Par C D B A) /\ (euclidean__defs.Par D C B A)) as H87.
------------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------------- destruct H87 as [H87 H88].
exact H87.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.RT D C B C B A) as H85.
----------------------------------------------------------------------------- assert (* Cut *) (forall (B0: euclidean__axioms.Point) (D0: euclidean__axioms.Point) (E0: euclidean__axioms.Point) (G0: euclidean__axioms.Point) (H85: euclidean__axioms.Point), (euclidean__defs.Par G0 B0 H85 D0) -> ((euclidean__defs.OS B0 D0 G0 H85) -> ((euclidean__axioms.BetS E0 G0 H85) -> (euclidean__defs.RT B0 G0 H85 G0 H85 D0)))) as H85.
------------------------------------------------------------------------------ intro B0.
intro D0.
intro E0.
intro G0.
intro H85.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA E0 G0 B0 G0 H85 D0) /\ (euclidean__defs.RT B0 G0 H85 G0 H85 D0)) as __2.
------------------------------------------------------------------------------- apply (@proposition__29C.proposition__29C (B0) (D0) (E0) (G0) (H85) (__) (__0) __1).
------------------------------------------------------------------------------- destruct __2 as [__2 __3].
exact __3.
------------------------------------------------------------------------------ apply (@H85 (D) (A) (c) (C) (B) (H84) (H24) H83).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS K F C G) as H86.
------------------------------------------------------------------------------ apply (@lemma__samesideflip.lemma__samesideflip (G) (C) (K) (F) H27).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS F K C G) as H87.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS F K C G) /\ ((euclidean__defs.OS K F G C) /\ (euclidean__defs.OS F K G C))) as H87.
-------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (C) (G) (K) (F) H86).
-------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS F K C G) /\ ((euclidean__defs.OS K F G C) /\ (euclidean__defs.OS F K G C))) as H88.
--------------------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__defs.OS K F G C) /\ (euclidean__defs.OS F K G C)) as H90.
---------------------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------------------- destruct H90 as [H90 H91].
exact H88.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C G B) as H88.
-------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (G) (C) H4).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS c C G) as H89.
--------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__innertransitivity (c) (C) (G) (B) (H83) H88).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.RT F C G C G K) as H90.
---------------------------------------------------------------------------------- assert (* Cut *) (forall (B0: euclidean__axioms.Point) (D0: euclidean__axioms.Point) (E0: euclidean__axioms.Point) (G0: euclidean__axioms.Point) (H90: euclidean__axioms.Point), (euclidean__defs.Par G0 B0 H90 D0) -> ((euclidean__defs.OS B0 D0 G0 H90) -> ((euclidean__axioms.BetS E0 G0 H90) -> (euclidean__defs.RT B0 G0 H90 G0 H90 D0)))) as H90.
----------------------------------------------------------------------------------- intro B0.
intro D0.
intro E0.
intro G0.
intro H90.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA E0 G0 B0 G0 H90 D0) /\ (euclidean__defs.RT B0 G0 H90 G0 H90 D0)) as __2.
------------------------------------------------------------------------------------ apply (@proposition__29C.proposition__29C (B0) (D0) (E0) (G0) (H90) (__) (__0) __1).
------------------------------------------------------------------------------------ destruct __2 as [__2 __3].
exact __3.
----------------------------------------------------------------------------------- apply (@H90 (F) (K) (c) (C) (G) (H13) (H87) H89).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D B C) as H91.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H91.
------------------------------------------------------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC (A) (D) (B) (C) H7).
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H92.
------------------------------------------------------------------------------------- exact H91.
------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C))) as H94.
-------------------------------------------------------------------------------------- exact H93.
-------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)) as H96.
--------------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
exact H96.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D C B) as H92.
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))))) as H92.
------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (D) (B) (C) H91).
------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))))) as H93.
-------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D)))) as H95.
--------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D))) as H97.
---------------------------------------------------------------------------------------- exact H96.
---------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.nCol D C B) /\ (euclidean__axioms.nCol C B D)) as H99.
----------------------------------------------------------------------------------------- exact H98.
----------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
exact H99.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA D C B D C B) as H93.
------------------------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (D) (C) (B) H92).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C F D) as H94.
-------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (F) (C) H3).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C F) as H95.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H95.
---------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (D) H94).
---------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H96.
----------------------------------------------------------------------------------------- exact H95.
----------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D)) as H98.
------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------ destruct H98 as [H98 H99].
exact H98.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C F D) as H96.
---------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (F) (D)).
-----------------------------------------------------------------------------------------right.
right.
exact H94.

----------------------------------------------------------------------------------------- exact H95.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C D F) as H97.
----------------------------------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (C) (F) (D) H96).
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C G B) as H98.
------------------------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C G) as H99.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C B))) as H99.
-------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (G) (B) H98).
-------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C B))) as H100.
--------------------------------------------------------------------------------------------- exact H99.
--------------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C B)) as H102.
---------------------------------------------------------------------------------------------- exact H101.
---------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
exact H102.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C G B) as H100.
-------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (G) (B)).
---------------------------------------------------------------------------------------------right.
right.
exact H98.

--------------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C B G) as H101.
--------------------------------------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (C) (G) (B) H100).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D C B F C G) as H102.
---------------------------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (D) (C) (B) (D) (C) (B) (F) (G) (H93) (H97) H101).
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B A C G K) as H103.
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.RT D C B C B A) -> ((euclidean__defs.CongA D C B F C G) -> ((euclidean__defs.RT F C G C G K) -> (euclidean__defs.CongA C B A C G K)))) as H103.
------------------------------------------------------------------------------------------------ intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA C B A C G K) /\ (euclidean__defs.CongA C G K C B A)) as __2.
------------------------------------------------------------------------------------------------- apply (@lemma__supplements2.lemma__supplements2 (D) (C) (B) (C) (G) (K) (F) (C) (G) (C) (B) (A) (__) (__0) __1).
------------------------------------------------------------------------------------------------- destruct __2 as [__2 __3].
exact __2.
------------------------------------------------------------------------------------------------ apply (@H103 (H85) (H102) H90).
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C G K C B A) as H104.
------------------------------------------------------------------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (C) (B) (A) (C) (G) (K) H103).
------------------------------------------------------------------------------------------------ assert (* Cut *) (A = A) as H105.
------------------------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) A).
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H106.
-------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
---------------------------------------------------------------------------------------------------right.
left.
exact H105.

--------------------------------------------------------------------------------------------------- exact H32.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H107.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C B))) as H107.
---------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (G) (B) H98).
---------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C B))) as H108.
----------------------------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C B)) as H110.
------------------------------------------------------------------------------------------------------ exact H109.
------------------------------------------------------------------------------------------------------ destruct H110 as [H110 H111].
exact H30.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B G C) as H108.
---------------------------------------------------------------------------------------------------- exact H67.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C G) as H109.
----------------------------------------------------------------------------------------------------- exact H68.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C G K G B A) as H110.
------------------------------------------------------------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper (C) (G) (K) (C) (B) (A) (G) (A) (H104) (H109) H106).
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B G C) as H111.
------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H4.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B G) as H112.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col B C G) /\ (euclidean__axioms.Col C G B))))) as H112.
--------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (G) (C) H111).
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col B C G) /\ (euclidean__axioms.Col C G B))))) as H113.
---------------------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col B C G) /\ (euclidean__axioms.Col C G B)))) as H115.
----------------------------------------------------------------------------------------------------------- exact H114.
----------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col B C G) /\ (euclidean__axioms.Col C G B))) as H117.
------------------------------------------------------------------------------------------------------------ exact H116.
------------------------------------------------------------------------------------------------------------ destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Col B C G) /\ (euclidean__axioms.Col C G B)) as H119.
------------------------------------------------------------------------------------------------------------- exact H118.
------------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
exact H117.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C F D) as H113.
--------------------------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C F) as H114.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H114.
----------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (D) H113).
----------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H115.
------------------------------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------------------------------ destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D)) as H117.
------------------------------------------------------------------------------------------------------------- exact H116.
------------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
exact H117.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C F D) as H115.
----------------------------------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C D F) as H116.
------------------------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (C = C) as H117.
------------------------------------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) C).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C C) as H118.
-------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H117.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A F B C) as H119.
--------------------------------------------------------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 (B) (C) (C) (A) (D) (F) (H22) (H118) H116).
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP G C K F) as H120.
---------------------------------------------------------------------------------------------------------------- exact H20.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS K F G C) as H121.
----------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)))) as H121.
------------------------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------------------------ destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C))) as H123.
------------------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)) as H125.
-------------------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A D) /\ ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C)))) as H127.
--------------------------------------------------------------------------------------------------------------------- exact H21.
--------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C))) as H129.
---------------------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((~(euclidean__defs.Meet B C A D)) /\ (euclidean__defs.OS A D B C)) as H131.
----------------------------------------------------------------------------------------------------------------------- exact H130.
----------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)))) as H133.
------------------------------------------------------------------------------------------------------------------------ exact H20.
------------------------------------------------------------------------------------------------------------------------ destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.neq K F) /\ ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C))) as H135.
------------------------------------------------------------------------------------------------------------------------- exact H134.
------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((~(euclidean__defs.Meet G C K F)) /\ (euclidean__defs.OS K F G C)) as H137.
-------------------------------------------------------------------------------------------------------------------------- exact H136.
-------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq H K) /\ ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A)))) as H139.
--------------------------------------------------------------------------------------------------------------------------- exact H19.
--------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A))) as H141.
---------------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((~(euclidean__defs.Meet E A H K)) /\ (euclidean__defs.OS H K E A)) as H143.
----------------------------------------------------------------------------------------------------------------------------- exact H142.
----------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)))) as H145.
------------------------------------------------------------------------------------------------------------------------------ exact H18.
------------------------------------------------------------------------------------------------------------------------------ destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B))) as H147.
------------------------------------------------------------------------------------------------------------------------------- exact H146.
------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ (euclidean__defs.OS C D A B)) as H149.
-------------------------------------------------------------------------------------------------------------------------------- exact H148.
-------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
exact H126.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G B) as H122.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B C G) /\ ((euclidean__axioms.Col B G C) /\ ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col C G B) /\ (euclidean__axioms.Col G B C))))) as H122.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (G) H112).
------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C G) /\ ((euclidean__axioms.Col B G C) /\ ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col C G B) /\ (euclidean__axioms.Col G B C))))) as H123.
-------------------------------------------------------------------------------------------------------------------- exact H122.
-------------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col B G C) /\ ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col C G B) /\ (euclidean__axioms.Col G B C)))) as H125.
--------------------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col C G B) /\ (euclidean__axioms.Col G B C))) as H127.
---------------------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col C G B) /\ (euclidean__axioms.Col G B C)) as H129.
----------------------------------------------------------------------------------------------------------------------- exact H128.
----------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
exact H129.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C B) as H123.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H78).
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS K F C G) as H124.
-------------------------------------------------------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS K F C B) as H125.
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear (C) (G) (B) (K) (F) (H124) (H122) H123).
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS K F B C) as H126.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip (C) (B) (K) (F) H125).
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS F K B C) as H127.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS F K B C) /\ ((euclidean__defs.OS K F C B) /\ (euclidean__defs.OS F K C B))) as H127.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (B) (C) (K) (F) H126).
------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__defs.OS F K B C) /\ ((euclidean__defs.OS K F C B) /\ (euclidean__defs.OS F K C B))) as H128.
------------------------------------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__defs.OS K F C B) /\ (euclidean__defs.OS F K C B)) as H130.
-------------------------------------------------------------------------------------------------------------------------- exact H129.
-------------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
exact H128.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A K B C) as H128.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__samesidetransitive.lemma__samesidetransitive (B) (C) (A) (F) (K) (H119) H127).
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS K A B C) as H129.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS K A B C) /\ ((euclidean__defs.OS A K C B) /\ (euclidean__defs.OS K A C B))) as H129.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (B) (C) (A) (K) H128).
-------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS K A B C) /\ ((euclidean__defs.OS A K C B) /\ (euclidean__defs.OS K A C B))) as H130.
--------------------------------------------------------------------------------------------------------------------------- exact H129.
--------------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__defs.OS A K C B) /\ (euclidean__defs.OS K A C B)) as H132.
---------------------------------------------------------------------------------------------------------------------------- exact H131.
---------------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
exact H130.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C G) as H130.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B C G) /\ ((euclidean__axioms.Col C B G) /\ (euclidean__axioms.Col B G C))))) as H130.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (G) (B) H122).
--------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G C B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B C G) /\ ((euclidean__axioms.Col C B G) /\ (euclidean__axioms.Col B G C))))) as H131.
---------------------------------------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B C G) /\ ((euclidean__axioms.Col C B G) /\ (euclidean__axioms.Col B G C)))) as H133.
----------------------------------------------------------------------------------------------------------------------------- exact H132.
----------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col B C G) /\ ((euclidean__axioms.Col C B G) /\ (euclidean__axioms.Col B G C))) as H135.
------------------------------------------------------------------------------------------------------------------------------ exact H134.
------------------------------------------------------------------------------------------------------------------------------ destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col C B G) /\ (euclidean__axioms.Col B G C)) as H137.
------------------------------------------------------------------------------------------------------------------------------- exact H136.
------------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
exact H135.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS K A B G) as H131.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear (B) (C) (G) (K) (A) (H129) (H130) H107).
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS K A G B) as H132.
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip (B) (G) (K) (A) H131).
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G K B A) as H133.
----------------------------------------------------------------------------------------------------------------------------- apply (@proposition__28D.proposition__28D (K) (A) (C) (G) (B) (H98) (H110) H132).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G K A B) as H134.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par K G B A) /\ ((euclidean__defs.Par G K A B) /\ (euclidean__defs.Par K G A B))) as H134.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (G) (K) (B) (A) H133).
------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par K G B A) /\ ((euclidean__defs.Par G K A B) /\ (euclidean__defs.Par K G A B))) as H135.
-------------------------------------------------------------------------------------------------------------------------------- exact H134.
-------------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__defs.Par G K A B) /\ (euclidean__defs.Par K G A B)) as H137.
--------------------------------------------------------------------------------------------------------------------------------- exact H136.
--------------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
exact H137.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A B E) as H135.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E B A) /\ (euclidean__axioms.Col B A E))))) as H135.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (A) (B) H62).
-------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A E B) /\ ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E B A) /\ (euclidean__axioms.Col B A E))))) as H136.
--------------------------------------------------------------------------------------------------------------------------------- exact H135.
--------------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E B A) /\ (euclidean__axioms.Col B A E)))) as H138.
---------------------------------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E B A) /\ (euclidean__axioms.Col B A E))) as H140.
----------------------------------------------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Col E B A) /\ (euclidean__axioms.Col B A E)) as H142.
------------------------------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------------------------------ destruct H142 as [H142 H143].
exact H138.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G K E B) as H136.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (G) (K) (E) (A) (B) (H134) (H135) H56).
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E B G K) as H137.
--------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (G) (K) (E) (B) H136).
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E B K G) as H138.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par B E G K) /\ ((euclidean__defs.Par E B K G) /\ (euclidean__defs.Par B E K G))) as H138.
----------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (E) (B) (G) (K) H137).
----------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par B E G K) /\ ((euclidean__defs.Par E B K G) /\ (euclidean__defs.Par B E K G))) as H139.
------------------------------------------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------------------------------------------ destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__defs.Par E B K G) /\ (euclidean__defs.Par B E K G)) as H141.
------------------------------------------------------------------------------------------------------------------------------------- exact H140.
------------------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
exact H141.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG E K G B) as H139.
----------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------------------------------------------------------------------ exact H138.
----------------------------------------------------------------------------------------------------------------------------------- exact H139.
Qed.
