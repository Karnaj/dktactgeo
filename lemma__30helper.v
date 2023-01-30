Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__crisscross.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Definition lemma__30helper : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point), (euclidean__defs.Par A B E F) -> ((euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS E H F) -> ((~(euclidean__defs.CR A F G H)) -> (euclidean__defs.CR A E G H)))).
Proof.
intro A.
intro B.
intro E.
intro F.
intro G.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
assert (* Cut *) (euclidean__axioms.Col A G B) as H4.
- right.
right.
right.
right.
left.
exact H1.
- assert (* Cut *) (euclidean__axioms.Col E H F) as H5.
-- right.
right.
right.
right.
left.
exact H2.
-- assert (* Cut *) (euclidean__axioms.Col B A G) as H6.
--- assert (* Cut *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H6.
---- apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (B) H4).
---- assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A)))) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))) as H11.
------- exact H10.
------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A)) as H13.
-------- exact H12.
-------- destruct H13 as [H13 H14].
exact H11.
--- assert (* Cut *) (euclidean__axioms.Col E F H) as H7.
---- assert (* Cut *) ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E))))) as H7.
----- apply (@lemma__collinearorder.lemma__collinearorder (E) (H) (F) H5).
----- assert (* AndElim *) ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E))))) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E)))) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E))) as H12.
-------- exact H11.
-------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E)) as H14.
--------- exact H13.
--------- destruct H14 as [H14 H15].
exact H14.
---- assert (* Cut *) (euclidean__axioms.neq H F) as H8.
----- assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H8.
------ apply (@lemma__betweennotequal.lemma__betweennotequal (E) (H) (F) H2).
------ assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F)) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
exact H9.
----- assert (* Cut *) (euclidean__axioms.neq E H) as H9.
------ assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H9.
------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (H) (F) H2).
------- assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F)) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
exact H12.
------ assert (* Cut *) (euclidean__axioms.neq H E) as H10.
------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (H) H9).
------- assert (* Cut *) (euclidean__axioms.neq F H) as H11.
-------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (H) (F) H8).
-------- assert (* Cut *) (euclidean__axioms.neq A G) as H12.
--------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H12.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (G) (B) H1).
---------- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B)) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
exact H15.
--------- assert (* Cut *) (euclidean__axioms.neq G A) as H13.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (G) H12).
---------- assert (* Cut *) (euclidean__defs.Par A B F E) as H14.
----------- assert (* Cut *) ((euclidean__defs.Par B A E F) /\ ((euclidean__defs.Par A B F E) /\ (euclidean__defs.Par B A F E))) as H14.
------------ apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (E) (F) H0).
------------ assert (* AndElim *) ((euclidean__defs.Par B A E F) /\ ((euclidean__defs.Par A B F E) /\ (euclidean__defs.Par B A F E))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__defs.Par A B F E) /\ (euclidean__defs.Par B A F E)) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
exact H17.
----------- assert (* Cut *) (euclidean__axioms.Col F E H) as H15.
------------ assert (* Cut *) ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col F H E) /\ ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col E H F) /\ (euclidean__axioms.Col H F E))))) as H15.
------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (H) H7).
------------- assert (* AndElim *) ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col F H E) /\ ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col E H F) /\ (euclidean__axioms.Col H F E))))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col F H E) /\ ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col E H F) /\ (euclidean__axioms.Col H F E)))) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col E H F) /\ (euclidean__axioms.Col H F E))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col E H F) /\ (euclidean__axioms.Col H F E)) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
exact H16.
------------ assert (* Cut *) (euclidean__defs.Par A B H E) as H16.
------------- apply (@lemma__collinearparallel.lemma__collinearparallel (A) (B) (H) (F) (E) (H14) (H15) H10).
------------- assert (* Cut *) (euclidean__defs.Par A B H F) as H17.
-------------- apply (@lemma__collinearparallel.lemma__collinearparallel (A) (B) (H) (E) (F) (H0) (H7) H8).
-------------- assert (* Cut *) (euclidean__defs.Par H F A B) as H18.
--------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (B) (H) (F) H17).
--------------- assert (* Cut *) (euclidean__defs.Par H F B A) as H19.
---------------- assert (* Cut *) ((euclidean__defs.Par F H A B) /\ ((euclidean__defs.Par H F B A) /\ (euclidean__defs.Par F H B A))) as H19.
----------------- apply (@lemma__parallelflip.lemma__parallelflip (H) (F) (A) (B) H18).
----------------- assert (* AndElim *) ((euclidean__defs.Par F H A B) /\ ((euclidean__defs.Par H F B A) /\ (euclidean__defs.Par F H B A))) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__defs.Par H F B A) /\ (euclidean__defs.Par F H B A)) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
exact H22.
---------------- assert (* Cut *) (euclidean__defs.Par H F G A) as H20.
----------------- apply (@lemma__collinearparallel.lemma__collinearparallel (H) (F) (G) (B) (A) (H19) (H6) H13).
----------------- assert (* Cut *) (euclidean__defs.Par H F A G) as H21.
------------------ assert (* Cut *) ((euclidean__defs.Par F H G A) /\ ((euclidean__defs.Par H F A G) /\ (euclidean__defs.Par F H A G))) as H21.
------------------- apply (@lemma__parallelflip.lemma__parallelflip (H) (F) (G) (A) H20).
------------------- assert (* AndElim *) ((euclidean__defs.Par F H G A) /\ ((euclidean__defs.Par H F A G) /\ (euclidean__defs.Par F H A G))) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.Par H F A G) /\ (euclidean__defs.Par F H A G)) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [H24 H25].
exact H24.
------------------ assert (* Cut *) (euclidean__defs.Par A G H F) as H22.
------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (H) (F) (A) (G) H21).
------------------- assert (* Cut *) (euclidean__defs.Par A G F H) as H23.
-------------------- assert (* Cut *) ((euclidean__defs.Par G A H F) /\ ((euclidean__defs.Par A G F H) /\ (euclidean__defs.Par G A F H))) as H23.
--------------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (G) (H) (F) H22).
--------------------- assert (* AndElim *) ((euclidean__defs.Par G A H F) /\ ((euclidean__defs.Par A G F H) /\ (euclidean__defs.Par G A F H))) as H24.
---------------------- exact H23.
---------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__defs.Par A G F H) /\ (euclidean__defs.Par G A F H)) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [H26 H27].
exact H26.
-------------------- assert (* Cut *) (euclidean__defs.CR A H F G) as H24.
--------------------- apply (@lemma__crisscross.lemma__crisscross (A) (F) (G) (H) (H23) H3).
--------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M H) /\ (euclidean__axioms.BetS F M G)) as H25.
---------------------- exact H24.
---------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M H) /\ (euclidean__axioms.BetS F M G))) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [M H26].
assert (* AndElim *) ((euclidean__axioms.BetS A M H) /\ (euclidean__axioms.BetS F M G)) as H27.
------------------------ exact H26.
------------------------ destruct H27 as [H27 H28].
assert (* Cut *) (euclidean__axioms.neq A H) as H29.
------------------------- assert (* Cut *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A H))) as H29.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (M) (H) H27).
-------------------------- assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A H))) as H30.
--------------------------- exact H29.
--------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A H)) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [H32 H33].
exact H33.
------------------------- assert (* Cut *) (euclidean__axioms.neq F G) as H30.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq M G) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F G))) as H30.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (M) (G) H28).
--------------------------- assert (* AndElim *) ((euclidean__axioms.neq M G) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F G))) as H31.
---------------------------- exact H30.
---------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F G)) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
exact H34.
-------------------------- assert (* Cut *) (euclidean__axioms.BetS G M F) as H31.
--------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (F) (M) (G) H28).
--------------------------- assert (* Cut *) (euclidean__axioms.nCol A E F) as H32.
---------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol A E F) /\ ((euclidean__axioms.nCol B E F) /\ (euclidean__axioms.nCol A B F)))) as H32.
----------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (E) (F) H0).
----------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol A E F) /\ ((euclidean__axioms.nCol B E F) /\ (euclidean__axioms.nCol A B F)))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.nCol A E F) /\ ((euclidean__axioms.nCol B E F) /\ (euclidean__axioms.nCol A B F))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.nCol B E F) /\ (euclidean__axioms.nCol A B F)) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
exact H35.
---------------------------- assert (* Cut *) (euclidean__axioms.nCol F E A) as H33.
----------------------------- assert (* Cut *) ((euclidean__axioms.nCol E A F) /\ ((euclidean__axioms.nCol E F A) /\ ((euclidean__axioms.nCol F A E) /\ ((euclidean__axioms.nCol A F E) /\ (euclidean__axioms.nCol F E A))))) as H33.
------------------------------ apply (@lemma__NCorder.lemma__NCorder (A) (E) (F) H32).
------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol E A F) /\ ((euclidean__axioms.nCol E F A) /\ ((euclidean__axioms.nCol F A E) /\ ((euclidean__axioms.nCol A F E) /\ (euclidean__axioms.nCol F E A))))) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.nCol E F A) /\ ((euclidean__axioms.nCol F A E) /\ ((euclidean__axioms.nCol A F E) /\ (euclidean__axioms.nCol F E A)))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.nCol F A E) /\ ((euclidean__axioms.nCol A F E) /\ (euclidean__axioms.nCol F E A))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.nCol A F E) /\ (euclidean__axioms.nCol F E A)) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
exact H41.
----------------------------- assert (* Cut *) (euclidean__axioms.BetS F H E) as H34.
------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (H) (F) H2).
------------------------------ assert (* Cut *) (exists (p: euclidean__axioms.Point), (euclidean__axioms.BetS A p E) /\ (euclidean__axioms.BetS F M p)) as H35.
------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (A) (F) (H) (M) (E) (H27) (H34) H33).
------------------------------- assert (exists p: euclidean__axioms.Point, ((euclidean__axioms.BetS A p E) /\ (euclidean__axioms.BetS F M p))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [p H36].
assert (* AndElim *) ((euclidean__axioms.BetS A p E) /\ (euclidean__axioms.BetS F M p)) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
assert (* Cut *) (euclidean__axioms.nCol A G H) as H39.
---------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A G F) /\ ((euclidean__axioms.nCol A F H) /\ ((euclidean__axioms.nCol G F H) /\ (euclidean__axioms.nCol A G H)))) as H39.
----------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (G) (F) (H) H23).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A G F) /\ ((euclidean__axioms.nCol A F H) /\ ((euclidean__axioms.nCol G F H) /\ (euclidean__axioms.nCol A G H)))) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.nCol A F H) /\ ((euclidean__axioms.nCol G F H) /\ (euclidean__axioms.nCol A G H))) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.nCol G F H) /\ (euclidean__axioms.nCol A G H)) as H44.
-------------------------------------- exact H43.
-------------------------------------- destruct H44 as [H44 H45].
exact H45.
---------------------------------- assert (* Cut *) (euclidean__axioms.nCol A H G) as H40.
----------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G A H) /\ ((euclidean__axioms.nCol G H A) /\ ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A))))) as H40.
------------------------------------ apply (@lemma__NCorder.lemma__NCorder (A) (G) (H) H39).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol G A H) /\ ((euclidean__axioms.nCol G H A) /\ ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A))))) as H41.
------------------------------------- exact H40.
------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.nCol G H A) /\ ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A)))) as H43.
-------------------------------------- exact H42.
-------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A))) as H45.
--------------------------------------- exact H44.
--------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A)) as H47.
---------------------------------------- exact H46.
---------------------------------------- destruct H47 as [H47 H48].
exact H47.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col F M G) as H41.
------------------------------------ right.
right.
right.
right.
left.
exact H28.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col F M p) as H42.
------------------------------------- right.
right.
right.
right.
left.
exact H38.
------------------------------------- assert (* Cut *) (euclidean__axioms.neq F M) as H43.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M p) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p))) as H43.
--------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (M) (p) H38).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M p) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p))) as H44.
---------------------------------------- exact H43.
---------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p)) as H46.
----------------------------------------- exact H45.
----------------------------------------- destruct H46 as [H46 H47].
exact H46.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col M G p) as H44.
--------------------------------------- apply (@euclidean__tactics.not__nCol__Col (M) (G) (p)).
----------------------------------------intro H44.
apply (@euclidean__tactics.Col__nCol__False (M) (G) (p) (H44)).
-----------------------------------------apply (@lemma__collinear4.lemma__collinear4 (F) (M) (G) (p) (H41) (H42) H43).


--------------------------------------- assert (* Cut *) (euclidean__axioms.Col M p G) as H45.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G M p) /\ ((euclidean__axioms.Col G p M) /\ ((euclidean__axioms.Col p M G) /\ ((euclidean__axioms.Col M p G) /\ (euclidean__axioms.Col p G M))))) as H45.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (M) (G) (p) H44).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G M p) /\ ((euclidean__axioms.Col G p M) /\ ((euclidean__axioms.Col p M G) /\ ((euclidean__axioms.Col M p G) /\ (euclidean__axioms.Col p G M))))) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col G p M) /\ ((euclidean__axioms.Col p M G) /\ ((euclidean__axioms.Col M p G) /\ (euclidean__axioms.Col p G M)))) as H48.
------------------------------------------- exact H47.
------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col p M G) /\ ((euclidean__axioms.Col M p G) /\ (euclidean__axioms.Col p G M))) as H50.
-------------------------------------------- exact H49.
-------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col M p G) /\ (euclidean__axioms.Col p G M)) as H52.
--------------------------------------------- exact H51.
--------------------------------------------- destruct H52 as [H52 H53].
exact H52.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col M p F) as H46.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M F p) /\ ((euclidean__axioms.Col M p F) /\ ((euclidean__axioms.Col p F M) /\ ((euclidean__axioms.Col F p M) /\ (euclidean__axioms.Col p M F))))) as H46.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (F) (M) (p) H42).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col M F p) /\ ((euclidean__axioms.Col M p F) /\ ((euclidean__axioms.Col p F M) /\ ((euclidean__axioms.Col F p M) /\ (euclidean__axioms.Col p M F))))) as H47.
------------------------------------------- exact H46.
------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col M p F) /\ ((euclidean__axioms.Col p F M) /\ ((euclidean__axioms.Col F p M) /\ (euclidean__axioms.Col p M F)))) as H49.
-------------------------------------------- exact H48.
-------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col p F M) /\ ((euclidean__axioms.Col F p M) /\ (euclidean__axioms.Col p M F))) as H51.
--------------------------------------------- exact H50.
--------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col F p M) /\ (euclidean__axioms.Col p M F)) as H53.
---------------------------------------------- exact H52.
---------------------------------------------- destruct H53 as [H53 H54].
exact H49.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq M p) as H47.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq M p) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p))) as H47.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (M) (p) H38).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M p) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p))) as H48.
-------------------------------------------- exact H47.
-------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p)) as H50.
--------------------------------------------- exact H49.
--------------------------------------------- destruct H50 as [H50 H51].
exact H48.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col p G F) as H48.
------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (p) (G) (F)).
--------------------------------------------intro H48.
apply (@euclidean__tactics.Col__nCol__False (p) (G) (F) (H48)).
---------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (M) (p) (G) (F) (H45) (H46) H47).


------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G F p) as H49.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G p F) /\ ((euclidean__axioms.Col G F p) /\ ((euclidean__axioms.Col F p G) /\ ((euclidean__axioms.Col p F G) /\ (euclidean__axioms.Col F G p))))) as H49.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (p) (G) (F) H48).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G p F) /\ ((euclidean__axioms.Col G F p) /\ ((euclidean__axioms.Col F p G) /\ ((euclidean__axioms.Col p F G) /\ (euclidean__axioms.Col F G p))))) as H50.
---------------------------------------------- exact H49.
---------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col G F p) /\ ((euclidean__axioms.Col F p G) /\ ((euclidean__axioms.Col p F G) /\ (euclidean__axioms.Col F G p)))) as H52.
----------------------------------------------- exact H51.
----------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col F p G) /\ ((euclidean__axioms.Col p F G) /\ (euclidean__axioms.Col F G p))) as H54.
------------------------------------------------ exact H53.
------------------------------------------------ destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col p F G) /\ (euclidean__axioms.Col F G p)) as H56.
------------------------------------------------- exact H55.
------------------------------------------------- destruct H56 as [H56 H57].
exact H52.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H F E) as H50.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E F H) /\ ((euclidean__axioms.Col E H F) /\ ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F H E) /\ (euclidean__axioms.Col H E F))))) as H50.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (E) (H) H15).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E F H) /\ ((euclidean__axioms.Col E H F) /\ ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F H E) /\ (euclidean__axioms.Col H E F))))) as H51.
----------------------------------------------- exact H50.
----------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col E H F) /\ ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F H E) /\ (euclidean__axioms.Col H E F)))) as H53.
------------------------------------------------ exact H52.
------------------------------------------------ destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F H E) /\ (euclidean__axioms.Col H E F))) as H55.
------------------------------------------------- exact H54.
------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col F H E) /\ (euclidean__axioms.Col H E F)) as H57.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H57 as [H57 H58].
exact H55.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A B) as H51.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H51.
----------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (G) (B) H1).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H52.
------------------------------------------------ exact H51.
------------------------------------------------ destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B)) as H54.
------------------------------------------------- exact H53.
------------------------------------------------- destruct H54 as [H54 H55].
exact H55.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A G) as H52.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M p) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p))) as H52.
------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (F) (M) (p) H38).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq M p) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p))) as H53.
------------------------------------------------- exact H52.
------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p)) as H55.
-------------------------------------------------- exact H54.
-------------------------------------------------- destruct H55 as [H55 H56].
exact H12.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E F) as H53.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H53.
------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (H) (F) H2).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H54.
-------------------------------------------------- exact H53.
-------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F)) as H56.
--------------------------------------------------- exact H55.
--------------------------------------------------- destruct H56 as [H56 H57].
exact H57.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq F E) as H54.
------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (F) H53).
------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B H E)) as H55.
-------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H55.
--------------------------------------------------- exact H23.
--------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
---------------------------------------------------- exact H55.
---------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H56.
----------------------------------------------------- exact __TmpHyp.
----------------------------------------------------- destruct H56 as [x H56].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H57.
------------------------------------------------------ exact H56.
------------------------------------------------------ destruct H57 as [x0 H57].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H58.
------------------------------------------------------- exact H57.
------------------------------------------------------- destruct H58 as [x1 H58].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H59.
-------------------------------------------------------- exact H58.
-------------------------------------------------------- destruct H59 as [x2 H59].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H60.
--------------------------------------------------------- exact H59.
--------------------------------------------------------- destruct H60 as [x3 H60].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H61.
---------------------------------------------------------- exact H60.
---------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H63.
----------------------------------------------------------- exact H62.
----------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H65.
------------------------------------------------------------ exact H64.
------------------------------------------------------------ destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H67.
------------------------------------------------------------- exact H66.
------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H69.
-------------------------------------------------------------- exact H68.
-------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H71.
--------------------------------------------------------------- exact H70.
--------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H73.
---------------------------------------------------------------- exact H72.
---------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H75.
----------------------------------------------------------------- exact H74.
----------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H77.
------------------------------------------------------------------ exact H76.
------------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H79.
------------------------------------------------------------------- exact H78.
------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H81.
-------------------------------------------------------------------- exact H22.
-------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
--------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H82.
---------------------------------------------------------------------- exact __TmpHyp0.
---------------------------------------------------------------------- destruct H82 as [x4 H82].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x4) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H83.
----------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------- destruct H83 as [x5 H83].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x4) /\ ((euclidean__axioms.Col A G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H84.
------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------ destruct H84 as [x6 H84].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x4) /\ ((euclidean__axioms.Col A G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H85.
------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------- destruct H85 as [x7 H85].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x4) /\ ((euclidean__axioms.Col A G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H86.
-------------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------------- destruct H86 as [x8 H86].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x4) /\ ((euclidean__axioms.Col A G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H87.
--------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x4) /\ ((euclidean__axioms.Col A G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H89.
---------------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col A G x4) /\ ((euclidean__axioms.Col A G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H91.
----------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col A G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H93.
------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------ destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H95.
------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H97.
-------------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H99.
--------------------------------------------------------------------------------- exact H98.
--------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H101.
---------------------------------------------------------------------------------- exact H100.
---------------------------------------------------------------------------------- destruct H101 as [H101 H102].
assert (* AndElim *) ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H103.
----------------------------------------------------------------------------------- exact H102.
----------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H105.
------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------ destruct H105 as [H105 H106].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H107.
------------------------------------------------------------------------------------- exact H21.
------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
-------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H108.
--------------------------------------------------------------------------------------- exact __TmpHyp1.
--------------------------------------------------------------------------------------- destruct H108 as [x9 H108].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H109.
---------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------- destruct H109 as [x10 H109].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H110.
----------------------------------------------------------------------------------------- exact H109.
----------------------------------------------------------------------------------------- destruct H110 as [x11 H110].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H111.
------------------------------------------------------------------------------------------ exact H110.
------------------------------------------------------------------------------------------ destruct H111 as [x12 H111].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H112.
------------------------------------------------------------------------------------------- exact H111.
------------------------------------------------------------------------------------------- destruct H112 as [x13 H112].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H113.
-------------------------------------------------------------------------------------------- exact H112.
-------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H115.
--------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H117.
---------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H119.
----------------------------------------------------------------------------------------------- exact H118.
----------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H121.
------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------ destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col A G x11) /\ ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H123.
------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col A G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H125.
-------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H127.
--------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H129.
---------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H131.
----------------------------------------------------------------------------------------------------- exact H130.
----------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H133.
------------------------------------------------------------------------------------------------------ exact H20.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
------------------------------------------------------------------------------------------------------- exact H133.
------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H134.
-------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
-------------------------------------------------------------------------------------------------------- destruct H134 as [x14 H134].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x14) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H135.
--------------------------------------------------------------------------------------------------------- exact H134.
--------------------------------------------------------------------------------------------------------- destruct H135 as [x15 H135].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x14) /\ ((euclidean__axioms.Col H F x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H136.
---------------------------------------------------------------------------------------------------------- exact H135.
---------------------------------------------------------------------------------------------------------- destruct H136 as [x16 H136].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x14) /\ ((euclidean__axioms.Col H F x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col G A x16) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H137.
----------------------------------------------------------------------------------------------------------- exact H136.
----------------------------------------------------------------------------------------------------------- destruct H137 as [x17 H137].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x14) /\ ((euclidean__axioms.Col H F x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col G A x16) /\ ((euclidean__axioms.Col G A x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H138.
------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------ destruct H138 as [x18 H138].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x14) /\ ((euclidean__axioms.Col H F x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col G A x16) /\ ((euclidean__axioms.Col G A x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H139.
------------------------------------------------------------------------------------------------------------- exact H138.
------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x14) /\ ((euclidean__axioms.Col H F x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col G A x16) /\ ((euclidean__axioms.Col G A x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H141.
-------------------------------------------------------------------------------------------------------------- exact H140.
-------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Col H F x14) /\ ((euclidean__axioms.Col H F x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col G A x16) /\ ((euclidean__axioms.Col G A x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H143.
--------------------------------------------------------------------------------------------------------------- exact H142.
--------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Col H F x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col G A x16) /\ ((euclidean__axioms.Col G A x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H145.
---------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col G A x16) /\ ((euclidean__axioms.Col G A x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H147.
----------------------------------------------------------------------------------------------------------------- exact H146.
----------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.Col G A x16) /\ ((euclidean__axioms.Col G A x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H149.
------------------------------------------------------------------------------------------------------------------ exact H148.
------------------------------------------------------------------------------------------------------------------ destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.Col G A x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H151.
------------------------------------------------------------------------------------------------------------------- exact H150.
------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H153.
-------------------------------------------------------------------------------------------------------------------- exact H152.
-------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H155.
--------------------------------------------------------------------------------------------------------------------- exact H154.
--------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H157.
---------------------------------------------------------------------------------------------------------------------- exact H156.
---------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H159.
----------------------------------------------------------------------------------------------------------------------- exact H19.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H160.
------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------- destruct H160 as [x19 H160].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x19) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H161.
-------------------------------------------------------------------------------------------------------------------------- exact H160.
-------------------------------------------------------------------------------------------------------------------------- destruct H161 as [x20 H161].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x19) /\ ((euclidean__axioms.Col H F x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H162.
--------------------------------------------------------------------------------------------------------------------------- exact H161.
--------------------------------------------------------------------------------------------------------------------------- destruct H162 as [x21 H162].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x19) /\ ((euclidean__axioms.Col H F x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B A x21) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H163.
---------------------------------------------------------------------------------------------------------------------------- exact H162.
---------------------------------------------------------------------------------------------------------------------------- destruct H163 as [x22 H163].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x19) /\ ((euclidean__axioms.Col H F x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B A x21) /\ ((euclidean__axioms.Col B A x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H164.
----------------------------------------------------------------------------------------------------------------------------- exact H163.
----------------------------------------------------------------------------------------------------------------------------- destruct H164 as [x23 H164].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x19) /\ ((euclidean__axioms.Col H F x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B A x21) /\ ((euclidean__axioms.Col B A x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H165.
------------------------------------------------------------------------------------------------------------------------------ exact H164.
------------------------------------------------------------------------------------------------------------------------------ destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x19) /\ ((euclidean__axioms.Col H F x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B A x21) /\ ((euclidean__axioms.Col B A x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H167.
------------------------------------------------------------------------------------------------------------------------------- exact H166.
------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.Col H F x19) /\ ((euclidean__axioms.Col H F x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B A x21) /\ ((euclidean__axioms.Col B A x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H169.
-------------------------------------------------------------------------------------------------------------------------------- exact H168.
-------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.Col H F x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B A x21) /\ ((euclidean__axioms.Col B A x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H171.
--------------------------------------------------------------------------------------------------------------------------------- exact H170.
--------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col B A x21) /\ ((euclidean__axioms.Col B A x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H173.
---------------------------------------------------------------------------------------------------------------------------------- exact H172.
---------------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.Col B A x21) /\ ((euclidean__axioms.Col B A x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H175.
----------------------------------------------------------------------------------------------------------------------------------- exact H174.
----------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__axioms.Col B A x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H177.
------------------------------------------------------------------------------------------------------------------------------------ exact H176.
------------------------------------------------------------------------------------------------------------------------------------ destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H179.
------------------------------------------------------------------------------------------------------------------------------------- exact H178.
------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H181.
-------------------------------------------------------------------------------------------------------------------------------------- exact H180.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H183.
--------------------------------------------------------------------------------------------------------------------------------------- exact H182.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H185.
---------------------------------------------------------------------------------------------------------------------------------------- exact H18.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
----------------------------------------------------------------------------------------------------------------------------------------- exact H185.
----------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H186.
------------------------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp4.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H186 as [x24 H186].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H187.
------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [x25 H187].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H188.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [x26 H188].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A B x26) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H189.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [x27 H189].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A B x26) /\ ((euclidean__axioms.Col A B x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H190.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [x28 H190].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A B x26) /\ ((euclidean__axioms.Col A B x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H191.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A B x26) /\ ((euclidean__axioms.Col A B x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H193.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H192.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A B x26) /\ ((euclidean__axioms.Col A B x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A B x26) /\ ((euclidean__axioms.Col A B x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H197.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A B x26) /\ ((euclidean__axioms.Col A B x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H199.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [H199 H200].
assert (* AndElim *) ((euclidean__axioms.Col A B x26) /\ ((euclidean__axioms.Col A B x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H201.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [H201 H202].
assert (* AndElim *) ((euclidean__axioms.Col A B x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H203.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H202.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [H203 H204].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H205.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H204.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H205 as [H205 H206].
assert (* AndElim *) ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H207.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H206.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H207 as [H207 H208].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H209.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [H209 H210].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H211.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H17.
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H211.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H212.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp5.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [x29 H212].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x29 V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H213 as [x30 H213].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X x30)))))))))))) as H214.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [x31 H214].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col H F x31) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq x31 v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H215.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [x32 H215].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col H F x31) /\ ((euclidean__axioms.Col H F x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 X x32) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H216.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H216 as [x33 H216].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col H F x31) /\ ((euclidean__axioms.Col H F x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))))) as H217.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H216.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H217 as [H217 H218].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col H F x31) /\ ((euclidean__axioms.Col H F x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))))) as H219.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H218.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H219 as [H219 H220].
assert (* AndElim *) ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col H F x31) /\ ((euclidean__axioms.Col H F x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))) as H221.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H220.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col H F x31) /\ ((euclidean__axioms.Col H F x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))) as H223.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H222.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H223 as [H223 H224].
assert (* AndElim *) ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col H F x31) /\ ((euclidean__axioms.Col H F x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))) as H225.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H224.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H225 as [H225 H226].
assert (* AndElim *) ((euclidean__axioms.Col H F x31) /\ ((euclidean__axioms.Col H F x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))) as H227.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H226.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H227 as [H227 H228].
assert (* AndElim *) ((euclidean__axioms.Col H F x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))) as H229.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H228.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [H229 H230].
assert (* AndElim *) ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))) as H231.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [H231 H232].
assert (* AndElim *) ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))) as H233.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H232.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H233 as [H233 H234].
assert (* AndElim *) ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)) as H235.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H234.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H235 as [H235 H236].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H237.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H16.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H237.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H238.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp6.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H238 as [x34 H238].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x34 V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H239.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H238.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H239 as [x35 H239].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS u X x35)))))))))))) as H240.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H239.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H240 as [x36 H240].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col H E x36) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq x36 v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS x36 X x35)))))))))))) as H241.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H240.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H241 as [x37 H241].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col H E x36) /\ ((euclidean__axioms.Col H E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 X x37) /\ (euclidean__axioms.BetS x36 X x35)))))))))))) as H242.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H241.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H242 as [x38 H242].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col H E x36) /\ ((euclidean__axioms.Col H E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))))))) as H243.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H242.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H243 as [H243 H244].
assert (* AndElim *) ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col H E x36) /\ ((euclidean__axioms.Col H E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))))))) as H245.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H244.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H245 as [H245 H246].
assert (* AndElim *) ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col H E x36) /\ ((euclidean__axioms.Col H E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))))) as H247.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H246.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H247 as [H247 H248].
assert (* AndElim *) ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col H E x36) /\ ((euclidean__axioms.Col H E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))))) as H249.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H248.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H249 as [H249 H250].
assert (* AndElim *) ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col H E x36) /\ ((euclidean__axioms.Col H E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))) as H251.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H250.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H251 as [H251 H252].
assert (* AndElim *) ((euclidean__axioms.Col H E x36) /\ ((euclidean__axioms.Col H E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))) as H253.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H252.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H253 as [H253 H254].
assert (* AndElim *) ((euclidean__axioms.Col H E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))) as H255.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H254.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H255 as [H255 H256].
assert (* AndElim *) ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))) as H257.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H256.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H257 as [H257 H258].
assert (* AndElim *) ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))) as H259.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H258.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H259 as [H259 H260].
assert (* AndElim *) ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)) as H261.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H260.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H261 as [H261 H262].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H263.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H14.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H263.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H264.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp7.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H264 as [x39 H264].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x39 V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H265.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H264.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H265 as [x40 H265].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS u X x40)))))))))))) as H266.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H265.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H266 as [x41 H266].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col F E x41) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq x41 v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS x41 X x40)))))))))))) as H267.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H266.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H267 as [x42 H267].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col F E x41) /\ ((euclidean__axioms.Col F E x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 X x42) /\ (euclidean__axioms.BetS x41 X x40)))))))))))) as H268.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H267.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H268 as [x43 H268].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col F E x41) /\ ((euclidean__axioms.Col F E x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))))))) as H269.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H268.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H269 as [H269 H270].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col F E x41) /\ ((euclidean__axioms.Col F E x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))))))) as H271.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H270.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H271 as [H271 H272].
assert (* AndElim *) ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col F E x41) /\ ((euclidean__axioms.Col F E x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))))) as H273.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H272.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H273 as [H273 H274].
assert (* AndElim *) ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col F E x41) /\ ((euclidean__axioms.Col F E x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))))) as H275.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H274.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H275 as [H275 H276].
assert (* AndElim *) ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col F E x41) /\ ((euclidean__axioms.Col F E x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))) as H277.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H276.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H277 as [H277 H278].
assert (* AndElim *) ((euclidean__axioms.Col F E x41) /\ ((euclidean__axioms.Col F E x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))) as H279.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H278.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H279 as [H279 H280].
assert (* AndElim *) ((euclidean__axioms.Col F E x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))) as H281.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H280.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H281 as [H281 H282].
assert (* AndElim *) ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))) as H283.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H282.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H283 as [H283 H284].
assert (* AndElim *) ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))) as H285.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H284.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H285 as [H285 H286].
assert (* AndElim *) ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)) as H287.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H286.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H287 as [H287 H288].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H289.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H0.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H289.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H290.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp8.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H290 as [x44 H290].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x44 V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H291.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H290.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H291 as [x45 H291].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 X v) /\ (euclidean__axioms.BetS u X x45)))))))))))) as H292.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H291.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H292 as [x46 H292].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col E F x46) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq x46 v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 X v) /\ (euclidean__axioms.BetS x46 X x45)))))))))))) as H293.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H292.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H293 as [x47 H293].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col E F x46) /\ ((euclidean__axioms.Col E F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 X x47) /\ (euclidean__axioms.BetS x46 X x45)))))))))))) as H294.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H293.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H294 as [x48 H294].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col E F x46) /\ ((euclidean__axioms.Col E F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))))))))) as H295.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H294.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H295 as [H295 H296].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col E F x46) /\ ((euclidean__axioms.Col E F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))))))))) as H297.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H296.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H297 as [H297 H298].
assert (* AndElim *) ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col E F x46) /\ ((euclidean__axioms.Col E F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))))))) as H299.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H298.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H299 as [H299 H300].
assert (* AndElim *) ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col E F x46) /\ ((euclidean__axioms.Col E F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))))))) as H301.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H300.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H301 as [H301 H302].
assert (* AndElim *) ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col E F x46) /\ ((euclidean__axioms.Col E F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))))) as H303.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H302.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H303 as [H303 H304].
assert (* AndElim *) ((euclidean__axioms.Col E F x46) /\ ((euclidean__axioms.Col E F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))))) as H305.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H304.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H305 as [H305 H306].
assert (* AndElim *) ((euclidean__axioms.Col E F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))) as H307.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H306.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H307 as [H307 H308].
assert (* AndElim *) ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))) as H309.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H308.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H309 as [H309 H310].
assert (* AndElim *) ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))) as H311.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H310.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H311 as [H311 H312].
assert (* AndElim *) ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)) as H313.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H312.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H313 as [H313 H314].
exact H259.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G p F) as H56.
--------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (A) (B) (H) (E) (G) (F) (p) (H4) (H50) (H51) (H10) (H52) (H54) (H55) (H37) H49).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F p G) as H57.
---------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (p) (F) H56).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS M p G) as H58.
----------------------------------------------------- apply (@lemma__3__6a.lemma__3__6a (F) (M) (p) (G) (H38) H57).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G p M) as H59.
------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (M) (p) (G) H58).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A G H) as H60.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A G F) /\ ((euclidean__axioms.nCol A F H) /\ ((euclidean__axioms.nCol G F H) /\ (euclidean__axioms.nCol A G H)))) as H60.
-------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (G) (F) (H) H23).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A G F) /\ ((euclidean__axioms.nCol A F H) /\ ((euclidean__axioms.nCol G F H) /\ (euclidean__axioms.nCol A G H)))) as H61.
--------------------------------------------------------- exact H60.
--------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.nCol A F H) /\ ((euclidean__axioms.nCol G F H) /\ (euclidean__axioms.nCol A G H))) as H63.
---------------------------------------------------------- exact H62.
---------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.nCol G F H) /\ (euclidean__axioms.nCol A G H)) as H65.
----------------------------------------------------------- exact H64.
----------------------------------------------------------- destruct H65 as [H65 H66].
exact H39.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A H G) as H61.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G A H) /\ ((euclidean__axioms.nCol G H A) /\ ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A))))) as H61.
--------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (G) (H) H60).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol G A H) /\ ((euclidean__axioms.nCol G H A) /\ ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A))))) as H62.
---------------------------------------------------------- exact H61.
---------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.nCol G H A) /\ ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A)))) as H64.
----------------------------------------------------------- exact H63.
----------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A))) as H66.
------------------------------------------------------------ exact H65.
------------------------------------------------------------ destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A)) as H68.
------------------------------------------------------------- exact H67.
------------------------------------------------------------- destruct H68 as [H68 H69].
exact H68.
-------------------------------------------------------- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS G m H) /\ (euclidean__axioms.BetS A p m)) as H62.
--------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (G) (A) (M) (p) (H) (H59) (H27) H61).
--------------------------------------------------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS G m H) /\ (euclidean__axioms.BetS A p m))) as H63.
---------------------------------------------------------- exact H62.
---------------------------------------------------------- destruct H63 as [m H63].
assert (* AndElim *) ((euclidean__axioms.BetS G m H) /\ (euclidean__axioms.BetS A p m)) as H64.
----------------------------------------------------------- exact H63.
----------------------------------------------------------- destruct H64 as [H64 H65].
assert (* Cut *) (euclidean__axioms.Col A p m) as H66.
------------------------------------------------------------ right.
right.
right.
right.
left.
exact H65.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A p E) as H67.
------------------------------------------------------------- right.
right.
right.
right.
left.
exact H37.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A p) as H68.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq p m) /\ ((euclidean__axioms.neq A p) /\ (euclidean__axioms.neq A m))) as H68.
--------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (p) (m) H65).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq p m) /\ ((euclidean__axioms.neq A p) /\ (euclidean__axioms.neq A m))) as H69.
---------------------------------------------------------------- exact H68.
---------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.neq A p) /\ (euclidean__axioms.neq A m)) as H71.
----------------------------------------------------------------- exact H70.
----------------------------------------------------------------- destruct H71 as [H71 H72].
exact H71.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p m E) as H69.
--------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (p) (m) (E)).
----------------------------------------------------------------intro H69.
apply (@euclidean__tactics.Col__nCol__False (p) (m) (E) (H69)).
-----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (p) (m) (E) (H66) (H67) H68).


--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p m A) as H70.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p A m) /\ ((euclidean__axioms.Col p m A) /\ ((euclidean__axioms.Col m A p) /\ ((euclidean__axioms.Col A m p) /\ (euclidean__axioms.Col m p A))))) as H70.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (p) (m) H66).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p A m) /\ ((euclidean__axioms.Col p m A) /\ ((euclidean__axioms.Col m A p) /\ ((euclidean__axioms.Col A m p) /\ (euclidean__axioms.Col m p A))))) as H71.
------------------------------------------------------------------ exact H70.
------------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col p m A) /\ ((euclidean__axioms.Col m A p) /\ ((euclidean__axioms.Col A m p) /\ (euclidean__axioms.Col m p A)))) as H73.
------------------------------------------------------------------- exact H72.
------------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col m A p) /\ ((euclidean__axioms.Col A m p) /\ (euclidean__axioms.Col m p A))) as H75.
-------------------------------------------------------------------- exact H74.
-------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col A m p) /\ (euclidean__axioms.Col m p A)) as H77.
--------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------- destruct H77 as [H77 H78].
exact H73.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq p m) as H71.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq p m) /\ ((euclidean__axioms.neq A p) /\ (euclidean__axioms.neq A m))) as H71.
------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (p) (m) H65).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq p m) /\ ((euclidean__axioms.neq A p) /\ (euclidean__axioms.neq A m))) as H72.
------------------------------------------------------------------- exact H71.
------------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.neq A p) /\ (euclidean__axioms.neq A m)) as H74.
-------------------------------------------------------------------- exact H73.
-------------------------------------------------------------------- destruct H74 as [H74 H75].
exact H72.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m E A) as H72.
------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (m) (E) (A)).
-------------------------------------------------------------------intro H72.
apply (@euclidean__tactics.Col__nCol__False (m) (E) (A) (H72)).
--------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (p) (m) (E) (A) (H69) (H70) H71).


------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A E m) as H73.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E m A) /\ ((euclidean__axioms.Col E A m) /\ ((euclidean__axioms.Col A m E) /\ ((euclidean__axioms.Col m A E) /\ (euclidean__axioms.Col A E m))))) as H73.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (m) (E) (A) H72).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E m A) /\ ((euclidean__axioms.Col E A m) /\ ((euclidean__axioms.Col A m E) /\ ((euclidean__axioms.Col m A E) /\ (euclidean__axioms.Col A E m))))) as H74.
--------------------------------------------------------------------- exact H73.
--------------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col E A m) /\ ((euclidean__axioms.Col A m E) /\ ((euclidean__axioms.Col m A E) /\ (euclidean__axioms.Col A E m)))) as H76.
---------------------------------------------------------------------- exact H75.
---------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col A m E) /\ ((euclidean__axioms.Col m A E) /\ (euclidean__axioms.Col A E m))) as H78.
----------------------------------------------------------------------- exact H77.
----------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col m A E) /\ (euclidean__axioms.Col A E m)) as H80.
------------------------------------------------------------------------ exact H79.
------------------------------------------------------------------------ destruct H80 as [H80 H81].
exact H81.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H74.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A F)))))) as H74.
--------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (F) (E) (A) H33).
--------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A F)))))) as H75.
---------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A F))))) as H77.
----------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A F)))) as H79.
------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------ destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A F))) as H81.
------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A F)) as H83.
-------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------- destruct H83 as [H83 H84].
exact H83.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G H) as H75.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A H) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H A) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G A)))))) as H75.
---------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (H) (G) H61).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq A H) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H A) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G A)))))) as H76.
----------------------------------------------------------------------- exact H75.
----------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H A) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G A))))) as H78.
------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------ destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H A) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G A)))) as H80.
------------------------------------------------------------------------- exact H79.
------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.neq H A) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G A))) as H82.
-------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G A)) as H84.
--------------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------------- destruct H84 as [H84 H85].
exact H84.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G B) as H76.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H76.
----------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (G) (B) H1).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H77.
------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B)) as H79.
------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------- destruct H79 as [H79 H80].
exact H77.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H77.
----------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (B) H76).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H F B G) as H78.
------------------------------------------------------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel (H) (F) (B) (A) (G) (H21) (H4) H77).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par B G H F) as H79.
------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (H) (F) (B) (G) H78).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G B F H) as H80.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par G B H F) /\ ((euclidean__defs.Par B G F H) /\ (euclidean__defs.Par G B F H))) as H80.
--------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (G) (H) (F) H79).
--------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par G B H F) /\ ((euclidean__defs.Par B G F H) /\ (euclidean__defs.Par G B F H))) as H81.
---------------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__defs.Par B G F H) /\ (euclidean__defs.Par G B F H)) as H83.
----------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------- destruct H83 as [H83 H84].
exact H84.
-------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet G B F H)) as H81.
--------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col G B U) /\ ((euclidean__axioms.Col G B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H81.
---------------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col G B U) /\ ((euclidean__axioms.Col G B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
----------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col G B U) /\ ((euclidean__axioms.Col G B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H82.
------------------------------------------------------------------------------ exact __TmpHyp.
------------------------------------------------------------------------------ destruct H82 as [x H82].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col G B x) /\ ((euclidean__axioms.Col G B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H83.
------------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------------- destruct H83 as [x0 H83].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col G B x) /\ ((euclidean__axioms.Col G B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H84.
-------------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------------- destruct H84 as [x1 H84].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col G B x) /\ ((euclidean__axioms.Col G B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H85.
--------------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------------- destruct H85 as [x2 H85].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col G B x) /\ ((euclidean__axioms.Col G B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H86.
---------------------------------------------------------------------------------- exact H85.
---------------------------------------------------------------------------------- destruct H86 as [x3 H86].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col G B x) /\ ((euclidean__axioms.Col G B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H87.
----------------------------------------------------------------------------------- exact H86.
----------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col G B x) /\ ((euclidean__axioms.Col G B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H89.
------------------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------------------ destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col G B x) /\ ((euclidean__axioms.Col G B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H91.
------------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col G B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H93.
-------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H95.
--------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col F H x1) /\ ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H97.
---------------------------------------------------------------------------------------- exact H96.
---------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col F H x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H99.
----------------------------------------------------------------------------------------- exact H98.
----------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H101.
------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------ destruct H101 as [H101 H102].
assert (* AndElim *) ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H103.
------------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H105.
-------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col B G U) /\ ((euclidean__axioms.Col B G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H107.
--------------------------------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col B G U) /\ ((euclidean__axioms.Col B G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
---------------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col B G U) /\ ((euclidean__axioms.Col B G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H108.
----------------------------------------------------------------------------------------------- exact __TmpHyp0.
----------------------------------------------------------------------------------------------- destruct H108 as [x4 H108].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col B G x4) /\ ((euclidean__axioms.Col B G V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H109.
------------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------------ destruct H109 as [x5 H109].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col B G x4) /\ ((euclidean__axioms.Col B G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H110.
------------------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------------------- destruct H110 as [x6 H110].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col B G x4) /\ ((euclidean__axioms.Col B G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H111.
-------------------------------------------------------------------------------------------------- exact H110.
-------------------------------------------------------------------------------------------------- destruct H111 as [x7 H111].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col B G x4) /\ ((euclidean__axioms.Col B G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H112.
--------------------------------------------------------------------------------------------------- exact H111.
--------------------------------------------------------------------------------------------------- destruct H112 as [x8 H112].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col B G x4) /\ ((euclidean__axioms.Col B G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H113.
---------------------------------------------------------------------------------------------------- exact H112.
---------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col B G x4) /\ ((euclidean__axioms.Col B G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H115.
----------------------------------------------------------------------------------------------------- exact H114.
----------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col B G x4) /\ ((euclidean__axioms.Col B G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H117.
------------------------------------------------------------------------------------------------------ exact H116.
------------------------------------------------------------------------------------------------------ destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Col B G x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H119.
------------------------------------------------------------------------------------------------------- exact H118.
------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H121.
-------------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col H F x6) /\ ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H123.
--------------------------------------------------------------------------------------------------------- exact H122.
--------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col H F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H125.
---------------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H127.
----------------------------------------------------------------------------------------------------------- exact H126.
----------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H129.
------------------------------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------------------------------ destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H131.
------------------------------------------------------------------------------------------------------------- exact H130.
------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B G u) /\ ((euclidean__axioms.Col B G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H133.
-------------------------------------------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B G u) /\ ((euclidean__axioms.Col B G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
--------------------------------------------------------------------------------------------------------------- exact H133.
--------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B G u) /\ ((euclidean__axioms.Col B G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H134.
---------------------------------------------------------------------------------------------------------------- exact __TmpHyp1.
---------------------------------------------------------------------------------------------------------------- destruct H134 as [x9 H134].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col B G u) /\ ((euclidean__axioms.Col B G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H135.
----------------------------------------------------------------------------------------------------------------- exact H134.
----------------------------------------------------------------------------------------------------------------- destruct H135 as [x10 H135].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B G u) /\ ((euclidean__axioms.Col B G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H136.
------------------------------------------------------------------------------------------------------------------ exact H135.
------------------------------------------------------------------------------------------------------------------ destruct H136 as [x11 H136].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B G x11) /\ ((euclidean__axioms.Col B G v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H137.
------------------------------------------------------------------------------------------------------------------- exact H136.
------------------------------------------------------------------------------------------------------------------- destruct H137 as [x12 H137].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B G x11) /\ ((euclidean__axioms.Col B G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H138.
-------------------------------------------------------------------------------------------------------------------- exact H137.
-------------------------------------------------------------------------------------------------------------------- destruct H138 as [x13 H138].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B G x11) /\ ((euclidean__axioms.Col B G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H139.
--------------------------------------------------------------------------------------------------------------------- exact H138.
--------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B G x11) /\ ((euclidean__axioms.Col B G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H141.
---------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Col H F x9) /\ ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B G x11) /\ ((euclidean__axioms.Col B G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H143.
----------------------------------------------------------------------------------------------------------------------- exact H142.
----------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Col H F x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B G x11) /\ ((euclidean__axioms.Col B G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H145.
------------------------------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------------------------------ destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col B G x11) /\ ((euclidean__axioms.Col B G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H147.
------------------------------------------------------------------------------------------------------------------------- exact H146.
------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__axioms.Col B G x11) /\ ((euclidean__axioms.Col B G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H149.
-------------------------------------------------------------------------------------------------------------------------- exact H148.
-------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
assert (* AndElim *) ((euclidean__axioms.Col B G x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H151.
--------------------------------------------------------------------------------------------------------------------------- exact H150.
--------------------------------------------------------------------------------------------------------------------------- destruct H151 as [H151 H152].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H153.
---------------------------------------------------------------------------------------------------------------------------- exact H152.
---------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H153 H154].
assert (* AndElim *) ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H155.
----------------------------------------------------------------------------------------------------------------------------- exact H154.
----------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H157.
------------------------------------------------------------------------------------------------------------------------------ exact H156.
------------------------------------------------------------------------------------------------------------------------------ destruct H157 as [H157 H158].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H159.
------------------------------------------------------------------------------------------------------------------------------- exact H23.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
-------------------------------------------------------------------------------------------------------------------------------- exact H159.
-------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H160.
--------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
--------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [x14 H160].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H161.
---------------------------------------------------------------------------------------------------------------------------------- exact H160.
---------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [x15 H161].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H162.
----------------------------------------------------------------------------------------------------------------------------------- exact H161.
----------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [x16 H162].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F H x16) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H163.
------------------------------------------------------------------------------------------------------------------------------------ exact H162.
------------------------------------------------------------------------------------------------------------------------------------ destruct H163 as [x17 H163].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F H x16) /\ ((euclidean__axioms.Col F H x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H164.
------------------------------------------------------------------------------------------------------------------------------------- exact H163.
------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [x18 H164].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F H x16) /\ ((euclidean__axioms.Col F H x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H165.
-------------------------------------------------------------------------------------------------------------------------------------- exact H164.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H165 as [H165 H166].
assert (* AndElim *) ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F H x16) /\ ((euclidean__axioms.Col F H x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H167.
--------------------------------------------------------------------------------------------------------------------------------------- exact H166.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H167 as [H167 H168].
assert (* AndElim *) ((euclidean__axioms.Col A G x14) /\ ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F H x16) /\ ((euclidean__axioms.Col F H x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H169.
---------------------------------------------------------------------------------------------------------------------------------------- exact H168.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H169 as [H169 H170].
assert (* AndElim *) ((euclidean__axioms.Col A G x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F H x16) /\ ((euclidean__axioms.Col F H x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H171.
----------------------------------------------------------------------------------------------------------------------------------------- exact H170.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H171 as [H171 H172].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col F H x16) /\ ((euclidean__axioms.Col F H x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H173.
------------------------------------------------------------------------------------------------------------------------------------------ exact H172.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H173 as [H173 H174].
assert (* AndElim *) ((euclidean__axioms.Col F H x16) /\ ((euclidean__axioms.Col F H x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H175.
------------------------------------------------------------------------------------------------------------------------------------------- exact H174.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H175 H176].
assert (* AndElim *) ((euclidean__axioms.Col F H x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H177.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H177 H178].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H179.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H179 H180].
assert (* AndElim *) ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H181.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H180.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H181 H182].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H183.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H182.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [H183 H184].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H185.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H22.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H185.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H186.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp3.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [x19 H186].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H187.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H187 as [x20 H187].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H188.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [x21 H188].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col H F x21) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H189.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [x22 H189].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col H F x21) /\ ((euclidean__axioms.Col H F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H190.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H189.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H190 as [x23 H190].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col H F x21) /\ ((euclidean__axioms.Col H F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H191.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H190.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H191 H192].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col H F x21) /\ ((euclidean__axioms.Col H F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H193.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H192.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H193 as [H193 H194].
assert (* AndElim *) ((euclidean__axioms.Col A G x19) /\ ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col H F x21) /\ ((euclidean__axioms.Col H F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H195.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H194.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H195 H196].
assert (* AndElim *) ((euclidean__axioms.Col A G x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col H F x21) /\ ((euclidean__axioms.Col H F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H197.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [H197 H198].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col H F x21) /\ ((euclidean__axioms.Col H F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H199.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H198.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H199 as [H199 H200].
assert (* AndElim *) ((euclidean__axioms.Col H F x21) /\ ((euclidean__axioms.Col H F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H201.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H200.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H201 as [H201 H202].
assert (* AndElim *) ((euclidean__axioms.Col H F x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H203.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H202.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [H203 H204].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H205.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H204.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [H205 H206].
assert (* AndElim *) ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H207.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H206.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H207 as [H207 H208].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H209.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [H209 H210].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H211.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [x24 H212].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H213.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H212.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H213 as [x25 H213].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H214.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [x26 H214].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A G x26) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H215.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H214.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [x27 H215].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A G x26) /\ ((euclidean__axioms.Col A G x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H216.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H216 as [x28 H216].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A G x26) /\ ((euclidean__axioms.Col A G x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H217.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H216.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H217 as [H217 H218].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A G x26) /\ ((euclidean__axioms.Col A G x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H219.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H218.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H219 as [H219 H220].
assert (* AndElim *) ((euclidean__axioms.Col H F x24) /\ ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A G x26) /\ ((euclidean__axioms.Col A G x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H221.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H220.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H221 as [H221 H222].
assert (* AndElim *) ((euclidean__axioms.Col H F x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A G x26) /\ ((euclidean__axioms.Col A G x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H223.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H222.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H223 as [H223 H224].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col A G x26) /\ ((euclidean__axioms.Col A G x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H225.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H224.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H225 as [H225 H226].
assert (* AndElim *) ((euclidean__axioms.Col A G x26) /\ ((euclidean__axioms.Col A G x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H227.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H226.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H227 as [H227 H228].
assert (* AndElim *) ((euclidean__axioms.Col A G x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H229.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H228.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H229 as [H229 H230].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H231.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [H231 H232].
assert (* AndElim *) ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H233.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H232.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H233 as [H233 H234].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H235.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H234.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H235 as [H235 H236].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H237.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H20.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H237.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H238.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp5.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H238 as [x29 H238].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x29) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq x29 V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H239.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H238.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H239 as [x30 H239].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x29) /\ ((euclidean__axioms.Col H F x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X x30)))))))))))) as H240.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H239.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H240 as [x31 H240].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x29) /\ ((euclidean__axioms.Col H F x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G A x31) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq x31 v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H241.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H240.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H241 as [x32 H241].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x29) /\ ((euclidean__axioms.Col H F x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G A x31) /\ ((euclidean__axioms.Col G A x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 X x32) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H242.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H241.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H242 as [x33 H242].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x29) /\ ((euclidean__axioms.Col H F x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G A x31) /\ ((euclidean__axioms.Col G A x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))))) as H243.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H242.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H243 as [H243 H244].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F x29) /\ ((euclidean__axioms.Col H F x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G A x31) /\ ((euclidean__axioms.Col G A x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))))) as H245.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H244.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H245 as [H245 H246].
assert (* AndElim *) ((euclidean__axioms.Col H F x29) /\ ((euclidean__axioms.Col H F x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G A x31) /\ ((euclidean__axioms.Col G A x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))) as H247.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H246.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H247 as [H247 H248].
assert (* AndElim *) ((euclidean__axioms.Col H F x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G A x31) /\ ((euclidean__axioms.Col G A x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))) as H249.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H248.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H249 as [H249 H250].
assert (* AndElim *) ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col G A x31) /\ ((euclidean__axioms.Col G A x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))) as H251.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H250.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H251 as [H251 H252].
assert (* AndElim *) ((euclidean__axioms.Col G A x31) /\ ((euclidean__axioms.Col G A x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))) as H253.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H252.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H253 as [H253 H254].
assert (* AndElim *) ((euclidean__axioms.Col G A x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))) as H255.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H254.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H255 as [H255 H256].
assert (* AndElim *) ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))) as H257.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H256.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H257 as [H257 H258].
assert (* AndElim *) ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))) as H259.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H258.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H259 as [H259 H260].
assert (* AndElim *) ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)) as H261.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H260.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H261 as [H261 H262].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H263.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H19.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H263.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H264.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp6.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H264 as [x34 H264].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x34) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq x34 V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H265.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H264.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H265 as [x35 H265].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x34) /\ ((euclidean__axioms.Col H F x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS u X x35)))))))))))) as H266.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H265.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H266 as [x36 H266].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x34) /\ ((euclidean__axioms.Col H F x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B A x36) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq x36 v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS x36 X x35)))))))))))) as H267.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H266.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H267 as [x37 H267].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x34) /\ ((euclidean__axioms.Col H F x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B A x36) /\ ((euclidean__axioms.Col B A x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 X x37) /\ (euclidean__axioms.BetS x36 X x35)))))))))))) as H268.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H267.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H268 as [x38 H268].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x34) /\ ((euclidean__axioms.Col H F x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B A x36) /\ ((euclidean__axioms.Col B A x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))))))) as H269.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H268.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H269 as [H269 H270].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F x34) /\ ((euclidean__axioms.Col H F x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B A x36) /\ ((euclidean__axioms.Col B A x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))))))) as H271.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H270.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H271 as [H271 H272].
assert (* AndElim *) ((euclidean__axioms.Col H F x34) /\ ((euclidean__axioms.Col H F x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B A x36) /\ ((euclidean__axioms.Col B A x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))))) as H273.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H272.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H273 as [H273 H274].
assert (* AndElim *) ((euclidean__axioms.Col H F x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B A x36) /\ ((euclidean__axioms.Col B A x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))))) as H275.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H274.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H275 as [H275 H276].
assert (* AndElim *) ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col B A x36) /\ ((euclidean__axioms.Col B A x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))) as H277.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H276.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H277 as [H277 H278].
assert (* AndElim *) ((euclidean__axioms.Col B A x36) /\ ((euclidean__axioms.Col B A x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))) as H279.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H278.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H279 as [H279 H280].
assert (* AndElim *) ((euclidean__axioms.Col B A x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))) as H281.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H280.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H281 as [H281 H282].
assert (* AndElim *) ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))) as H283.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H282.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H283 as [H283 H284].
assert (* AndElim *) ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))) as H285.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H284.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H285 as [H285 H286].
assert (* AndElim *) ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)) as H287.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H286.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H287 as [H287 H288].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H289.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H18.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H289.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H290.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp7.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H290 as [x39 H290].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x39) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq x39 V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H291.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H290.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H291 as [x40 H291].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x39) /\ ((euclidean__axioms.Col H F x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS u X x40)))))))))))) as H292.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H291.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H292 as [x41 H292].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x39) /\ ((euclidean__axioms.Col H F x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A B x41) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq x41 v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS x41 X x40)))))))))))) as H293.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H292.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H293 as [x42 H293].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x39) /\ ((euclidean__axioms.Col H F x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A B x41) /\ ((euclidean__axioms.Col A B x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 X x42) /\ (euclidean__axioms.BetS x41 X x40)))))))))))) as H294.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H293.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H294 as [x43 H294].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x39) /\ ((euclidean__axioms.Col H F x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A B x41) /\ ((euclidean__axioms.Col A B x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))))))) as H295.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H294.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H295 as [H295 H296].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F x39) /\ ((euclidean__axioms.Col H F x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A B x41) /\ ((euclidean__axioms.Col A B x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))))))) as H297.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H296.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H297 as [H297 H298].
assert (* AndElim *) ((euclidean__axioms.Col H F x39) /\ ((euclidean__axioms.Col H F x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A B x41) /\ ((euclidean__axioms.Col A B x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))))) as H299.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H298.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H299 as [H299 H300].
assert (* AndElim *) ((euclidean__axioms.Col H F x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A B x41) /\ ((euclidean__axioms.Col A B x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))))) as H301.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H300.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H301 as [H301 H302].
assert (* AndElim *) ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col A B x41) /\ ((euclidean__axioms.Col A B x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))) as H303.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H302.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H303 as [H303 H304].
assert (* AndElim *) ((euclidean__axioms.Col A B x41) /\ ((euclidean__axioms.Col A B x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))) as H305.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H304.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H305 as [H305 H306].
assert (* AndElim *) ((euclidean__axioms.Col A B x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))) as H307.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H306.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H307 as [H307 H308].
assert (* AndElim *) ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))) as H309.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H308.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H309 as [H309 H310].
assert (* AndElim *) ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))) as H311.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H310.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H311 as [H311 H312].
assert (* AndElim *) ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)) as H313.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H312.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H313 as [H313 H314].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H315.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H17.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H315.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H316.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp8.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H316 as [x44 H316].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x44 V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H317.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H316.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H317 as [x45 H317].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 X v) /\ (euclidean__axioms.BetS u X x45)))))))))))) as H318.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H317.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H318 as [x46 H318].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col H F x46) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq x46 v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 X v) /\ (euclidean__axioms.BetS x46 X x45)))))))))))) as H319.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H318.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H319 as [x47 H319].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col H F x46) /\ ((euclidean__axioms.Col H F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 X x47) /\ (euclidean__axioms.BetS x46 X x45)))))))))))) as H320.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H319.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H320 as [x48 H320].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col H F x46) /\ ((euclidean__axioms.Col H F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))))))))) as H321.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H320.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H321 as [H321 H322].
assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col H F x46) /\ ((euclidean__axioms.Col H F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))))))))) as H323.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H322.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H323 as [H323 H324].
assert (* AndElim *) ((euclidean__axioms.Col A B x44) /\ ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col H F x46) /\ ((euclidean__axioms.Col H F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))))))) as H325.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H324.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H325 as [H325 H326].
assert (* AndElim *) ((euclidean__axioms.Col A B x45) /\ ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col H F x46) /\ ((euclidean__axioms.Col H F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))))))) as H327.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H326.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H327 as [H327 H328].
assert (* AndElim *) ((euclidean__axioms.neq x44 x45) /\ ((euclidean__axioms.Col H F x46) /\ ((euclidean__axioms.Col H F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))))) as H329.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H328.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H329 as [H329 H330].
assert (* AndElim *) ((euclidean__axioms.Col H F x46) /\ ((euclidean__axioms.Col H F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))))) as H331.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H330.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H331 as [H331 H332].
assert (* AndElim *) ((euclidean__axioms.Col H F x47) /\ ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))))) as H333.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H332.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H333 as [H333 H334].
assert (* AndElim *) ((euclidean__axioms.neq x46 x47) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)))) as H335.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H334.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H335 as [H335 H336].
assert (* AndElim *) ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45))) as H337.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H336.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H337 as [H337 H338].
assert (* AndElim *) ((euclidean__axioms.BetS x44 x48 x47) /\ (euclidean__axioms.BetS x46 x48 x45)) as H339.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H338.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H339 as [H339 H340].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H341.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H16.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp9.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H341.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H342.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp9.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H342 as [x49 H342].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x49) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x49 V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H343.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H342.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H343 as [x50 H343].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x49) /\ ((euclidean__axioms.Col A B x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 X v) /\ (euclidean__axioms.BetS u X x50)))))))))))) as H344.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H343.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H344 as [x51 H344].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x49) /\ ((euclidean__axioms.Col A B x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col H E x51) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq x51 v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 X v) /\ (euclidean__axioms.BetS x51 X x50)))))))))))) as H345.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H344.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H345 as [x52 H345].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x49) /\ ((euclidean__axioms.Col A B x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col H E x51) /\ ((euclidean__axioms.Col H E x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 X x52) /\ (euclidean__axioms.BetS x51 X x50)))))))))))) as H346.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H345.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H346 as [x53 H346].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x49) /\ ((euclidean__axioms.Col A B x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col H E x51) /\ ((euclidean__axioms.Col H E x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50))))))))))) as H347.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H346.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H347 as [H347 H348].
assert (* AndElim *) ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B x49) /\ ((euclidean__axioms.Col A B x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col H E x51) /\ ((euclidean__axioms.Col H E x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50)))))))))) as H349.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H348.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H349 as [H349 H350].
assert (* AndElim *) ((euclidean__axioms.Col A B x49) /\ ((euclidean__axioms.Col A B x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col H E x51) /\ ((euclidean__axioms.Col H E x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50))))))))) as H351.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H350.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H351 as [H351 H352].
assert (* AndElim *) ((euclidean__axioms.Col A B x50) /\ ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col H E x51) /\ ((euclidean__axioms.Col H E x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50)))))))) as H353.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H352.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H353 as [H353 H354].
assert (* AndElim *) ((euclidean__axioms.neq x49 x50) /\ ((euclidean__axioms.Col H E x51) /\ ((euclidean__axioms.Col H E x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50))))))) as H355.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H354.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H355 as [H355 H356].
assert (* AndElim *) ((euclidean__axioms.Col H E x51) /\ ((euclidean__axioms.Col H E x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50)))))) as H357.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H356.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H357 as [H357 H358].
assert (* AndElim *) ((euclidean__axioms.Col H E x52) /\ ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50))))) as H359.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H358.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H359 as [H359 H360].
assert (* AndElim *) ((euclidean__axioms.neq x51 x52) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50)))) as H361.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H360.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H361 as [H361 H362].
assert (* AndElim *) ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50))) as H363.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H362.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H363 as [H363 H364].
assert (* AndElim *) ((euclidean__axioms.BetS x49 x53 x52) /\ (euclidean__axioms.BetS x51 x53 x50)) as H365.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H364.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H365 as [H365 H366].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H367.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H14.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp10.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H367.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H368.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp10.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H368 as [x54 H368].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x54 V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H369.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H368.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H369 as [x55 H369].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 X v) /\ (euclidean__axioms.BetS u X x55)))))))))))) as H370.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H369.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H370 as [x56 H370].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col F E x56) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq x56 v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 X v) /\ (euclidean__axioms.BetS x56 X x55)))))))))))) as H371.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H370.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H371 as [x57 H371].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col F E x56) /\ ((euclidean__axioms.Col F E x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 X x57) /\ (euclidean__axioms.BetS x56 X x55)))))))))))) as H372.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H371.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H372 as [x58 H372].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col F E x56) /\ ((euclidean__axioms.Col F E x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55))))))))))) as H373.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H372.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H373 as [H373 H374].
assert (* AndElim *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col F E x56) /\ ((euclidean__axioms.Col F E x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55)))))))))) as H375.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H374.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H375 as [H375 H376].
assert (* AndElim *) ((euclidean__axioms.Col A B x54) /\ ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col F E x56) /\ ((euclidean__axioms.Col F E x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55))))))))) as H377.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H376.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H377 as [H377 H378].
assert (* AndElim *) ((euclidean__axioms.Col A B x55) /\ ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col F E x56) /\ ((euclidean__axioms.Col F E x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55)))))))) as H379.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H378.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H379 as [H379 H380].
assert (* AndElim *) ((euclidean__axioms.neq x54 x55) /\ ((euclidean__axioms.Col F E x56) /\ ((euclidean__axioms.Col F E x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55))))))) as H381.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H380.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H381 as [H381 H382].
assert (* AndElim *) ((euclidean__axioms.Col F E x56) /\ ((euclidean__axioms.Col F E x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55)))))) as H383.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H382.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H383 as [H383 H384].
assert (* AndElim *) ((euclidean__axioms.Col F E x57) /\ ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55))))) as H385.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H384.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H385 as [H385 H386].
assert (* AndElim *) ((euclidean__axioms.neq x56 x57) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55)))) as H387.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H386.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H387 as [H387 H388].
assert (* AndElim *) ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55))) as H389.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H388.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H389 as [H389 H390].
assert (* AndElim *) ((euclidean__axioms.BetS x54 x58 x57) /\ (euclidean__axioms.BetS x56 x58 x55)) as H391.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H390.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H391 as [H391 H392].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H393.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H0.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp11.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H393.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H394.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp11.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H394 as [x59 H394].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x59 V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H395.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H394.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H395 as [x60 H395].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 X v) /\ (euclidean__axioms.BetS u X x60)))))))))))) as H396.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H395.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H396 as [x61 H396].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col E F x61) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq x61 v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 X v) /\ (euclidean__axioms.BetS x61 X x60)))))))))))) as H397.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H396.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H397 as [x62 H397].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col E F x61) /\ ((euclidean__axioms.Col E F x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 X x62) /\ (euclidean__axioms.BetS x61 X x60)))))))))))) as H398.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H397.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H398 as [x63 H398].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col E F x61) /\ ((euclidean__axioms.Col E F x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60))))))))))) as H399.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H398.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H399 as [H399 H400].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col E F x61) /\ ((euclidean__axioms.Col E F x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60)))))))))) as H401.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H400.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H401 as [H401 H402].
assert (* AndElim *) ((euclidean__axioms.Col A B x59) /\ ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col E F x61) /\ ((euclidean__axioms.Col E F x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60))))))))) as H403.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H402.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H403 as [H403 H404].
assert (* AndElim *) ((euclidean__axioms.Col A B x60) /\ ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col E F x61) /\ ((euclidean__axioms.Col E F x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60)))))))) as H405.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H404.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H405 as [H405 H406].
assert (* AndElim *) ((euclidean__axioms.neq x59 x60) /\ ((euclidean__axioms.Col E F x61) /\ ((euclidean__axioms.Col E F x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60))))))) as H407.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H406.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H407 as [H407 H408].
assert (* AndElim *) ((euclidean__axioms.Col E F x61) /\ ((euclidean__axioms.Col E F x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60)))))) as H409.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H408.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H409 as [H409 H410].
assert (* AndElim *) ((euclidean__axioms.Col E F x62) /\ ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60))))) as H411.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H410.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H411 as [H411 H412].
assert (* AndElim *) ((euclidean__axioms.neq x61 x62) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60)))) as H413.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H412.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H413 as [H413 H414].
assert (* AndElim *) ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60))) as H415.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H414.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H415 as [H415 H416].
assert (* AndElim *) ((euclidean__axioms.BetS x59 x63 x62) /\ (euclidean__axioms.BetS x61 x63 x60)) as H417.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H416.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H417 as [H417 H418].
exact H103.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G A B) as H82.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B))))) as H82.
----------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (G) H6).
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B))))) as H83.
------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B)))) as H85.
------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B))) as H87.
-------------------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B)) as H89.
--------------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------------- destruct H89 as [H89 H90].
exact H90.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A m E) as H83.
----------------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (G) (B) (F) (H) (A) (E) (m) (H82) (H15) (H76) (H11) (H13) (H9) (H81) (H64) H73).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CR A E G H) as H84.
------------------------------------------------------------------------------ exists m.
split.
------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------- exact H64.
------------------------------------------------------------------------------ exact H84.
Qed.
