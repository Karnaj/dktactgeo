Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__NCdistinct.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelsymmetric.
Require Export logic.
Require Export proposition__28A.
Definition proposition__28D : forall (B: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point), (euclidean__axioms.BetS E G H) -> ((euclidean__defs.CongA E G B G H D) -> ((euclidean__defs.OS B D G H) -> (euclidean__defs.Par G B H D))).
Proof.
intro B.
intro D.
intro E.
intro G.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.nCol G H B) as H3.
- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))))) as H3.
-- exact H2.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))))) as __TmpHyp.
--- exact H3.
--- assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D))))))) as H4.
---- exact __TmpHyp.
---- destruct H4 as [x H4].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U x) /\ ((euclidean__axioms.BetS D V x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D))))))) as H5.
----- exact H4.
----- destruct H5 as [x0 H5].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col G H x0) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B x0 x) /\ ((euclidean__axioms.BetS D V x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D))))))) as H6.
------ exact H5.
------ destruct H6 as [x1 H6].
assert (* AndElim *) ((euclidean__axioms.Col G H x0) /\ ((euclidean__axioms.Col G H x1) /\ ((euclidean__axioms.BetS B x0 x) /\ ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Col G H x1) /\ ((euclidean__axioms.BetS B x0 x) /\ ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D))))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.BetS B x0 x) /\ ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
exact H15.
- assert (* Cut *) (euclidean__axioms.nCol G H D) as H4.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))))) as H4.
--- exact H2.
--- assert (* Cut *) (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))))) as __TmpHyp.
---- exact H4.
---- assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D))))))) as H5.
----- exact __TmpHyp.
----- destruct H5 as [x H5].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U x) /\ ((euclidean__axioms.BetS D V x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D))))))) as H6.
------ exact H5.
------ destruct H6 as [x0 H6].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col G H x0) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B x0 x) /\ ((euclidean__axioms.BetS D V x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D))))))) as H7.
------- exact H6.
------- destruct H7 as [x1 H7].
assert (* AndElim *) ((euclidean__axioms.Col G H x0) /\ ((euclidean__axioms.Col G H x1) /\ ((euclidean__axioms.BetS B x0 x) /\ ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col G H x1) /\ ((euclidean__axioms.BetS B x0 x) /\ ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D))))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.BetS B x0 x) /\ ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS D x1 x) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D))) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
exact H17.
-- assert (* Cut *) (euclidean__axioms.neq H D) as H5.
--- assert (* Cut *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G)))))) as H5.
---- apply (@lemma__NCdistinct.lemma__NCdistinct (G) (H) (D) H4).
---- assert (* AndElim *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G)))))) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G))))) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G)))) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G))) as H12.
-------- exact H11.
-------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G)) as H14.
--------- exact H13.
--------- destruct H14 as [H14 H15].
exact H8.
--- assert (* Cut *) (euclidean__axioms.neq D H) as H6.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (H) (D) H5).
---- assert (* Cut *) (euclidean__axioms.neq G B) as H7.
----- assert (* Cut *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq H B) /\ ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq B H) /\ (euclidean__axioms.neq B G)))))) as H7.
------ apply (@lemma__NCdistinct.lemma__NCdistinct (G) (H) (B) H3).
------ assert (* AndElim *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq H B) /\ ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq B H) /\ (euclidean__axioms.neq B G)))))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq H B) /\ ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq B H) /\ (euclidean__axioms.neq B G))))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq B H) /\ (euclidean__axioms.neq B G)))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq B H) /\ (euclidean__axioms.neq B G))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq B H) /\ (euclidean__axioms.neq B G)) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
exact H12.
----- assert (* Cut *) (euclidean__axioms.neq B G) as H8.
------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (B) H7).
------ assert (* Cut *) (exists (A: euclidean__axioms.Point), (euclidean__axioms.BetS B G A) /\ (euclidean__axioms.Cong G A G B)) as H9.
------- apply (@lemma__extension.lemma__extension (B) (G) (G) (B) (H8) H7).
------- assert (exists A: euclidean__axioms.Point, ((euclidean__axioms.BetS B G A) /\ (euclidean__axioms.Cong G A G B))) as H10.
-------- exact H9.
-------- destruct H10 as [A H10].
assert (* AndElim *) ((euclidean__axioms.BetS B G A) /\ (euclidean__axioms.Cong G A G B)) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* Cut *) (euclidean__axioms.BetS A G B) as H13.
---------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (G) (A) H11).
---------- assert (* Cut *) (exists (C: euclidean__axioms.Point), (euclidean__axioms.BetS D H C) /\ (euclidean__axioms.Cong H C H D)) as H14.
----------- apply (@lemma__extension.lemma__extension (D) (H) (H) (D) (H6) H5).
----------- assert (exists C: euclidean__axioms.Point, ((euclidean__axioms.BetS D H C) /\ (euclidean__axioms.Cong H C H D))) as H15.
------------ exact H14.
------------ destruct H15 as [C H15].
assert (* AndElim *) ((euclidean__axioms.BetS D H C) /\ (euclidean__axioms.Cong H C H D)) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
assert (* Cut *) (euclidean__axioms.BetS C H D) as H18.
-------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (H) (C) H16).
-------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H19.
--------------- apply (@proposition__28A.proposition__28A (A) (B) (C) (D) (E) (G) (H) (H13) (H18) (H0) (H1) H2).
--------------- assert (* Cut *) (euclidean__axioms.Col D H C) as H20.
---------------- right.
right.
right.
right.
left.
exact H16.
---------------- assert (* Cut *) (euclidean__axioms.Col C D H) as H21.
----------------- assert (* Cut *) ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))))) as H21.
------------------ apply (@lemma__collinearorder.lemma__collinearorder (D) (H) (C) H20).
------------------ assert (* AndElim *) ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))))) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D)))) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))) as H26.
--------------------- exact H25.
--------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D)) as H28.
---------------------- exact H27.
---------------------- destruct H28 as [H28 H29].
exact H26.
----------------- assert (* Cut *) (euclidean__axioms.neq H D) as H22.
------------------ assert (* Cut *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G)))))) as H22.
------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (G) (H) (D) H4).
------------------- assert (* AndElim *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G)))))) as H23.
-------------------- exact H22.
-------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G))))) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G)))) as H27.
---------------------- exact H26.
---------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G))) as H29.
----------------------- exact H28.
----------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G)) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [H31 H32].
exact H5.
------------------ assert (* Cut *) (euclidean__defs.Par A B H D) as H23.
------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (A) (B) (H) (C) (D) (H19) (H21) H22).
------------------- assert (* Cut *) (euclidean__defs.Par H D A B) as H24.
-------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (B) (H) (D) H23).
-------------------- assert (* Cut *) (euclidean__axioms.Col B G A) as H25.
--------------------- right.
right.
right.
right.
left.
exact H11.
--------------------- assert (* Cut *) (euclidean__axioms.Col A B G) as H26.
---------------------- assert (* Cut *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B))))) as H26.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (G) (A) H25).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B))))) as H27.
------------------------ exact H26.
------------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B)))) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B))) as H31.
-------------------------- exact H30.
-------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B)) as H33.
--------------------------- exact H32.
--------------------------- destruct H33 as [H33 H34].
exact H31.
---------------------- assert (* Cut *) (euclidean__defs.Par H D G B) as H27.
----------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (H) (D) (G) (A) (B) (H24) (H26) H7).
----------------------- assert (* Cut *) (euclidean__defs.Par G B H D) as H28.
------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (H) (D) (G) (B) H27).
------------------------ exact H28.
Qed.
