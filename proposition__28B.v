Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angledistinct.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray4.
Require Export lemma__samesidesymmetric.
Require Export lemma__supplements.
Require Export lemma__supplementsymmetric.
Require Export logic.
Require Export proposition__27.
Definition proposition__28B : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point), (euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS C H D) -> ((euclidean__defs.RT B G H G H D) -> ((euclidean__defs.OS B D G H) -> (euclidean__defs.Par A B C D)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro G.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
assert (* Cut *) (euclidean__defs.OS D B G H) as H4.
- assert (* Cut *) ((euclidean__defs.OS D B G H) /\ ((euclidean__defs.OS B D H G) /\ (euclidean__defs.OS D B H G))) as H4.
-- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (G) (H) (B) (D) H3).
-- assert (* AndElim *) ((euclidean__defs.OS D B G H) /\ ((euclidean__defs.OS B D H G) /\ (euclidean__defs.OS D B H G))) as H5.
--- exact H4.
--- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.OS B D H G) /\ (euclidean__defs.OS D B H G)) as H7.
---- exact H6.
---- destruct H7 as [H7 H8].
exact H5.
- assert (* Cut *) (exists (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c e d) /\ ((euclidean__defs.CongA B G H a b c) /\ (euclidean__defs.CongA G H D e b d))) as H5.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA B G H X Y U) /\ (euclidean__defs.CongA G H D V Y Z))) as H5.
--- exact H2.
--- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA B G H X Y U) /\ (euclidean__defs.CongA G H D V Y Z))) as __TmpHyp.
---- exact H5.
---- assert (exists X: euclidean__axioms.Point, (exists (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA B G H X Y U) /\ (euclidean__defs.CongA G H D V Y Z)))) as H6.
----- exact __TmpHyp.
----- destruct H6 as [x H6].
assert (exists Y: euclidean__axioms.Point, (exists (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x Y U V Z) /\ ((euclidean__defs.CongA B G H x Y U) /\ (euclidean__defs.CongA G H D V Y Z)))) as H7.
------ exact H6.
------ destruct H7 as [x0 H7].
assert (exists Z: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V Z) /\ ((euclidean__defs.CongA B G H x x0 U) /\ (euclidean__defs.CongA G H D V x0 Z)))) as H8.
------- exact H7.
------- destruct H8 as [x1 H8].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V x1) /\ ((euclidean__defs.CongA B G H x x0 U) /\ (euclidean__defs.CongA G H D V x0 x1)))) as H9.
-------- exact H8.
-------- destruct H9 as [x2 H9].
assert (exists V: euclidean__axioms.Point, ((euclidean__defs.Supp x x0 x2 V x1) /\ ((euclidean__defs.CongA B G H x x0 x2) /\ (euclidean__defs.CongA G H D V x0 x1)))) as H10.
--------- exact H9.
--------- destruct H10 as [x3 H10].
assert (* AndElim *) ((euclidean__defs.Supp x x0 x2 x3 x1) /\ ((euclidean__defs.CongA B G H x x0 x2) /\ (euclidean__defs.CongA G H D x3 x0 x1))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.CongA B G H x x0 x2) /\ (euclidean__defs.CongA G H D x3 x0 x1)) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
exists x.
exists x0.
exists x2.
exists x1.
exists x3.
split.
------------ exact H11.
------------ split.
------------- exact H13.
------------- exact H14.
-- assert (exists a: euclidean__axioms.Point, (exists (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c e d) /\ ((euclidean__defs.CongA B G H a b c) /\ (euclidean__defs.CongA G H D e b d)))) as H6.
--- exact H5.
--- destruct H6 as [a H6].
assert (exists b: euclidean__axioms.Point, (exists (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c e d) /\ ((euclidean__defs.CongA B G H a b c) /\ (euclidean__defs.CongA G H D e b d)))) as H7.
---- exact H6.
---- destruct H7 as [b H7].
assert (exists c: euclidean__axioms.Point, (exists (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c e d) /\ ((euclidean__defs.CongA B G H a b c) /\ (euclidean__defs.CongA G H D e b d)))) as H8.
----- exact H7.
----- destruct H8 as [c H8].
assert (exists d: euclidean__axioms.Point, (exists (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c e d) /\ ((euclidean__defs.CongA B G H a b c) /\ (euclidean__defs.CongA G H D e b d)))) as H9.
------ exact H8.
------ destruct H9 as [d H9].
assert (exists e: euclidean__axioms.Point, ((euclidean__defs.Supp a b c e d) /\ ((euclidean__defs.CongA B G H a b c) /\ (euclidean__defs.CongA G H D e b d)))) as H10.
------- exact H9.
------- destruct H10 as [e H10].
assert (* AndElim *) ((euclidean__defs.Supp a b c e d) /\ ((euclidean__defs.CongA B G H a b c) /\ (euclidean__defs.CongA G H D e b d))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.CongA B G H a b c) /\ (euclidean__defs.CongA G H D e b d)) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
assert (* Cut *) (euclidean__defs.CongA a b c B G H) as H15.
---------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (B) (G) (H) (a) (b) (c) H13).
---------- assert (* Cut *) (euclidean__axioms.neq G H) as H16.
----------- assert (* Cut *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq B H)))))) as H16.
------------ apply (@lemma__angledistinct.lemma__angledistinct (a) (b) (c) (B) (G) (H) H15).
------------ assert (* AndElim *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq B H)))))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq b c) /\ ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq B H))))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq a c) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq B H)))) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq B H))) as H23.
---------------- exact H22.
---------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq B H)) as H25.
----------------- exact H24.
----------------- destruct H25 as [H25 H26].
exact H25.
----------- assert (* Cut *) (euclidean__defs.CongA e b d G H D) as H17.
------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (G) (H) (D) (e) (b) (d) H14).
------------ assert (* Cut *) (H = H) as H18.
------------- apply (@logic.eq__refl (Point) H).
------------- assert (* Cut *) (euclidean__defs.Out G H H) as H19.
-------------- apply (@lemma__ray4.lemma__ray4 (G) (H) (H)).
---------------right.
left.
exact H18.

--------------- exact H16.
-------------- assert (* Cut *) (euclidean__defs.Supp A G H H B) as H20.
--------------- split.
---------------- exact H19.
---------------- exact H0.
--------------- assert (* Cut *) (euclidean__defs.Supp B G H H A) as H21.
---------------- apply (@lemma__supplementsymmetric.lemma__supplementsymmetric (A) (G) (H) (B) (H) H20).
---------------- assert (* Cut *) (euclidean__defs.CongA e b d H G A) as H22.
----------------- apply (@lemma__supplements.lemma__supplements (a) (b) (c) (e) (d) (B) (G) (H) (H) (A) (H15) (H11) H21).
----------------- assert (* Cut *) (euclidean__defs.CongA G H D e b d) as H23.
------------------ exact H14.
------------------ assert (* Cut *) (euclidean__defs.CongA G H D H G A) as H24.
------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (G) (H) (D) (e) (b) (d) (H) (G) (A) (H23) H22).
------------------- assert (* Cut *) (euclidean__axioms.nCol H G A) as H25.
-------------------- apply (@euclidean__tactics.nCol__notCol (H) (G) (A)).
---------------------apply (@euclidean__tactics.nCol__not__Col (H) (G) (A)).
----------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (G) (H) (D) (H) (G) (A) H24).


-------------------- assert (* Cut *) (euclidean__defs.CongA H G A A G H) as H26.
--------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (H) (G) (A) H25).
--------------------- assert (* Cut *) (euclidean__defs.CongA G H D A G H) as H27.
---------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (G) (H) (D) (H) (G) (A) (A) (G) (H) (H24) H26).
---------------------- assert (* Cut *) (euclidean__defs.CongA A G H G H D) as H28.
----------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (G) (H) (D) (A) (G) (H) H27).
----------------------- assert (* Cut *) (G = G) as H29.
------------------------ apply (@logic.eq__refl (Point) G).
------------------------ assert (* Cut *) (euclidean__axioms.Col G H G) as H30.
------------------------- right.
left.
exact H29.
------------------------- assert (* Cut *) (euclidean__axioms.nCol A G H) as H31.
-------------------------- apply (@euclidean__tactics.nCol__notCol (A) (G) (H)).
---------------------------apply (@euclidean__tactics.nCol__not__Col (A) (G) (H)).
----------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (G) (H) (D) (A) (G) (H) H27).


-------------------------- assert (* Cut *) (~(euclidean__axioms.Col G H A)) as H32.
--------------------------- intro H32.
assert (* Cut *) (euclidean__axioms.Col A G H) as H33.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col H G A) /\ ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G))))) as H33.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (H) (A) H32).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col H G A) /\ ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G))))) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col H A G) /\ ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G)))) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col A G H) /\ ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G))) as H38.
-------------------------------- exact H37.
-------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col G A H) /\ (euclidean__axioms.Col A H G)) as H40.
--------------------------------- exact H39.
--------------------------------- destruct H40 as [H40 H41].
exact H38.
---------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (G) (H) (H31) H33).
--------------------------- assert (* Cut *) (euclidean__axioms.TS A G H B) as H33.
---------------------------- exists G.
split.
----------------------------- exact H0.
----------------------------- split.
------------------------------ exact H30.
------------------------------ apply (@euclidean__tactics.nCol__notCol (G) (H) (A) H32).
---------------------------- assert (* Cut *) (euclidean__axioms.TS B G H A) as H34.
----------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (G) (H) (A) (B) H33).
----------------------------- assert (* Cut *) (euclidean__axioms.TS D G H A) as H35.
------------------------------ apply (@lemma__planeseparation.lemma__planeseparation (G) (H) (D) (B) (A) (H4) H34).
------------------------------ assert (* Cut *) (euclidean__axioms.TS A G H D) as H36.
------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (G) (H) (D) (A) H35).
------------------------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H37.
-------------------------------- apply (@proposition__27.proposition__27 (A) (B) (C) (D) (G) (H) (H0) (H1) (H28) H36).
-------------------------------- exact H37.
Qed.
