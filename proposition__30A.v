Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7b.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__27.
Require Export proposition__29.
Definition proposition__30A : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point) (K: euclidean__axioms.Point), (euclidean__defs.Par A B E F) -> ((euclidean__defs.Par C D E F) -> ((euclidean__axioms.BetS G H K) -> ((euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS E H F) -> ((euclidean__axioms.BetS C K D) -> ((euclidean__axioms.TS A G H F) -> ((euclidean__axioms.TS F H K C) -> (euclidean__defs.Par A B C D)))))))).
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
intro H7.
assert (* Cut *) (euclidean__defs.Par E F C D) as H8.
- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (C) (D) (E) (F) H1).
- assert (* Cut *) (euclidean__axioms.neq G H) as H9.
-- assert (* Cut *) ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G K))) as H9.
--- apply (@lemma__betweennotequal.lemma__betweennotequal (G) (H) (K) H2).
--- assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G K))) as H10.
---- exact H9.
---- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G K)) as H12.
----- exact H11.
----- destruct H12 as [H12 H13].
exact H12.
-- assert (* Cut *) (euclidean__axioms.neq H G) as H10.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (H) H9).
--- assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.BetS H G P) /\ (euclidean__axioms.Cong G P G H)) as H11.
---- apply (@lemma__extension.lemma__extension (H) (G) (G) (H) (H10) H9).
---- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.BetS H G P) /\ (euclidean__axioms.Cong G P G H))) as H12.
----- exact H11.
----- destruct H12 as [P H12].
assert (* AndElim *) ((euclidean__axioms.BetS H G P) /\ (euclidean__axioms.Cong G P G H)) as H13.
------ exact H12.
------ destruct H13 as [H13 H14].
assert (* Cut *) (euclidean__axioms.BetS P G H) as H15.
------- apply (@euclidean__axioms.axiom__betweennesssymmetry (H) (G) (P) H13).
------- assert (* Cut *) (euclidean__axioms.BetS P G K) as H16.
-------- apply (@lemma__3__7b.lemma__3__7b (P) (G) (H) (K) (H15) H2).
-------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M F) /\ ((euclidean__axioms.Col G H M) /\ (euclidean__axioms.nCol G H A))) as H17.
--------- exact H6.
--------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M F) /\ ((euclidean__axioms.Col G H M) /\ (euclidean__axioms.nCol G H A)))) as H18.
---------- exact H17.
---------- destruct H18 as [M H18].
assert (* AndElim *) ((euclidean__axioms.BetS A M F) /\ ((euclidean__axioms.Col G H M) /\ (euclidean__axioms.nCol G H A))) as H19.
----------- exact H18.
----------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col G H M) /\ (euclidean__axioms.nCol G H A)) as H21.
------------ exact H20.
------------ destruct H21 as [H21 H22].
assert (* Cut *) (exists (N: euclidean__axioms.Point), (euclidean__axioms.BetS F N C) /\ ((euclidean__axioms.Col H K N) /\ (euclidean__axioms.nCol H K F))) as H23.
------------- exact H7.
------------- assert (exists N: euclidean__axioms.Point, ((euclidean__axioms.BetS F N C) /\ ((euclidean__axioms.Col H K N) /\ (euclidean__axioms.nCol H K F)))) as H24.
-------------- exact H23.
-------------- destruct H24 as [N H24].
assert (* AndElim *) ((euclidean__axioms.BetS F N C) /\ ((euclidean__axioms.Col H K N) /\ (euclidean__axioms.nCol H K F))) as H25.
--------------- exact H24.
--------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col H K N) /\ (euclidean__axioms.nCol H K F)) as H27.
---------------- exact H26.
---------------- destruct H27 as [H27 H28].
assert (* Cut *) (~(euclidean__defs.Meet C D E F)) as H29.
----------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H29.
------------------ exact H8.
------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
------------------- exact H29.
------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H30.
-------------------- exact __TmpHyp.
-------------------- destruct H30 as [x H30].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col E F x) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H31.
--------------------- exact H30.
--------------------- destruct H31 as [x0 H31].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col E F x) /\ ((euclidean__axioms.Col E F x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H32.
---------------------- exact H31.
---------------------- destruct H32 as [x1 H32].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col E F x) /\ ((euclidean__axioms.Col E F x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H33.
----------------------- exact H32.
----------------------- destruct H33 as [x2 H33].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col E F x) /\ ((euclidean__axioms.Col E F x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H34.
------------------------ exact H33.
------------------------ destruct H34 as [x3 H34].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col E F x) /\ ((euclidean__axioms.Col E F x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H35.
------------------------- exact H34.
------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col E F x) /\ ((euclidean__axioms.Col E F x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H37.
-------------------------- exact H36.
-------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col E F x) /\ ((euclidean__axioms.Col E F x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H39.
--------------------------- exact H38.
--------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col E F x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H41.
---------------------------- exact H40.
---------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H43.
----------------------------- exact H42.
----------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H45.
------------------------------ exact H44.
------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H47.
------------------------------- exact H46.
------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H49.
-------------------------------- exact H48.
-------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H51.
--------------------------------- exact H50.
--------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H53.
---------------------------------- exact H52.
---------------------------------- destruct H53 as [H53 H54].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H55.
----------------------------------- exact H1.
----------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------------------ exact H55.
------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H56.
------------------------------------- exact __TmpHyp0.
------------------------------------- destruct H56 as [x4 H56].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col C D x4) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H57.
-------------------------------------- exact H56.
-------------------------------------- destruct H57 as [x5 H57].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col C D x4) /\ ((euclidean__axioms.Col C D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H58.
--------------------------------------- exact H57.
--------------------------------------- destruct H58 as [x6 H58].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col C D x4) /\ ((euclidean__axioms.Col C D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col E F x6) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H59.
---------------------------------------- exact H58.
---------------------------------------- destruct H59 as [x7 H59].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col C D x4) /\ ((euclidean__axioms.Col C D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col E F x6) /\ ((euclidean__axioms.Col E F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H60.
----------------------------------------- exact H59.
----------------------------------------- destruct H60 as [x8 H60].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col C D x4) /\ ((euclidean__axioms.Col C D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col E F x6) /\ ((euclidean__axioms.Col E F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H61.
------------------------------------------ exact H60.
------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col C D x4) /\ ((euclidean__axioms.Col C D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col E F x6) /\ ((euclidean__axioms.Col E F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H63.
------------------------------------------- exact H62.
------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col C D x4) /\ ((euclidean__axioms.Col C D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col E F x6) /\ ((euclidean__axioms.Col E F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H65.
-------------------------------------------- exact H64.
-------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col C D x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col E F x6) /\ ((euclidean__axioms.Col E F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H67.
--------------------------------------------- exact H66.
--------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col E F x6) /\ ((euclidean__axioms.Col E F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H69.
---------------------------------------------- exact H68.
---------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col E F x6) /\ ((euclidean__axioms.Col E F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H71.
----------------------------------------------- exact H70.
----------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col E F x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H73.
------------------------------------------------ exact H72.
------------------------------------------------ destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H75.
------------------------------------------------- exact H74.
------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H77.
-------------------------------------------------- exact H76.
-------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H79.
--------------------------------------------------- exact H78.
--------------------------------------------------- destruct H79 as [H79 H80].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H81.
---------------------------------------------------- exact H0.
---------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
----------------------------------------------------- exact H81.
----------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H82.
------------------------------------------------------ exact __TmpHyp1.
------------------------------------------------------ destruct H82 as [x9 H82].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H83.
------------------------------------------------------- exact H82.
------------------------------------------------------- destruct H83 as [x10 H83].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H84.
-------------------------------------------------------- exact H83.
-------------------------------------------------------- destruct H84 as [x11 H84].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E F x11) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H85.
--------------------------------------------------------- exact H84.
--------------------------------------------------------- destruct H85 as [x12 H85].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E F x11) /\ ((euclidean__axioms.Col E F x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H86.
---------------------------------------------------------- exact H85.
---------------------------------------------------------- destruct H86 as [x13 H86].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E F x11) /\ ((euclidean__axioms.Col E F x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H87.
----------------------------------------------------------- exact H86.
----------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E F x11) /\ ((euclidean__axioms.Col E F x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H89.
------------------------------------------------------------ exact H88.
------------------------------------------------------------ destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E F x11) /\ ((euclidean__axioms.Col E F x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H91.
------------------------------------------------------------- exact H90.
------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E F x11) /\ ((euclidean__axioms.Col E F x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H93.
-------------------------------------------------------------- exact H92.
-------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col E F x11) /\ ((euclidean__axioms.Col E F x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H95.
--------------------------------------------------------------- exact H94.
--------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col E F x11) /\ ((euclidean__axioms.Col E F x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H97.
---------------------------------------------------------------- exact H96.
---------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col E F x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H99.
----------------------------------------------------------------- exact H98.
----------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H101.
------------------------------------------------------------------ exact H100.
------------------------------------------------------------------ destruct H101 as [H101 H102].
assert (* AndElim *) ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H103.
------------------------------------------------------------------- exact H102.
------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H105.
-------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------- destruct H105 as [H105 H106].
exact H77.
----------------- assert (* Cut *) (euclidean__axioms.nCol G H A) as H30.
------------------ exact H22.
------------------ assert (* Cut *) (euclidean__axioms.neq A G) as H31.
------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H31.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (G) (B) H3).
-------------------- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H32.
--------------------- exact H31.
--------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B)) as H34.
---------------------- exact H33.
---------------------- destruct H34 as [H34 H35].
exact H34.
------------------- assert (* Cut *) (euclidean__axioms.neq G A) as H32.
-------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (G) H31).
-------------------- assert (* Cut *) (euclidean__axioms.neq G H) as H33.
--------------------- assert (* Cut *) ((euclidean__axioms.neq N C) /\ ((euclidean__axioms.neq F N) /\ (euclidean__axioms.neq F C))) as H33.
---------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (N) (C) H25).
---------------------- assert (* AndElim *) ((euclidean__axioms.neq N C) /\ ((euclidean__axioms.neq F N) /\ (euclidean__axioms.neq F C))) as H34.
----------------------- exact H33.
----------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq F N) /\ (euclidean__axioms.neq F C)) as H36.
------------------------ exact H35.
------------------------ destruct H36 as [H36 H37].
exact H9.
--------------------- assert (* Cut *) (euclidean__axioms.nCol A G H) as H34.
---------------------- assert (* Cut *) ((euclidean__axioms.nCol H G A) /\ ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A G H) /\ ((euclidean__axioms.nCol G A H) /\ (euclidean__axioms.nCol A H G))))) as H34.
----------------------- apply (@lemma__NCorder.lemma__NCorder (G) (H) (A) H30).
----------------------- assert (* AndElim *) ((euclidean__axioms.nCol H G A) /\ ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A G H) /\ ((euclidean__axioms.nCol G A H) /\ (euclidean__axioms.nCol A H G))))) as H35.
------------------------ exact H34.
------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A G H) /\ ((euclidean__axioms.nCol G A H) /\ (euclidean__axioms.nCol A H G)))) as H37.
------------------------- exact H36.
------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.nCol A G H) /\ ((euclidean__axioms.nCol G A H) /\ (euclidean__axioms.nCol A H G))) as H39.
-------------------------- exact H38.
-------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.nCol G A H) /\ (euclidean__axioms.nCol A H G)) as H41.
--------------------------- exact H40.
--------------------------- destruct H41 as [H41 H42].
exact H39.
---------------------- assert (* Cut *) (euclidean__defs.CongA A G H G H F) as H35.
----------------------- assert (* Cut *) ((euclidean__defs.Par A B E F) -> ((euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS E H F) -> ((euclidean__axioms.BetS P G H) -> ((euclidean__axioms.TS A G H F) -> (euclidean__defs.CongA A G H G H F)))))) as H35.
------------------------ intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.CongA A G H G H F) /\ ((euclidean__defs.CongA P G B G H F) /\ (euclidean__defs.RT B G H G H F))) as __4.
------------------------- apply (@proposition__29.proposition__29 (A) (B) (E) (F) (P) (G) (H) (__) (__0) (__1) (__2) __3).
------------------------- destruct __4 as [__4 __5].
exact __4.
------------------------ apply (@H35 (H0) (H3) (H4) (H15) H6).
----------------------- assert (* Cut *) (A = A) as H36.
------------------------ apply (@logic.eq__refl (Point) A).
------------------------ assert (* Cut *) (euclidean__defs.Out G A A) as H37.
------------------------- apply (@lemma__ray4.lemma__ray4 (G) (A) (A)).
--------------------------right.
left.
exact H36.

-------------------------- exact H32.
------------------------- assert (* Cut *) (euclidean__defs.Out G H K) as H38.
-------------------------- apply (@lemma__ray4.lemma__ray4 (G) (H) (K)).
---------------------------right.
right.
exact H2.

--------------------------- exact H33.
-------------------------- assert (* Cut *) (euclidean__defs.CongA A G H A G H) as H39.
--------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (G) (H) H34).
--------------------------- assert (* Cut *) (euclidean__defs.CongA A G H A G K) as H40.
---------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (A) (G) (H) (A) (G) (H) (A) (K) (H39) (H37) H38).
---------------------------- assert (* Cut *) (euclidean__defs.CongA A G K A G H) as H41.
----------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (G) (H) (A) (G) (K) H40).
----------------------------- assert (* Cut *) (euclidean__defs.CongA A G K G H F) as H42.
------------------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (G) (K) (A) (G) (H) (G) (H) (F) (H41) H35).
------------------------------ assert (* Cut *) (euclidean__axioms.BetS C N F) as H43.
------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (F) (N) (C) H25).
------------------------------- assert (* Cut *) (H = H) as H44.
-------------------------------- apply (@logic.eq__refl (Point) H).
-------------------------------- assert (* Cut *) (euclidean__axioms.nCol F H K) as H45.
--------------------------------- assert (* Cut *) ((euclidean__axioms.nCol K H F) /\ ((euclidean__axioms.nCol K F H) /\ ((euclidean__axioms.nCol F H K) /\ ((euclidean__axioms.nCol H F K) /\ (euclidean__axioms.nCol F K H))))) as H45.
---------------------------------- apply (@lemma__NCorder.lemma__NCorder (H) (K) (F) H28).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol K H F) /\ ((euclidean__axioms.nCol K F H) /\ ((euclidean__axioms.nCol F H K) /\ ((euclidean__axioms.nCol H F K) /\ (euclidean__axioms.nCol F K H))))) as H46.
----------------------------------- exact H45.
----------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.nCol K F H) /\ ((euclidean__axioms.nCol F H K) /\ ((euclidean__axioms.nCol H F K) /\ (euclidean__axioms.nCol F K H)))) as H48.
------------------------------------ exact H47.
------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.nCol F H K) /\ ((euclidean__axioms.nCol H F K) /\ (euclidean__axioms.nCol F K H))) as H50.
------------------------------------- exact H49.
------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.nCol H F K) /\ (euclidean__axioms.nCol F K H)) as H52.
-------------------------------------- exact H51.
-------------------------------------- destruct H52 as [H52 H53].
exact H50.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col E H F) as H46.
---------------------------------- right.
right.
right.
right.
left.
exact H4.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col F H E) as H47.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E))))) as H47.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (E) (H) (F) H46).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E))))) as H48.
------------------------------------- exact H47.
------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E)))) as H50.
-------------------------------------- exact H49.
-------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E))) as H52.
--------------------------------------- exact H51.
--------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E)) as H54.
---------------------------------------- exact H53.
---------------------------------------- destruct H54 as [H54 H55].
exact H55.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col F H H) as H48.
------------------------------------ right.
right.
left.
exact H44.
------------------------------------ assert (* Cut *) (euclidean__axioms.neq E H) as H49.
------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H49.
-------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (H) (F) H4).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H50.
--------------------------------------- exact H49.
--------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F)) as H52.
---------------------------------------- exact H51.
---------------------------------------- destruct H52 as [H52 H53].
exact H52.
------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E H K) as H50.
-------------------------------------- apply (@euclidean__tactics.nCol__notCol (E) (H) (K)).
---------------------------------------apply (@euclidean__tactics.nCol__not__Col (E) (H) (K)).
----------------------------------------apply (@lemma__NChelper.lemma__NChelper (F) (H) (K) (E) (H) (H45) (H47) (H48) H49).


-------------------------------------- assert (* Cut *) (euclidean__axioms.Col E H F) as H51.
--------------------------------------- exact H46.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col E H H) as H52.
---------------------------------------- right.
right.
left.
exact H44.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq H F) as H53.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H53.
------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (E) (H) (F) H4).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H54.
------------------------------------------- exact H53.
------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F)) as H56.
-------------------------------------------- exact H55.
-------------------------------------------- destruct H56 as [H56 H57].
exact H54.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq F H) as H54.
------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (H) (F) H53).
------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol F H K) as H55.
------------------------------------------- exact H45.
------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H K F) as H56.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H F K) /\ ((euclidean__axioms.nCol H K F) /\ ((euclidean__axioms.nCol K F H) /\ ((euclidean__axioms.nCol F K H) /\ (euclidean__axioms.nCol K H F))))) as H56.
--------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (F) (H) (K) H55).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol H F K) /\ ((euclidean__axioms.nCol H K F) /\ ((euclidean__axioms.nCol K F H) /\ ((euclidean__axioms.nCol F K H) /\ (euclidean__axioms.nCol K H F))))) as H57.
---------------------------------------------- exact H56.
---------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.nCol H K F) /\ ((euclidean__axioms.nCol K F H) /\ ((euclidean__axioms.nCol F K H) /\ (euclidean__axioms.nCol K H F)))) as H59.
----------------------------------------------- exact H58.
----------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.nCol K F H) /\ ((euclidean__axioms.nCol F K H) /\ (euclidean__axioms.nCol K H F))) as H61.
------------------------------------------------ exact H60.
------------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.nCol F K H) /\ (euclidean__axioms.nCol K H F)) as H63.
------------------------------------------------- exact H62.
------------------------------------------------- destruct H63 as [H63 H64].
exact H59.
-------------------------------------------- assert (* Cut *) (H = H) as H57.
--------------------------------------------- exact H44.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H K H) as H58.
---------------------------------------------- right.
left.
exact H57.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K H N) as H59.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K H N) /\ ((euclidean__axioms.Col K N H) /\ ((euclidean__axioms.Col N H K) /\ ((euclidean__axioms.Col H N K) /\ (euclidean__axioms.Col N K H))))) as H59.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (H) (K) (N) H27).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col K H N) /\ ((euclidean__axioms.Col K N H) /\ ((euclidean__axioms.Col N H K) /\ ((euclidean__axioms.Col H N K) /\ (euclidean__axioms.Col N K H))))) as H60.
------------------------------------------------- exact H59.
------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col K N H) /\ ((euclidean__axioms.Col N H K) /\ ((euclidean__axioms.Col H N K) /\ (euclidean__axioms.Col N K H)))) as H62.
-------------------------------------------------- exact H61.
-------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col N H K) /\ ((euclidean__axioms.Col H N K) /\ (euclidean__axioms.Col N K H))) as H64.
--------------------------------------------------- exact H63.
--------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col H N K) /\ (euclidean__axioms.Col N K H)) as H66.
---------------------------------------------------- exact H65.
---------------------------------------------------- destruct H66 as [H66 H67].
exact H60.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C K D) as H60.
------------------------------------------------ right.
right.
right.
right.
left.
exact H5.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E H F) as H61.
------------------------------------------------- exact H51.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C K) as H62.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq K D) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D))) as H62.
--------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (K) (D) H5).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq K D) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D))) as H63.
---------------------------------------------------- exact H62.
---------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D)) as H65.
----------------------------------------------------- exact H64.
----------------------------------------------------- destruct H65 as [H65 H66].
exact H65.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H63.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq K D) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D))) as H63.
---------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (K) (D) H5).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq K D) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D))) as H64.
----------------------------------------------------- exact H63.
----------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D)) as H66.
------------------------------------------------------ exact H65.
------------------------------------------------------ destruct H66 as [H66 H67].
exact H67.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H F) as H64.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq N F) /\ ((euclidean__axioms.neq C N) /\ (euclidean__axioms.neq C F))) as H64.
----------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (N) (F) H43).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq N F) /\ ((euclidean__axioms.neq C N) /\ (euclidean__axioms.neq C F))) as H65.
------------------------------------------------------ exact H64.
------------------------------------------------------ destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.neq C N) /\ (euclidean__axioms.neq C F)) as H67.
------------------------------------------------------- exact H66.
------------------------------------------------------- destruct H67 as [H67 H68].
exact H53.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E F) as H65.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H65.
------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (E) (H) (F) H4).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H66.
------------------------------------------------------- exact H65.
------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F)) as H68.
-------------------------------------------------------- exact H67.
-------------------------------------------------------- destruct H68 as [H68 H69].
exact H69.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS K N H) as H66.
------------------------------------------------------ apply (@lemma__collinearbetween.lemma__collinearbetween (C) (D) (E) (F) (K) (H) (N) (H60) (H61) (H63) (H65) (H62) (H64) (H29) (H43) H59).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq N H) as H67.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq N H) /\ ((euclidean__axioms.neq K N) /\ (euclidean__axioms.neq K H))) as H67.
-------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (K) (N) (H) H66).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq N H) /\ ((euclidean__axioms.neq K N) /\ (euclidean__axioms.neq K H))) as H68.
--------------------------------------------------------- exact H67.
--------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq K N) /\ (euclidean__axioms.neq K H)) as H70.
---------------------------------------------------------- exact H69.
---------------------------------------------------------- destruct H70 as [H70 H71].
exact H68.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H N) as H68.
-------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (N) (H) H67).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H N F) as H69.
--------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (H) (N) (F)).
----------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (H) (N) (F)).
-----------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (H) (K) (F) (H) (N) (H56) (H58) (H27) H68).


--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F N H) as H70.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol N H F) /\ ((euclidean__axioms.nCol N F H) /\ ((euclidean__axioms.nCol F H N) /\ ((euclidean__axioms.nCol H F N) /\ (euclidean__axioms.nCol F N H))))) as H70.
----------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (H) (N) (F) H69).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol N H F) /\ ((euclidean__axioms.nCol N F H) /\ ((euclidean__axioms.nCol F H N) /\ ((euclidean__axioms.nCol H F N) /\ (euclidean__axioms.nCol F N H))))) as H71.
------------------------------------------------------------ exact H70.
------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.nCol N F H) /\ ((euclidean__axioms.nCol F H N) /\ ((euclidean__axioms.nCol H F N) /\ (euclidean__axioms.nCol F N H)))) as H73.
------------------------------------------------------------- exact H72.
------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.nCol F H N) /\ ((euclidean__axioms.nCol H F N) /\ (euclidean__axioms.nCol F N H))) as H75.
-------------------------------------------------------------- exact H74.
-------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.nCol H F N) /\ (euclidean__axioms.nCol F N H)) as H77.
--------------------------------------------------------------- exact H76.
--------------------------------------------------------------- destruct H77 as [H77 H78].
exact H78.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F N C) as H71.
----------------------------------------------------------- exact H25.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F N C) as H72.
------------------------------------------------------------ right.
right.
right.
right.
left.
exact H71.
------------------------------------------------------------ assert (* Cut *) (N = N) as H73.
------------------------------------------------------------- apply (@logic.eq__refl (Point) N).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F N N) as H74.
-------------------------------------------------------------- right.
right.
left.
exact H73.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C N) as H75.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq N F) /\ ((euclidean__axioms.neq C N) /\ (euclidean__axioms.neq C F))) as H75.
---------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (N) (F) H43).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq N F) /\ ((euclidean__axioms.neq C N) /\ (euclidean__axioms.neq C F))) as H76.
----------------------------------------------------------------- exact H75.
----------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq C N) /\ (euclidean__axioms.neq C F)) as H78.
------------------------------------------------------------------ exact H77.
------------------------------------------------------------------ destruct H78 as [H78 H79].
exact H78.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C N H) as H76.
---------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (C) (N) (H)).
-----------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (C) (N) (H)).
------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (F) (N) (H) (C) (N) (H70) (H72) (H74) H75).


---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H N C) as H77.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol N C H) /\ ((euclidean__axioms.nCol N H C) /\ ((euclidean__axioms.nCol H C N) /\ ((euclidean__axioms.nCol C H N) /\ (euclidean__axioms.nCol H N C))))) as H77.
------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (C) (N) (H) H76).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol N C H) /\ ((euclidean__axioms.nCol N H C) /\ ((euclidean__axioms.nCol H C N) /\ ((euclidean__axioms.nCol C H N) /\ (euclidean__axioms.nCol H N C))))) as H78.
------------------------------------------------------------------- exact H77.
------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.nCol N H C) /\ ((euclidean__axioms.nCol H C N) /\ ((euclidean__axioms.nCol C H N) /\ (euclidean__axioms.nCol H N C)))) as H80.
-------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.nCol H C N) /\ ((euclidean__axioms.nCol C H N) /\ (euclidean__axioms.nCol H N C))) as H82.
--------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.nCol C H N) /\ (euclidean__axioms.nCol H N C)) as H84.
---------------------------------------------------------------------- exact H83.
---------------------------------------------------------------------- destruct H84 as [H84 H85].
exact H85.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS H N K) as H78.
------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (K) (N) (H) H66).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H N K) as H79.
------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H78.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H N H) as H80.
-------------------------------------------------------------------- right.
left.
exact H57.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H K) as H81.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq N K) /\ ((euclidean__axioms.neq H N) /\ (euclidean__axioms.neq H K))) as H81.
---------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (H) (N) (K) H78).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq N K) /\ ((euclidean__axioms.neq H N) /\ (euclidean__axioms.neq H K))) as H82.
----------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.neq H N) /\ (euclidean__axioms.neq H K)) as H84.
------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------ destruct H84 as [H84 H85].
exact H85.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H K C) as H82.
---------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (H) (K) (C)).
-----------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (H) (K) (C)).
------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (H) (N) (C) (H) (K) (H77) (H80) (H79) H81).


---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H K E) as H83.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H E K) /\ ((euclidean__axioms.nCol H K E) /\ ((euclidean__axioms.nCol K E H) /\ ((euclidean__axioms.nCol E K H) /\ (euclidean__axioms.nCol K H E))))) as H83.
------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (E) (H) (K) H50).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol H E K) /\ ((euclidean__axioms.nCol H K E) /\ ((euclidean__axioms.nCol K E H) /\ ((euclidean__axioms.nCol E K H) /\ (euclidean__axioms.nCol K H E))))) as H84.
------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.nCol H K E) /\ ((euclidean__axioms.nCol K E H) /\ ((euclidean__axioms.nCol E K H) /\ (euclidean__axioms.nCol K H E)))) as H86.
-------------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.nCol K E H) /\ ((euclidean__axioms.nCol E K H) /\ (euclidean__axioms.nCol K H E))) as H88.
--------------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.nCol E K H) /\ (euclidean__axioms.nCol K H E)) as H90.
---------------------------------------------------------------------------- exact H89.
---------------------------------------------------------------------------- destruct H90 as [H90 H91].
exact H86.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS E C H K) as H84.
------------------------------------------------------------------------ exists F.
exists H.
exists N.
split.
------------------------------------------------------------------------- exact H58.
------------------------------------------------------------------------- split.
-------------------------------------------------------------------------- exact H27.
-------------------------------------------------------------------------- split.
--------------------------------------------------------------------------- exact H4.
--------------------------------------------------------------------------- split.
---------------------------------------------------------------------------- exact H43.
---------------------------------------------------------------------------- split.
----------------------------------------------------------------------------- exact H83.
----------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------ assert (* Cut *) (K = K) as H85.
------------------------------------------------------------------------- apply (@logic.eq__refl (Point) K).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H K K) as H86.
-------------------------------------------------------------------------- right.
right.
left.
exact H85.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C H K D) as H87.
--------------------------------------------------------------------------- exists K.
split.
---------------------------------------------------------------------------- exact H5.
---------------------------------------------------------------------------- split.
----------------------------------------------------------------------------- exact H86.
----------------------------------------------------------------------------- exact H82.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS E H K D) as H88.
---------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation (H) (K) (E) (C) (D) (H84) H87).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G H F H K D) as H89.
----------------------------------------------------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point) (E0: euclidean__axioms.Point) (G0: euclidean__axioms.Point) (H89: euclidean__axioms.Point), (euclidean__defs.Par A0 B0 C0 D0) -> ((euclidean__axioms.BetS A0 G0 B0) -> ((euclidean__axioms.BetS C0 H89 D0) -> ((euclidean__axioms.BetS E0 G0 H89) -> ((euclidean__axioms.TS A0 G0 H89 D0) -> ((euclidean__defs.CongA E0 G0 B0 G0 H89 D0) /\ (euclidean__defs.RT B0 G0 H89 G0 H89 D0))))))) as H89.
------------------------------------------------------------------------------ intro A0.
intro B0.
intro C0.
intro D0.
intro E0.
intro G0.
intro H89.
intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.CongA A0 G0 H89 G0 H89 D0) /\ ((euclidean__defs.CongA E0 G0 B0 G0 H89 D0) /\ (euclidean__defs.RT B0 G0 H89 G0 H89 D0))) as __4.
------------------------------------------------------------------------------- apply (@proposition__29.proposition__29 (A0) (B0) (C0) (D0) (E0) (G0) (H89) (__) (__0) (__1) (__2) __3).
------------------------------------------------------------------------------- destruct __4 as [__4 __5].
exact __5.
------------------------------------------------------------------------------ assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point) (E0: euclidean__axioms.Point) (G0: euclidean__axioms.Point) (H90: euclidean__axioms.Point), (euclidean__defs.Par A0 B0 C0 D0) -> ((euclidean__axioms.BetS A0 G0 B0) -> ((euclidean__axioms.BetS C0 H90 D0) -> ((euclidean__axioms.BetS E0 G0 H90) -> ((euclidean__axioms.TS A0 G0 H90 D0) -> (euclidean__defs.CongA E0 G0 B0 G0 H90 D0)))))) as H90.
------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro E0.
intro G0.
intro H90.
intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.CongA E0 G0 B0 G0 H90 D0) /\ (euclidean__defs.RT B0 G0 H90 G0 H90 D0)) as __4.
-------------------------------------------------------------------------------- apply (@H89 (A0) (B0) (C0) (D0) (E0) (G0) (H90) (__) (__0) (__1) (__2) __3).
-------------------------------------------------------------------------------- destruct __4 as [__4 __5].
exact __4.
------------------------------------------------------------------------------- apply (@H90 (E) (F) (C) (D) (G) (H) (K) (H8) (H4) (H5) (H2) H88).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C K H) as H90.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol K H C) /\ ((euclidean__axioms.nCol K C H) /\ ((euclidean__axioms.nCol C H K) /\ ((euclidean__axioms.nCol H C K) /\ (euclidean__axioms.nCol C K H))))) as H90.
------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (H) (K) (C) H82).
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol K H C) /\ ((euclidean__axioms.nCol K C H) /\ ((euclidean__axioms.nCol C H K) /\ ((euclidean__axioms.nCol H C K) /\ (euclidean__axioms.nCol C K H))))) as H91.
-------------------------------------------------------------------------------- exact H90.
-------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.nCol K C H) /\ ((euclidean__axioms.nCol C H K) /\ ((euclidean__axioms.nCol H C K) /\ (euclidean__axioms.nCol C K H)))) as H93.
--------------------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.nCol C H K) /\ ((euclidean__axioms.nCol H C K) /\ (euclidean__axioms.nCol C K H))) as H95.
---------------------------------------------------------------------------------- exact H94.
---------------------------------------------------------------------------------- destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.nCol H C K) /\ (euclidean__axioms.nCol C K H)) as H97.
----------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------- destruct H97 as [H97 H98].
exact H98.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C K D) as H91.
------------------------------------------------------------------------------- exact H60.
------------------------------------------------------------------------------- assert (* Cut *) (K = K) as H92.
-------------------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C K K) as H93.
--------------------------------------------------------------------------------- right.
right.
left.
exact H92.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq K D) as H94.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq K D) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D))) as H94.
----------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (K) (D) H5).
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq K D) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D))) as H95.
------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D)) as H97.
------------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
exact H95.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D K) as H95.
----------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (K) (D) H94).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D K H) as H96.
------------------------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (D) (K) (H)).
-------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (D) (K) (H)).
--------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (C) (K) (H) (D) (K) (H90) (H91) (H93) H95).


------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol H K D) as H97.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol K D H) /\ ((euclidean__axioms.nCol K H D) /\ ((euclidean__axioms.nCol H D K) /\ ((euclidean__axioms.nCol D H K) /\ (euclidean__axioms.nCol H K D))))) as H97.
-------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (D) (K) (H) H96).
-------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol K D H) /\ ((euclidean__axioms.nCol K H D) /\ ((euclidean__axioms.nCol H D K) /\ ((euclidean__axioms.nCol D H K) /\ (euclidean__axioms.nCol H K D))))) as H98.
--------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.nCol K H D) /\ ((euclidean__axioms.nCol H D K) /\ ((euclidean__axioms.nCol D H K) /\ (euclidean__axioms.nCol H K D)))) as H100.
---------------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.nCol H D K) /\ ((euclidean__axioms.nCol D H K) /\ (euclidean__axioms.nCol H K D))) as H102.
----------------------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.nCol D H K) /\ (euclidean__axioms.nCol H K D)) as H104.
------------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------------ destruct H104 as [H104 H105].
exact H105.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H K D H K D) as H98.
-------------------------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (H) (K) (D) H97).
-------------------------------------------------------------------------------------- assert (* Cut *) (D = D) as H99.
--------------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) D).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out K D D) as H100.
---------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (K) (D) (D)).
-----------------------------------------------------------------------------------------right.
left.
exact H99.

----------------------------------------------------------------------------------------- exact H94.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS K H G) as H101.
----------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (H) (K) H2).
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq K H) as H102.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G))) as H102.
------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (K) (H) (G) H101).
------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G))) as H103.
-------------------------------------------------------------------------------------------- exact H102.
-------------------------------------------------------------------------------------------- destruct H103 as [H103 H104].
assert (* AndElim *) ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G)) as H105.
--------------------------------------------------------------------------------------------- exact H104.
--------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
exact H105.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out K H G) as H103.
------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (K) (H) (G)).
--------------------------------------------------------------------------------------------right.
right.
exact H101.

-------------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H K D G K D) as H104.
-------------------------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (H) (K) (D) (H) (K) (D) (G) (D) (H98) (H103) H100).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G H F G K D) as H105.
--------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (G) (H) (F) (H) (K) (D) (G) (K) (D) (H89) H104).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A G K G K D) as H106.
---------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (G) (K) (G) (H) (F) (G) (K) (D) (H42) H105).
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H K) as H107.
----------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H2.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G H) as H108.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G))) as H108.
------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (K) (H) (G) H101).
------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G))) as H109.
-------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G)) as H111.
--------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
exact H33.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H M K) as H109.
------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (H) (M) (K)).
--------------------------------------------------------------------------------------------------intro H109.
apply (@euclidean__tactics.Col__nCol__False (H) (M) (K) (H109)).
---------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (H) (M) (K) (H21) (H107) H108).


------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H K M) as H110.
-------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M H K) /\ ((euclidean__axioms.Col M K H) /\ ((euclidean__axioms.Col K H M) /\ ((euclidean__axioms.Col H K M) /\ (euclidean__axioms.Col K M H))))) as H110.
--------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H) (M) (K) H109).
--------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M H K) /\ ((euclidean__axioms.Col M K H) /\ ((euclidean__axioms.Col K H M) /\ ((euclidean__axioms.Col H K M) /\ (euclidean__axioms.Col K M H))))) as H111.
---------------------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.Col M K H) /\ ((euclidean__axioms.Col K H M) /\ ((euclidean__axioms.Col H K M) /\ (euclidean__axioms.Col K M H)))) as H113.
----------------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Col K H M) /\ ((euclidean__axioms.Col H K M) /\ (euclidean__axioms.Col K M H))) as H115.
------------------------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------------------------ destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col H K M) /\ (euclidean__axioms.Col K M H)) as H117.
------------------------------------------------------------------------------------------------------- exact H116.
------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
exact H117.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H K G) as H111.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H G K) /\ ((euclidean__axioms.Col H K G) /\ ((euclidean__axioms.Col K G H) /\ ((euclidean__axioms.Col G K H) /\ (euclidean__axioms.Col K H G))))) as H111.
---------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (H) (K) H107).
---------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H G K) /\ ((euclidean__axioms.Col H K G) /\ ((euclidean__axioms.Col K G H) /\ ((euclidean__axioms.Col G K H) /\ (euclidean__axioms.Col K H G))))) as H112.
----------------------------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.Col H K G) /\ ((euclidean__axioms.Col K G H) /\ ((euclidean__axioms.Col G K H) /\ (euclidean__axioms.Col K H G)))) as H114.
------------------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------------------ destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Col K G H) /\ ((euclidean__axioms.Col G K H) /\ (euclidean__axioms.Col K H G))) as H116.
------------------------------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col G K H) /\ (euclidean__axioms.Col K H G)) as H118.
-------------------------------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
exact H114.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H K) as H112.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G))) as H112.
----------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (K) (H) (G) H101).
----------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G))) as H113.
------------------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------------------ destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G)) as H115.
------------------------------------------------------------------------------------------------------- exact H114.
------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
exact H81.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K M G) as H113.
----------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (K) (M) (G)).
------------------------------------------------------------------------------------------------------intro H113.
apply (@euclidean__tactics.Col__nCol__False (K) (M) (G) (H113)).
-------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (H) (K) (M) (G) (H110) (H111) H112).


----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G K M) as H114.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col M K G) /\ ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G K M) /\ ((euclidean__axioms.Col K G M) /\ (euclidean__axioms.Col G M K))))) as H114.
------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (K) (M) (G) H113).
------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M K G) /\ ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G K M) /\ ((euclidean__axioms.Col K G M) /\ (euclidean__axioms.Col G M K))))) as H115.
-------------------------------------------------------------------------------------------------------- exact H114.
-------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G K M) /\ ((euclidean__axioms.Col K G M) /\ (euclidean__axioms.Col G M K)))) as H117.
--------------------------------------------------------------------------------------------------------- exact H116.
--------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Col G K M) /\ ((euclidean__axioms.Col K G M) /\ (euclidean__axioms.Col G M K))) as H119.
---------------------------------------------------------------------------------------------------------- exact H118.
---------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.Col K G M) /\ (euclidean__axioms.Col G M K)) as H121.
----------------------------------------------------------------------------------------------------------- exact H120.
----------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
exact H119.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H K G) as H115.
------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col K M G) /\ ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G))))) as H115.
-------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (K) (M) H114).
-------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col K M G) /\ ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G))))) as H116.
--------------------------------------------------------------------------------------------------------- exact H115.
--------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Col K M G) /\ ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G)))) as H118.
---------------------------------------------------------------------------------------------------------- exact H117.
---------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G))) as H120.
----------------------------------------------------------------------------------------------------------- exact H119.
----------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G)) as H122.
------------------------------------------------------------------------------------------------------------ exact H121.
------------------------------------------------------------------------------------------------------------ destruct H122 as [H122 H123].
exact H111.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K N G) as H116.
-------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (K) (N) (G)).
---------------------------------------------------------------------------------------------------------intro H116.
apply (@euclidean__tactics.Col__nCol__False (K) (N) (G) (H116)).
----------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (H) (K) (N) (G) (H27) (H115) H112).


-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G K N) as H117.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col N K G) /\ ((euclidean__axioms.Col N G K) /\ ((euclidean__axioms.Col G K N) /\ ((euclidean__axioms.Col K G N) /\ (euclidean__axioms.Col G N K))))) as H117.
---------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (K) (N) (G) H116).
---------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col N K G) /\ ((euclidean__axioms.Col N G K) /\ ((euclidean__axioms.Col G K N) /\ ((euclidean__axioms.Col K G N) /\ (euclidean__axioms.Col G N K))))) as H118.
----------------------------------------------------------------------------------------------------------- exact H117.
----------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.Col N G K) /\ ((euclidean__axioms.Col G K N) /\ ((euclidean__axioms.Col K G N) /\ (euclidean__axioms.Col G N K)))) as H120.
------------------------------------------------------------------------------------------------------------ exact H119.
------------------------------------------------------------------------------------------------------------ destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.Col G K N) /\ ((euclidean__axioms.Col K G N) /\ (euclidean__axioms.Col G N K))) as H122.
------------------------------------------------------------------------------------------------------------- exact H121.
------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col K G N) /\ (euclidean__axioms.Col G N K)) as H124.
-------------------------------------------------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
exact H122.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A G K) as H118.
---------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (G) (K)).
-----------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (G) (K)).
------------------------------------------------------------------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (G) (H) (A) (G) (K) H40).


---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G K A) as H119.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G A K) /\ ((euclidean__axioms.nCol G K A) /\ ((euclidean__axioms.nCol K A G) /\ ((euclidean__axioms.nCol A K G) /\ (euclidean__axioms.nCol K G A))))) as H119.
------------------------------------------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (A) (G) (K) H118).
------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol G A K) /\ ((euclidean__axioms.nCol G K A) /\ ((euclidean__axioms.nCol K A G) /\ ((euclidean__axioms.nCol A K G) /\ (euclidean__axioms.nCol K G A))))) as H120.
------------------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.nCol G K A) /\ ((euclidean__axioms.nCol K A G) /\ ((euclidean__axioms.nCol A K G) /\ (euclidean__axioms.nCol K G A)))) as H122.
-------------------------------------------------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.nCol K A G) /\ ((euclidean__axioms.nCol A K G) /\ (euclidean__axioms.nCol K G A))) as H124.
--------------------------------------------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.nCol A K G) /\ (euclidean__axioms.nCol K G A)) as H126.
---------------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
exact H122.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H K C) as H120.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol K G A) /\ ((euclidean__axioms.nCol K A G) /\ ((euclidean__axioms.nCol A G K) /\ ((euclidean__axioms.nCol G A K) /\ (euclidean__axioms.nCol A K G))))) as H120.
------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (G) (K) (A) H119).
------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol K G A) /\ ((euclidean__axioms.nCol K A G) /\ ((euclidean__axioms.nCol A G K) /\ ((euclidean__axioms.nCol G A K) /\ (euclidean__axioms.nCol A K G))))) as H121.
-------------------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.nCol K A G) /\ ((euclidean__axioms.nCol A G K) /\ ((euclidean__axioms.nCol G A K) /\ (euclidean__axioms.nCol A K G)))) as H123.
--------------------------------------------------------------------------------------------------------------- exact H122.
--------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.nCol A G K) /\ ((euclidean__axioms.nCol G A K) /\ (euclidean__axioms.nCol A K G))) as H125.
---------------------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.nCol G A K) /\ (euclidean__axioms.nCol A K G)) as H127.
----------------------------------------------------------------------------------------------------------------- exact H126.
----------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
exact H82.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H K G) as H121.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K G N) /\ ((euclidean__axioms.Col K N G) /\ ((euclidean__axioms.Col N G K) /\ ((euclidean__axioms.Col G N K) /\ (euclidean__axioms.Col N K G))))) as H121.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (K) (N) H117).
-------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col K G N) /\ ((euclidean__axioms.Col K N G) /\ ((euclidean__axioms.Col N G K) /\ ((euclidean__axioms.Col G N K) /\ (euclidean__axioms.Col N K G))))) as H122.
--------------------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col K N G) /\ ((euclidean__axioms.Col N G K) /\ ((euclidean__axioms.Col G N K) /\ (euclidean__axioms.Col N K G)))) as H124.
---------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.Col N G K) /\ ((euclidean__axioms.Col G N K) /\ (euclidean__axioms.Col N K G))) as H126.
----------------------------------------------------------------------------------------------------------------- exact H125.
----------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col G N K) /\ (euclidean__axioms.Col N K G)) as H128.
------------------------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------------------------ destruct H128 as [H128 H129].
exact H115.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H K K) as H122.
-------------------------------------------------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G K) as H123.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G K) /\ ((euclidean__axioms.neq P G) /\ (euclidean__axioms.neq P K))) as H123.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (G) (K) H16).
---------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq G K) /\ ((euclidean__axioms.neq P G) /\ (euclidean__axioms.neq P K))) as H124.
----------------------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.neq P G) /\ (euclidean__axioms.neq P K)) as H126.
------------------------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------------------------ destruct H126 as [H126 H127].
exact H124.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G K C) as H124.
---------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (G) (K) (C)).
-----------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (G) (K) (C)).
------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (H) (K) (C) (G) (K) (H120) (H121) (H122) H123).


---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A C G K) as H125.
----------------------------------------------------------------------------------------------------------------- exists F.
exists M.
exists N.
split.
------------------------------------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------- exact H19.
-------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------- exact H43.
--------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------- exact H119.
---------------------------------------------------------------------------------------------------------------------- exact H124.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G K K) as H126.
------------------------------------------------------------------------------------------------------------------ right.
right.
left.
exact H92.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS C G K D) as H127.
------------------------------------------------------------------------------------------------------------------- exists K.
split.
-------------------------------------------------------------------------------------------------------------------- exact H5.
-------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------------------- exact H124.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS A G K D) as H128.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation (G) (K) (A) (C) (D) (H125) H127).
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H129.
--------------------------------------------------------------------------------------------------------------------- apply (@proposition__27.proposition__27 (A) (B) (C) (D) (G) (K) (H3) (H5) (H106) H128).
--------------------------------------------------------------------------------------------------------------------- exact H129.
Qed.
