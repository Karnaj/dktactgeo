Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__Playfairhelper.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__crisscross.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Definition lemma__Playfairhelper2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__defs.Par A B C D) -> ((euclidean__defs.Par A B C E) -> ((euclidean__defs.CR A D B C) -> (euclidean__axioms.Col C D E))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.neq A B) as H2.
- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H2.
-- exact H0.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
--- exact H2.
--- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H3.
---- exact __TmpHyp.
---- destruct H3 as [x H3].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H4.
----- exact H3.
----- destruct H4 as [x0 H4].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H5.
------ exact H4.
------ destruct H5 as [x1 H5].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H6.
------- exact H5.
------- destruct H6 as [x2 H6].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H7.
-------- exact H6.
-------- destruct H7 as [x3 H7].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H18.
-------------- exact H17.
-------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H20.
--------------- exact H19.
--------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H22.
---------------- exact H21.
---------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H24.
----------------- exact H23.
----------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H26.
------------------ exact H25.
------------------ destruct H26 as [H26 H27].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H28.
------------------- exact H.
------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
-------------------- exact H28.
-------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H29.
--------------------- exact __TmpHyp0.
--------------------- destruct H29 as [x4 H29].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H30.
---------------------- exact H29.
---------------------- destruct H30 as [x5 H30].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [x6 H31].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H32.
------------------------ exact H31.
------------------------ destruct H32 as [x7 H32].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H33.
------------------------- exact H32.
------------------------- destruct H33 as [x8 H33].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H34.
-------------------------- exact H33.
-------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H36.
--------------------------- exact H35.
--------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H38.
---------------------------- exact H37.
---------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H40.
----------------------------- exact H39.
----------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H42.
------------------------------ exact H41.
------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H44.
------------------------------- exact H43.
------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H46.
-------------------------------- exact H45.
-------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H48.
--------------------------------- exact H47.
--------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H50.
---------------------------------- exact H49.
---------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H52.
----------------------------------- exact H51.
----------------------------------- destruct H52 as [H52 H53].
exact H34.
- assert (* Cut *) (euclidean__axioms.neq C D) as H3.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H3.
--- exact H0.
--- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
---- exact H3.
---- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H4.
----- exact __TmpHyp.
----- destruct H4 as [x H4].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H5.
------ exact H4.
------ destruct H5 as [x0 H5].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H6.
------- exact H5.
------- destruct H6 as [x1 H6].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H7.
-------- exact H6.
-------- destruct H7 as [x2 H7].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H8.
--------- exact H7.
--------- destruct H8 as [x3 H8].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H9.
---------- exact H8.
---------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H25.
------------------ exact H24.
------------------ destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H27.
------------------- exact H26.
------------------- destruct H27 as [H27 H28].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H29.
-------------------- exact H.
-------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
--------------------- exact H29.
--------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H30.
---------------------- exact __TmpHyp0.
---------------------- destruct H30 as [x4 H30].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [x5 H31].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H32.
------------------------ exact H31.
------------------------ destruct H32 as [x6 H32].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H33.
------------------------- exact H32.
------------------------- destruct H33 as [x7 H33].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H34.
-------------------------- exact H33.
-------------------------- destruct H34 as [x8 H34].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H35.
--------------------------- exact H34.
--------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H37.
---------------------------- exact H36.
---------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H39.
----------------------------- exact H38.
----------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H41.
------------------------------ exact H40.
------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H43.
------------------------------- exact H42.
------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H45.
-------------------------------- exact H44.
-------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H47.
--------------------------------- exact H46.
--------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H49.
---------------------------------- exact H48.
---------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H51.
----------------------------------- exact H50.
----------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H53.
------------------------------------ exact H52.
------------------------------------ destruct H53 as [H53 H54].
exact H37.
-- assert (* Cut *) (~(~((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)))) as H4.
--- intro H4.
assert (* Cut *) (euclidean__defs.Par A B E C) as H5.
---- assert (* Cut *) ((euclidean__defs.Par B A C E) /\ ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C))) as H5.
----- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (C) (E) H0).
----- assert (* AndElim *) ((euclidean__defs.Par B A C E) /\ ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C))) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C)) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
exact H8.
---- assert (* Cut *) (euclidean__defs.CR A C E B) as H6.
----- apply (@lemma__crisscross.lemma__crisscross (A) (E) (B) (C) (H5)).
------intro H6.
apply (@H4).
-------left.
exact H6.


----- apply (@H4).
------right.
exact H6.

--- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS B M C)) as H5.
---- exact H1.
---- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS B M C))) as H6.
----- exact H5.
----- destruct H6 as [M H6].
assert (* AndElim *) ((euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS B M C)) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* Cut *) (euclidean__axioms.Col C D E) as H9.
------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H9.
-------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B))).
---------intro H9.
assert (* Cut *) (False) as H10.
---------- apply (@H4 H9).
---------- assert (* Cut *) ((euclidean__defs.CR A E B C) -> False) as H11.
----------- intro H11.
apply (@H9).
------------left.
exact H11.

----------- assert (* Cut *) ((euclidean__defs.CR A C E B) -> False) as H12.
------------ intro H12.
apply (@H9).
-------------right.
exact H12.

------------ assert False.
-------------exact H10.
------------- contradiction.

-------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H10.
--------- exact H9.
--------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as __TmpHyp.
---------- exact H10.
---------- assert (euclidean__defs.CR A E B C \/ euclidean__defs.CR A C E B) as H11.
----------- exact __TmpHyp.
----------- destruct H11 as [H11|H11].
------------ assert (* Cut *) (euclidean__axioms.Col C D E) as H12.
------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H12.
-------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------- apply (@euclidean__tactics.not__nCol__Col (C) (D) (E)).
---------------intro H13.
apply (@euclidean__tactics.Col__nCol__False (C) (D) (E) (H13)).
----------------apply (@lemma__Playfairhelper.lemma__Playfairhelper (A) (B) (C) (D) (E) (H) (H0) (H1) H11).


------------- exact H12.
------------ assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS A m C) /\ (euclidean__axioms.BetS E m B)) as H12.
------------- exact H11.
------------- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS A m C) /\ (euclidean__axioms.BetS E m B))) as H13.
-------------- exact H12.
-------------- destruct H13 as [m H13].
assert (* AndElim *) ((euclidean__axioms.BetS A m C) /\ (euclidean__axioms.BetS E m B)) as H14.
--------------- exact H13.
--------------- destruct H14 as [H14 H15].
assert (* Cut *) (euclidean__axioms.BetS B m E) as H16.
---------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H16.
----------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (m) (B) H15).
---------------- assert (* Cut *) (euclidean__axioms.neq C E) as H17.
----------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H17.
------------------ exact H0.
------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------- exact H17.
------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H18.
-------------------- exact __TmpHyp0.
-------------------- destruct H18 as [x H18].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H19.
--------------------- exact H18.
--------------------- destruct H19 as [x0 H19].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H20.
---------------------- exact H19.
---------------------- destruct H20 as [x1 H20].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H21.
----------------------- exact H20.
----------------------- destruct H21 as [x2 H21].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H22.
------------------------ exact H21.
------------------------ destruct H22 as [x3 H22].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H23.
------------------------- exact H22.
------------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H25.
-------------------------- exact H24.
-------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H27.
--------------------------- exact H26.
--------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H29.
---------------------------- exact H28.
---------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H31.
----------------------------- exact H30.
----------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H43.
----------------------------------- exact H.
----------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
------------------------------------ exact H43.
------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H44.
------------------------------------- exact __TmpHyp1.
------------------------------------- destruct H44 as [x4 H44].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [x5 H45].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [x6 H46].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H47.
---------------------------------------- exact H46.
---------------------------------------- destruct H47 as [x7 H47].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H48.
----------------------------------------- exact H47.
----------------------------------------- destruct H48 as [x8 H48].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H51.
------------------------------------------- exact H50.
------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H53.
-------------------------------------------- exact H52.
-------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H55.
--------------------------------------------- exact H54.
--------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H57.
---------------------------------------------- exact H56.
---------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H59.
----------------------------------------------- exact H58.
----------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H61.
------------------------------------------------ exact H60.
------------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H63.
------------------------------------------------- exact H62.
------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H65.
-------------------------------------------------- exact H64.
-------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H67.
--------------------------------------------------- exact H66.
--------------------------------------------------- destruct H67 as [H67 H68].
exact H25.
----------------- assert (* Cut *) (euclidean__axioms.neq E C) as H18.
------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H18.
------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (E) H17).
------------------ assert (* Cut *) (exists (e: euclidean__axioms.Point), (euclidean__axioms.BetS E C e) /\ (euclidean__axioms.Cong C e E C)) as H19.
------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H19.
-------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------- apply (@lemma__extension.lemma__extension (E) (C) (E) (C) (H18) H18).
------------------- assert (exists e: euclidean__axioms.Point, ((euclidean__axioms.BetS E C e) /\ (euclidean__axioms.Cong C e E C))) as H20.
-------------------- exact H19.
-------------------- destruct H20 as [e H20].
assert (* AndElim *) ((euclidean__axioms.BetS E C e) /\ (euclidean__axioms.Cong C e E C)) as H21.
--------------------- exact H20.
--------------------- destruct H21 as [H21 H22].
assert (* Cut *) (euclidean__axioms.Col E C e) as H23.
---------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H23.
----------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------- right.
right.
right.
right.
left.
exact H21.
---------------------- assert (* Cut *) (euclidean__axioms.neq C e) as H24.
----------------------- assert (* Cut *) ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E e))) as H24.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (E) (C) (e) H21).
------------------------ assert (* AndElim *) ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E e))) as H25.
------------------------- exact H24.
------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E e)) as H27.
-------------------------- exact H26.
-------------------------- destruct H27 as [H27 H28].
exact H25.
----------------------- assert (* Cut *) (euclidean__axioms.neq e C) as H25.
------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H25.
------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (e) H24).
------------------------ assert (* Cut *) (euclidean__defs.Par A B E C) as H26.
------------------------- assert (* Cut *) ((euclidean__defs.Par B A C E) /\ ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C))) as H26.
-------------------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (C) (E) H0).
-------------------------- assert (* AndElim *) ((euclidean__defs.Par B A C E) /\ ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C))) as H27.
--------------------------- exact H26.
--------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C)) as H29.
---------------------------- exact H28.
---------------------------- destruct H29 as [H29 H30].
exact H29.
------------------------- assert (* Cut *) (euclidean__defs.Par A B e C) as H27.
-------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H27.
--------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (A) (B) (e) (E) (C) (H26) (H23) H25).
-------------------------- assert (* Cut *) (euclidean__defs.Par A B C e) as H28.
--------------------------- assert (* Cut *) ((euclidean__defs.Par B A e C) /\ ((euclidean__defs.Par A B C e) /\ (euclidean__defs.Par B A C e))) as H28.
---------------------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (e) (C) H27).
---------------------------- assert (* AndElim *) ((euclidean__defs.Par B A e C) /\ ((euclidean__defs.Par A B C e) /\ (euclidean__defs.Par B A C e))) as H29.
----------------------------- exact H28.
----------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__defs.Par A B C e) /\ (euclidean__defs.Par B A C e)) as H31.
------------------------------ exact H30.
------------------------------ destruct H31 as [H31 H32].
exact H31.
--------------------------- assert (* Cut *) (euclidean__axioms.nCol A C D) as H29.
---------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H29.
----------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (C) (D) H).
----------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H30.
------------------------------ exact H29.
------------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D))) as H32.
------------------------------- exact H31.
------------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)) as H34.
-------------------------------- exact H33.
-------------------------------- destruct H34 as [H34 H35].
exact H32.
---------------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H30.
----------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C e) /\ ((euclidean__axioms.nCol B C e) /\ (euclidean__axioms.nCol A B e)))) as H30.
------------------------------ apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (C) (e) H28).
------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C e) /\ ((euclidean__axioms.nCol B C e) /\ (euclidean__axioms.nCol A B e)))) as H31.
------------------------------- exact H30.
------------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.nCol A C e) /\ ((euclidean__axioms.nCol B C e) /\ (euclidean__axioms.nCol A B e))) as H33.
-------------------------------- exact H32.
-------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.nCol B C e) /\ (euclidean__axioms.nCol A B e)) as H35.
--------------------------------- exact H34.
--------------------------------- destruct H35 as [H35 H36].
exact H31.
----------------------------- assert (* Cut *) (euclidean__axioms.nCol B C A) as H31.
------------------------------ assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H31.
------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H30).
------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H32.
-------------------------------- exact H31.
-------------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H34.
--------------------------------- exact H33.
--------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H36.
---------------------------------- exact H35.
---------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H38.
----------------------------------- exact H37.
----------------------------------- destruct H38 as [H38 H39].
exact H34.
------------------------------ assert (* Cut *) (exists (H32: euclidean__axioms.Point), (euclidean__axioms.BetS B H32 m) /\ (euclidean__axioms.BetS A H32 M)) as H32.
------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H32.
-------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (B) (A) (C) (M) (m) (H8) (H14) H31).
------------------------------- assert (exists H33: euclidean__axioms.Point, ((euclidean__axioms.BetS B H33 m) /\ (euclidean__axioms.BetS A H33 M))) as H34.
-------------------------------- exact H32.
-------------------------------- destruct H34 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.BetS B H33 m) /\ (euclidean__axioms.BetS A H33 M)) as H35.
--------------------------------- exact H34.
--------------------------------- destruct H35 as [H35 H36].
assert (* Cut *) (euclidean__axioms.nCol A E C) as H37.
---------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol A B C)))) as H37.
----------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (E) (C) H26).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol A B C)))) as H38.
------------------------------------ exact H37.
------------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol A B C))) as H40.
------------------------------------- exact H39.
------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol A B C)) as H42.
-------------------------------------- exact H41.
-------------------------------------- destruct H42 as [H42 H43].
exact H40.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col E C e) as H38.
----------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H38.
------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------ exact H23.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col C E e) as H39.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C E e) /\ ((euclidean__axioms.Col C e E) /\ ((euclidean__axioms.Col e E C) /\ ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E))))) as H39.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (C) (e) H38).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C E e) /\ ((euclidean__axioms.Col C e E) /\ ((euclidean__axioms.Col e E C) /\ ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E))))) as H40.
-------------------------------------- exact H39.
-------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col C e E) /\ ((euclidean__axioms.Col e E C) /\ ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E)))) as H42.
--------------------------------------- exact H41.
--------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col e E C) /\ ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E))) as H44.
---------------------------------------- exact H43.
---------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E)) as H46.
----------------------------------------- exact H45.
----------------------------------------- destruct H46 as [H46 H47].
exact H40.
------------------------------------ assert (* Cut *) (euclidean__axioms.neq C E) as H40.
------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H40.
-------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------------- exact H17.
------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E A) as H41.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A))))) as H41.
--------------------------------------- apply (@lemma__NCorder.lemma__NCorder (A) (E) (C) H37).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A))))) as H42.
---------------------------------------- exact H41.
---------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A)))) as H44.
----------------------------------------- exact H43.
----------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A))) as H46.
------------------------------------------ exact H45.
------------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A)) as H48.
------------------------------------------- exact H47.
------------------------------------------- destruct H48 as [H48 H49].
exact H49.
-------------------------------------- assert (* Cut *) (E = E) as H42.
--------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H42.
---------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------------------------------- apply (@logic.eq__refl (Point) E).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col C E E) as H43.
---------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H43.
----------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------------------------- right.
right.
left.
exact H42.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq E e) as H44.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E e))) as H44.
------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (E) (C) (e) H21).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E e))) as H45.
------------------------------------------- exact H44.
------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E e)) as H47.
-------------------------------------------- exact H46.
-------------------------------------------- destruct H47 as [H47 H48].
exact H48.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E e A) as H45.
------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H45.
------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------- apply (@euclidean__tactics.nCol__notCol (E) (e) (A)).
--------------------------------------------apply (@euclidean__tactics.nCol__not__Col (E) (e) (A)).
---------------------------------------------apply (@lemma__NChelper.lemma__NChelper (C) (E) (A) (E) (e) (H41) (H43) (H39) H44).


------------------------------------------ assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS A F e) /\ (euclidean__axioms.BetS E m F)) as H46.
------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H46.
-------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (A) (E) (C) (m) (e) (H14) (H21) H45).
------------------------------------------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS A F e) /\ (euclidean__axioms.BetS E m F))) as H47.
-------------------------------------------- exact H46.
-------------------------------------------- destruct H47 as [F H47].
assert (* AndElim *) ((euclidean__axioms.BetS A F e) /\ (euclidean__axioms.BetS E m F)) as H48.
--------------------------------------------- exact H47.
--------------------------------------------- destruct H48 as [H48 H49].
assert (* Cut *) (euclidean__axioms.BetS e F A) as H50.
---------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H50.
----------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (F) (e) H48).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E m F) as H51.
----------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H51.
------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------ right.
right.
right.
right.
left.
exact H49.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E m B) as H52.
------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H52.
------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------- right.
right.
right.
right.
left.
exact H15.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col m E F) as H53.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m E F) /\ ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))))) as H53.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (m) (F) H51).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m E F) /\ ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))))) as H54.
--------------------------------------------------- exact H53.
--------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E)))) as H56.
---------------------------------------------------- exact H55.
---------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))) as H58.
----------------------------------------------------- exact H57.
----------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E)) as H60.
------------------------------------------------------ exact H59.
------------------------------------------------------ destruct H60 as [H60 H61].
exact H54.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m E B) as H54.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m E B) /\ ((euclidean__axioms.Col m B E) /\ ((euclidean__axioms.Col B E m) /\ ((euclidean__axioms.Col E B m) /\ (euclidean__axioms.Col B m E))))) as H54.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (m) (B) H52).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col m E B) /\ ((euclidean__axioms.Col m B E) /\ ((euclidean__axioms.Col B E m) /\ ((euclidean__axioms.Col E B m) /\ (euclidean__axioms.Col B m E))))) as H55.
---------------------------------------------------- exact H54.
---------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col m B E) /\ ((euclidean__axioms.Col B E m) /\ ((euclidean__axioms.Col E B m) /\ (euclidean__axioms.Col B m E)))) as H57.
----------------------------------------------------- exact H56.
----------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col B E m) /\ ((euclidean__axioms.Col E B m) /\ (euclidean__axioms.Col B m E))) as H59.
------------------------------------------------------ exact H58.
------------------------------------------------------ destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col E B m) /\ (euclidean__axioms.Col B m E)) as H61.
------------------------------------------------------- exact H60.
------------------------------------------------------- destruct H61 as [H61 H62].
exact H55.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E m) as H55.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F))) as H55.
---------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (m) (F) H49).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F))) as H56.
----------------------------------------------------- exact H55.
----------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F)) as H58.
------------------------------------------------------ exact H57.
------------------------------------------------------ destruct H58 as [H58 H59].
exact H58.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq m E) as H56.
---------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H56.
----------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (m) H55).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F B) as H57.
----------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H57.
------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (E) (F) (B)).
-------------------------------------------------------intro H58.
apply (@euclidean__tactics.Col__nCol__False (E) (F) (B) (H58)).
--------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (m) (E) (F) (B) (H53) (H54) H56).


----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B F) as H58.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col F E B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B E F) /\ ((euclidean__axioms.Col E B F) /\ (euclidean__axioms.Col B F E))))) as H58.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (F) (B) H57).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F E B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B E F) /\ ((euclidean__axioms.Col E B F) /\ (euclidean__axioms.Col B F E))))) as H59.
-------------------------------------------------------- exact H58.
-------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B E F) /\ ((euclidean__axioms.Col E B F) /\ (euclidean__axioms.Col B F E)))) as H61.
--------------------------------------------------------- exact H60.
--------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col B E F) /\ ((euclidean__axioms.Col E B F) /\ (euclidean__axioms.Col B F E))) as H63.
---------------------------------------------------------- exact H62.
---------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col E B F) /\ (euclidean__axioms.Col B F E)) as H65.
----------------------------------------------------------- exact H64.
----------------------------------------------------------- destruct H65 as [H65 H66].
exact H65.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq e E) as H59.
------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H59.
-------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (e) H44).
------------------------------------------------------- assert (* Cut *) (E = E) as H60.
-------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H60.
--------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------------------------------------------- exact H42.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e E E) as H61.
--------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H61.
---------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------------------------------------------------- right.
right.
left.
exact H60.
--------------------------------------------------------- assert (* Cut *) (B = B) as H62.
---------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H62.
----------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------------------------------------------- apply (@logic.eq__refl (Point) B).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B B A) as H63.
----------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H63.
------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------------ left.
exact H62.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H64.
------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H64.
------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H2).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par A B C E) as H65.
------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par B A C e) /\ ((euclidean__defs.Par A B e C) /\ (euclidean__defs.Par B A e C))) as H65.
-------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (C) (e) H28).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par B A C e) /\ ((euclidean__defs.Par A B e C) /\ (euclidean__defs.Par B A e C))) as H66.
--------------------------------------------------------------- exact H65.
--------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__defs.Par A B e C) /\ (euclidean__defs.Par B A e C)) as H68.
---------------------------------------------------------------- exact H67.
---------------------------------------------------------------- destruct H68 as [H68 H69].
exact H0.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C E e) as H66.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B B A) /\ ((euclidean__axioms.Col B A B) /\ ((euclidean__axioms.Col A B B) /\ ((euclidean__axioms.Col B A B) /\ (euclidean__axioms.Col A B B))))) as H66.
--------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (B) (A) H63).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B B A) /\ ((euclidean__axioms.Col B A B) /\ ((euclidean__axioms.Col A B B) /\ ((euclidean__axioms.Col B A B) /\ (euclidean__axioms.Col A B B))))) as H67.
---------------------------------------------------------------- exact H66.
---------------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col B A B) /\ ((euclidean__axioms.Col A B B) /\ ((euclidean__axioms.Col B A B) /\ (euclidean__axioms.Col A B B)))) as H69.
----------------------------------------------------------------- exact H68.
----------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A B B) /\ ((euclidean__axioms.Col B A B) /\ (euclidean__axioms.Col A B B))) as H71.
------------------------------------------------------------------ exact H70.
------------------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col B A B) /\ (euclidean__axioms.Col A B B)) as H73.
------------------------------------------------------------------- exact H72.
------------------------------------------------------------------- destruct H73 as [H73 H74].
exact H39.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B e E) as H67.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H67.
---------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (A) (B) (e) (C) (E) (H65) (H66) H59).
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par e E A B) as H68.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H68.
----------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (B) (e) (E) H67).
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par e E B A) as H69.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par E e A B) /\ ((euclidean__defs.Par e E B A) /\ (euclidean__defs.Par E e B A))) as H69.
------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip (e) (E) (A) (B) H68).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__defs.Par E e A B) /\ ((euclidean__defs.Par e E B A) /\ (euclidean__defs.Par E e B A))) as H70.
------------------------------------------------------------------- exact H69.
------------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__defs.Par e E B A) /\ (euclidean__defs.Par E e B A)) as H72.
-------------------------------------------------------------------- exact H71.
-------------------------------------------------------------------- destruct H72 as [H72 H73].
exact H72.
----------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet e E B A)) as H70.
------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col e E U) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H70.
------------------------------------------------------------------- exact H69.
------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col e E U) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
-------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col e E U) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H71.
--------------------------------------------------------------------- exact __TmpHyp0.
--------------------------------------------------------------------- destruct H71 as [x H71].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col e E x) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H72.
---------------------------------------------------------------------- exact H71.
---------------------------------------------------------------------- destruct H72 as [x0 H72].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col e E x) /\ ((euclidean__axioms.Col e E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H73.
----------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------- destruct H73 as [x1 H73].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col e E x) /\ ((euclidean__axioms.Col e E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B A x1) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H74.
------------------------------------------------------------------------ exact H73.
------------------------------------------------------------------------ destruct H74 as [x2 H74].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col e E x) /\ ((euclidean__axioms.Col e E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B A x1) /\ ((euclidean__axioms.Col B A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H75.
------------------------------------------------------------------------- exact H74.
------------------------------------------------------------------------- destruct H75 as [x3 H75].
assert (* AndElim *) ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col e E x) /\ ((euclidean__axioms.Col e E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B A x1) /\ ((euclidean__axioms.Col B A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H76.
-------------------------------------------------------------------------- exact H75.
-------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col e E x) /\ ((euclidean__axioms.Col e E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B A x1) /\ ((euclidean__axioms.Col B A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H78.
--------------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col e E x) /\ ((euclidean__axioms.Col e E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B A x1) /\ ((euclidean__axioms.Col B A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H80.
---------------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.Col e E x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B A x1) /\ ((euclidean__axioms.Col B A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H82.
----------------------------------------------------------------------------- exact H81.
----------------------------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B A x1) /\ ((euclidean__axioms.Col B A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H84.
------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------ destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col B A x1) /\ ((euclidean__axioms.Col B A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H86.
------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col B A x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H88.
-------------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H90.
--------------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((~(euclidean__defs.Meet e E B A)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H92.
---------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H94.
----------------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col e E U) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H96.
------------------------------------------------------------------------------------ exact H68.
------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col e E U) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1.
------------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col e E U) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H97.
-------------------------------------------------------------------------------------- exact __TmpHyp1.
-------------------------------------------------------------------------------------- destruct H97 as [x4 H97].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col e E x4) /\ ((euclidean__axioms.Col e E V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H98.
--------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------- destruct H98 as [x5 H98].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col e E x4) /\ ((euclidean__axioms.Col e E x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H99.
---------------------------------------------------------------------------------------- exact H98.
---------------------------------------------------------------------------------------- destruct H99 as [x6 H99].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col e E x4) /\ ((euclidean__axioms.Col e E x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A B x6) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H100.
----------------------------------------------------------------------------------------- exact H99.
----------------------------------------------------------------------------------------- destruct H100 as [x7 H100].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col e E x4) /\ ((euclidean__axioms.Col e E x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A B x6) /\ ((euclidean__axioms.Col A B x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H101.
------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------ destruct H101 as [x8 H101].
assert (* AndElim *) ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col e E x4) /\ ((euclidean__axioms.Col e E x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A B x6) /\ ((euclidean__axioms.Col A B x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H102.
------------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col e E x4) /\ ((euclidean__axioms.Col e E x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A B x6) /\ ((euclidean__axioms.Col A B x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H104.
-------------------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Col e E x4) /\ ((euclidean__axioms.Col e E x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A B x6) /\ ((euclidean__axioms.Col A B x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H106.
--------------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.Col e E x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A B x6) /\ ((euclidean__axioms.Col A B x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H108.
---------------------------------------------------------------------------------------------- exact H107.
---------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col A B x6) /\ ((euclidean__axioms.Col A B x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H110.
----------------------------------------------------------------------------------------------- exact H109.
----------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((euclidean__axioms.Col A B x6) /\ ((euclidean__axioms.Col A B x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H112.
------------------------------------------------------------------------------------------------ exact H111.
------------------------------------------------------------------------------------------------ destruct H112 as [H112 H113].
assert (* AndElim *) ((euclidean__axioms.Col A B x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H114.
------------------------------------------------------------------------------------------------- exact H113.
------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H116.
-------------------------------------------------------------------------------------------------- exact H115.
-------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((~(euclidean__defs.Meet e E A B)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H118.
--------------------------------------------------------------------------------------------------- exact H117.
--------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H120.
---------------------------------------------------------------------------------------------------- exact H119.
---------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e E u) /\ ((euclidean__axioms.Col e E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H122.
----------------------------------------------------------------------------------------------------- exact H67.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e E u) /\ ((euclidean__axioms.Col e E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2.
------------------------------------------------------------------------------------------------------ exact H122.
------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e E u) /\ ((euclidean__axioms.Col e E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H123.
------------------------------------------------------------------------------------------------------- exact __TmpHyp2.
------------------------------------------------------------------------------------------------------- destruct H123 as [x9 H123].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x9 V) /\ ((euclidean__axioms.Col e E u) /\ ((euclidean__axioms.Col e E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H124.
-------------------------------------------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------------------------------------------- destruct H124 as [x10 H124].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col e E u) /\ ((euclidean__axioms.Col e E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS u X x10)))))))))))) as H125.
--------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------- destruct H125 as [x11 H125].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col e E x11) /\ ((euclidean__axioms.Col e E v) /\ ((euclidean__axioms.neq x11 v) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 X v) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H126.
---------------------------------------------------------------------------------------------------------- exact H125.
---------------------------------------------------------------------------------------------------------- destruct H126 as [x12 H126].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col e E x11) /\ ((euclidean__axioms.Col e E x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 X x12) /\ (euclidean__axioms.BetS x11 X x10)))))))))))) as H127.
----------------------------------------------------------------------------------------------------------- exact H126.
----------------------------------------------------------------------------------------------------------- destruct H127 as [x13 H127].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col e E x11) /\ ((euclidean__axioms.Col e E x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))))) as H128.
------------------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------------------ destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.neq e E) /\ ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col e E x11) /\ ((euclidean__axioms.Col e E x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))))) as H130.
------------------------------------------------------------------------------------------------------------- exact H129.
------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Col A B x9) /\ ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col e E x11) /\ ((euclidean__axioms.Col e E x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))))) as H132.
-------------------------------------------------------------------------------------------------------------- exact H131.
-------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.Col A B x10) /\ ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col e E x11) /\ ((euclidean__axioms.Col e E x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))))) as H134.
--------------------------------------------------------------------------------------------------------------- exact H133.
--------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.neq x9 x10) /\ ((euclidean__axioms.Col e E x11) /\ ((euclidean__axioms.Col e E x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))))) as H136.
---------------------------------------------------------------------------------------------------------------- exact H135.
---------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Col e E x11) /\ ((euclidean__axioms.Col e E x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))))) as H138.
----------------------------------------------------------------------------------------------------------------- exact H137.
----------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col e E x12) /\ ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))))) as H140.
------------------------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------------------------ destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq x11 x12) /\ ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)))) as H142.
------------------------------------------------------------------------------------------------------------------- exact H141.
------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((~(euclidean__defs.Meet A B e E)) /\ ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10))) as H144.
-------------------------------------------------------------------------------------------------------------------- exact H143.
-------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.BetS x9 x13 x12) /\ (euclidean__axioms.BetS x11 x13 x10)) as H146.
--------------------------------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H148.
---------------------------------------------------------------------------------------------------------------------- exact H65.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3.
----------------------------------------------------------------------------------------------------------------------- exact H148.
----------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H149.
------------------------------------------------------------------------------------------------------------------------ exact __TmpHyp3.
------------------------------------------------------------------------------------------------------------------------ destruct H149 as [x14 H149].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x14 V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H150.
------------------------------------------------------------------------------------------------------------------------- exact H149.
------------------------------------------------------------------------------------------------------------------------- destruct H150 as [x15 H150].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS u X x15)))))))))))) as H151.
-------------------------------------------------------------------------------------------------------------------------- exact H150.
-------------------------------------------------------------------------------------------------------------------------- destruct H151 as [x16 H151].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C E x16) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq x16 v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 X v) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H152.
--------------------------------------------------------------------------------------------------------------------------- exact H151.
--------------------------------------------------------------------------------------------------------------------------- destruct H152 as [x17 H152].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C E x16) /\ ((euclidean__axioms.Col C E x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 X x17) /\ (euclidean__axioms.BetS x16 X x15)))))))))))) as H153.
---------------------------------------------------------------------------------------------------------------------------- exact H152.
---------------------------------------------------------------------------------------------------------------------------- destruct H153 as [x18 H153].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C E x16) /\ ((euclidean__axioms.Col C E x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))))) as H154.
----------------------------------------------------------------------------------------------------------------------------- exact H153.
----------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C E x16) /\ ((euclidean__axioms.Col C E x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))))) as H156.
------------------------------------------------------------------------------------------------------------------------------ exact H155.
------------------------------------------------------------------------------------------------------------------------------ destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.Col A B x14) /\ ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C E x16) /\ ((euclidean__axioms.Col C E x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))))) as H158.
------------------------------------------------------------------------------------------------------------------------------- exact H157.
------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.Col A B x15) /\ ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C E x16) /\ ((euclidean__axioms.Col C E x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))))) as H160.
-------------------------------------------------------------------------------------------------------------------------------- exact H159.
-------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.neq x14 x15) /\ ((euclidean__axioms.Col C E x16) /\ ((euclidean__axioms.Col C E x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))))) as H162.
--------------------------------------------------------------------------------------------------------------------------------- exact H161.
--------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((euclidean__axioms.Col C E x16) /\ ((euclidean__axioms.Col C E x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))))) as H164.
---------------------------------------------------------------------------------------------------------------------------------- exact H163.
---------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
assert (* AndElim *) ((euclidean__axioms.Col C E x17) /\ ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))))) as H166.
----------------------------------------------------------------------------------------------------------------------------------- exact H165.
----------------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H166 H167].
assert (* AndElim *) ((euclidean__axioms.neq x16 x17) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)))) as H168.
------------------------------------------------------------------------------------------------------------------------------------ exact H167.
------------------------------------------------------------------------------------------------------------------------------------ destruct H168 as [H168 H169].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15))) as H170.
------------------------------------------------------------------------------------------------------------------------------------- exact H169.
------------------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H170 H171].
assert (* AndElim *) ((euclidean__axioms.BetS x14 x18 x17) /\ (euclidean__axioms.BetS x16 x18 x15)) as H172.
-------------------------------------------------------------------------------------------------------------------------------------- exact H171.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H172 as [H172 H173].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C e u) /\ ((euclidean__axioms.Col C e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H174.
--------------------------------------------------------------------------------------------------------------------------------------- exact H28.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C e u) /\ ((euclidean__axioms.Col C e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4.
---------------------------------------------------------------------------------------------------------------------------------------- exact H174.
---------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C e u) /\ ((euclidean__axioms.Col C e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H175.
----------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp4.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [x19 H175].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.Col A B x19) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x19 V) /\ ((euclidean__axioms.Col C e u) /\ ((euclidean__axioms.Col C e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H176.
------------------------------------------------------------------------------------------------------------------------------------------ exact H175.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H176 as [x20 H176].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.Col A B x19) /\ ((euclidean__axioms.Col A B x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C e u) /\ ((euclidean__axioms.Col C e v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS u X x20)))))))))))) as H177.
------------------------------------------------------------------------------------------------------------------------------------------- exact H176.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [x21 H177].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.Col A B x19) /\ ((euclidean__axioms.Col A B x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C e x21) /\ ((euclidean__axioms.Col C e v) /\ ((euclidean__axioms.neq x21 v) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 X v) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H178.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H177.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [x22 H178].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.Col A B x19) /\ ((euclidean__axioms.Col A B x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C e x21) /\ ((euclidean__axioms.Col C e x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 X x22) /\ (euclidean__axioms.BetS x21 X x20)))))))))))) as H179.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H178.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [x23 H179].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.Col A B x19) /\ ((euclidean__axioms.Col A B x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C e x21) /\ ((euclidean__axioms.Col C e x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))))) as H180.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H179.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H180 H181].
assert (* AndElim *) ((euclidean__axioms.neq C e) /\ ((euclidean__axioms.Col A B x19) /\ ((euclidean__axioms.Col A B x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C e x21) /\ ((euclidean__axioms.Col C e x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))))) as H182.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H182 H183].
assert (* AndElim *) ((euclidean__axioms.Col A B x19) /\ ((euclidean__axioms.Col A B x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C e x21) /\ ((euclidean__axioms.Col C e x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))))) as H184.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H183.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H184 as [H184 H185].
assert (* AndElim *) ((euclidean__axioms.Col A B x20) /\ ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C e x21) /\ ((euclidean__axioms.Col C e x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))))) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H185.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H186 H187].
assert (* AndElim *) ((euclidean__axioms.neq x19 x20) /\ ((euclidean__axioms.Col C e x21) /\ ((euclidean__axioms.Col C e x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))))) as H188.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H187.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H188 H189].
assert (* AndElim *) ((euclidean__axioms.Col C e x21) /\ ((euclidean__axioms.Col C e x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))))) as H190.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H190 H191].
assert (* AndElim *) ((euclidean__axioms.Col C e x22) /\ ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))))) as H192.
---------------------------------------------------------------------------------------------------------------------------------------------------- exact H191.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H192 H193].
assert (* AndElim *) ((euclidean__axioms.neq x21 x22) /\ ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)))) as H194.
----------------------------------------------------------------------------------------------------------------------------------------------------- exact H193.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H194 as [H194 H195].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C e)) /\ ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20))) as H196.
------------------------------------------------------------------------------------------------------------------------------------------------------ exact H195.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H196 as [H196 H197].
assert (* AndElim *) ((euclidean__axioms.BetS x19 x23 x22) /\ (euclidean__axioms.BetS x21 x23 x20)) as H198.
------------------------------------------------------------------------------------------------------------------------------------------------------- exact H197.
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [H198 H199].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e C u) /\ ((euclidean__axioms.Col e C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H200.
-------------------------------------------------------------------------------------------------------------------------------------------------------- exact H27.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e C u) /\ ((euclidean__axioms.Col e C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5.
--------------------------------------------------------------------------------------------------------------------------------------------------------- exact H200.
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col e C u) /\ ((euclidean__axioms.Col e C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H201.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp5.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H201 as [x24 H201].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x24 V) /\ ((euclidean__axioms.Col e C u) /\ ((euclidean__axioms.Col e C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H202.
----------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [x25 H202].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col e C u) /\ ((euclidean__axioms.Col e C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS u X x25)))))))))))) as H203.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H202.
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H203 as [x26 H203].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col e C x26) /\ ((euclidean__axioms.Col e C v) /\ ((euclidean__axioms.neq x26 v) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 X v) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H204.
------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H203.
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H204 as [x27 H204].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col e C x26) /\ ((euclidean__axioms.Col e C x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 X x27) /\ (euclidean__axioms.BetS x26 X x25)))))))))))) as H205.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H204.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [x28 H205].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col e C x26) /\ ((euclidean__axioms.Col e C x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))))) as H206.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H205.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H206 H207].
assert (* AndElim *) ((euclidean__axioms.neq e C) /\ ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col e C x26) /\ ((euclidean__axioms.Col e C x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))))) as H208.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H207.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H208 as [H208 H209].
assert (* AndElim *) ((euclidean__axioms.Col A B x24) /\ ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col e C x26) /\ ((euclidean__axioms.Col e C x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))))) as H210.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H210 as [H210 H211].
assert (* AndElim *) ((euclidean__axioms.Col A B x25) /\ ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col e C x26) /\ ((euclidean__axioms.Col e C x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))))) as H212.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H212 as [H212 H213].
assert (* AndElim *) ((euclidean__axioms.neq x24 x25) /\ ((euclidean__axioms.Col e C x26) /\ ((euclidean__axioms.Col e C x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))))) as H214.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H213.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H214 H215].
assert (* AndElim *) ((euclidean__axioms.Col e C x26) /\ ((euclidean__axioms.Col e C x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))))) as H216.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H215.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H216 as [H216 H217].
assert (* AndElim *) ((euclidean__axioms.Col e C x27) /\ ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))))) as H218.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H217.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H218 as [H218 H219].
assert (* AndElim *) ((euclidean__axioms.neq x26 x27) /\ ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)))) as H220.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H219.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [H220 H221].
assert (* AndElim *) ((~(euclidean__defs.Meet A B e C)) /\ ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25))) as H222.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H221.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H222 as [H222 H223].
assert (* AndElim *) ((euclidean__axioms.BetS x24 x28 x27) /\ (euclidean__axioms.BetS x26 x28 x25)) as H224.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H223.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H224 as [H224 H225].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H226.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H26.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H226.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H227.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp6.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H227 as [x29 H227].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x29 V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H228.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H227.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H228 as [x30 H228].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS u X x30)))))))))))) as H229.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H228.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H229 as [x31 H229].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq x31 v) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 X v) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H230.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H229.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H230 as [x32 H230].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 X x32) /\ (euclidean__axioms.BetS x31 X x30)))))))))))) as H231.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H230.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [x33 H231].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))))) as H232.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H231.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H232 as [H232 H233].
assert (* AndElim *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))))) as H234.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H233.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H234 as [H234 H235].
assert (* AndElim *) ((euclidean__axioms.Col A B x29) /\ ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))))) as H236.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H235.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H236 as [H236 H237].
assert (* AndElim *) ((euclidean__axioms.Col A B x30) /\ ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))))) as H238.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H237.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H238 as [H238 H239].
assert (* AndElim *) ((euclidean__axioms.neq x29 x30) /\ ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))))) as H240.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H239.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H240 as [H240 H241].
assert (* AndElim *) ((euclidean__axioms.Col E C x31) /\ ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))))) as H242.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H241.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H242 as [H242 H243].
assert (* AndElim *) ((euclidean__axioms.Col E C x32) /\ ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))))) as H244.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H243.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H244 as [H244 H245].
assert (* AndElim *) ((euclidean__axioms.neq x31 x32) /\ ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)))) as H246.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H245.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H246 as [H246 H247].
assert (* AndElim *) ((~(euclidean__defs.Meet A B E C)) /\ ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30))) as H248.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H247.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H248 as [H248 H249].
assert (* AndElim *) ((euclidean__axioms.BetS x29 x33 x32) /\ (euclidean__axioms.BetS x31 x33 x30)) as H250.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H249.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H250 as [H250 H251].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H252.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H0.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H252.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H253.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp7.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H253 as [x34 H253].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x34 V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H254.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H253.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H254 as [x35 H254].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS u X x35)))))))))))) as H255.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H254.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H255 as [x36 H255].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C E x36) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq x36 v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 X v) /\ (euclidean__axioms.BetS x36 X x35)))))))))))) as H256.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H255.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H256 as [x37 H256].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C E x36) /\ ((euclidean__axioms.Col C E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 X x37) /\ (euclidean__axioms.BetS x36 X x35)))))))))))) as H257.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H256.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H257 as [x38 H257].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C E x36) /\ ((euclidean__axioms.Col C E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))))))) as H258.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H257.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H258 as [H258 H259].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C E x36) /\ ((euclidean__axioms.Col C E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))))))) as H260.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H259.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H260 as [H260 H261].
assert (* AndElim *) ((euclidean__axioms.Col A B x34) /\ ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C E x36) /\ ((euclidean__axioms.Col C E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))))) as H262.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H261.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H262 as [H262 H263].
assert (* AndElim *) ((euclidean__axioms.Col A B x35) /\ ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C E x36) /\ ((euclidean__axioms.Col C E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))))) as H264.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H263.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H264 as [H264 H265].
assert (* AndElim *) ((euclidean__axioms.neq x34 x35) /\ ((euclidean__axioms.Col C E x36) /\ ((euclidean__axioms.Col C E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))))) as H266.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H265.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H266 as [H266 H267].
assert (* AndElim *) ((euclidean__axioms.Col C E x36) /\ ((euclidean__axioms.Col C E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))))) as H268.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H267.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H268 as [H268 H269].
assert (* AndElim *) ((euclidean__axioms.Col C E x37) /\ ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))))) as H270.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H269.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H270 as [H270 H271].
assert (* AndElim *) ((euclidean__axioms.neq x36 x37) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)))) as H272.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H271.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H272 as [H272 H273].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35))) as H274.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H273.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H274 as [H274 H275].
assert (* AndElim *) ((euclidean__axioms.BetS x34 x38 x37) /\ (euclidean__axioms.BetS x36 x38 x35)) as H276.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H275.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H276 as [H276 H277].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H278.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H278.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H279.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact __TmpHyp8.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H279 as [x39 H279].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x39 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H280.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H279.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H280 as [x40 H280].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS u X x40)))))))))))) as H281.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H280.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H281 as [x41 H281].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col C D x41) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x41 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 X v) /\ (euclidean__axioms.BetS x41 X x40)))))))))))) as H282.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H281.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H282 as [x42 H282].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col C D x41) /\ ((euclidean__axioms.Col C D x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 X x42) /\ (euclidean__axioms.BetS x41 X x40)))))))))))) as H283.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H282.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H283 as [x43 H283].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col C D x41) /\ ((euclidean__axioms.Col C D x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))))))) as H284.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H283.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H284 as [H284 H285].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col C D x41) /\ ((euclidean__axioms.Col C D x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))))))) as H286.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H285.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H286 as [H286 H287].
assert (* AndElim *) ((euclidean__axioms.Col A B x39) /\ ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col C D x41) /\ ((euclidean__axioms.Col C D x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))))) as H288.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H287.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H288 as [H288 H289].
assert (* AndElim *) ((euclidean__axioms.Col A B x40) /\ ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col C D x41) /\ ((euclidean__axioms.Col C D x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))))) as H290.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H289.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H290 as [H290 H291].
assert (* AndElim *) ((euclidean__axioms.neq x39 x40) /\ ((euclidean__axioms.Col C D x41) /\ ((euclidean__axioms.Col C D x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))))) as H292.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H291.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H292 as [H292 H293].
assert (* AndElim *) ((euclidean__axioms.Col C D x41) /\ ((euclidean__axioms.Col C D x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))))) as H294.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H293.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H294 as [H294 H295].
assert (* AndElim *) ((euclidean__axioms.Col C D x42) /\ ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))))) as H296.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H295.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H296 as [H296 H297].
assert (* AndElim *) ((euclidean__axioms.neq x41 x42) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)))) as H298.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H297.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H298 as [H298 H299].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40))) as H300.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H299.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H300 as [H300 H301].
assert (* AndElim *) ((euclidean__axioms.BetS x39 x43 x42) /\ (euclidean__axioms.BetS x41 x43 x40)) as H302.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H301.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H302 as [H302 H303].
exact H92.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS E F B) as H71.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H71.
-------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (e) (E) (B) (A) (E) (B) (F) (H61) (H63) (H59) (H64) (H59) (H64) (H70) (H50) H58).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B F E) as H72.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H72.
--------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (F) (B) H71).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS e C E) as H73.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H73.
---------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (E) (C) (e) H21).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E C) as H74.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol A B C)))) as H74.
----------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (E) (C) H26).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol A B C)))) as H75.
------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol A B C))) as H77.
------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.nCol B E C) /\ (euclidean__axioms.nCol A B C)) as H79.
-------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------- destruct H79 as [H79 H80].
exact H79.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E C B) as H75.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol E C B) /\ ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol C E B))))) as H75.
------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder (B) (E) (C) H74).
------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol E C B) /\ ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol C E B))))) as H76.
------------------------------------------------------------------------- exact H75.
------------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.nCol E C B) /\ ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol C E B)))) as H78.
-------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.nCol C B E) /\ ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol C E B))) as H80.
--------------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.nCol B C E) /\ (euclidean__axioms.nCol C E B)) as H82.
---------------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H78.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C e) as H76.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H76.
------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------------------------- exact H38.
------------------------------------------------------------------------ assert (* Cut *) (E = E) as H77.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H77.
-------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------------------------------------------------- exact H60.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C E) as H78.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H78.
--------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------------------------------------------------------------- right.
left.
exact H77.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E e B) as H79.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H79.
---------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (E) (e) (B)).
-----------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (E) (e) (B)).
------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (E) (C) (B) (E) (e) (H75) (H78) (H76) H44).


--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E e) as H80.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol e E B) /\ ((euclidean__axioms.nCol e B E) /\ ((euclidean__axioms.nCol B E e) /\ ((euclidean__axioms.nCol E B e) /\ (euclidean__axioms.nCol B e E))))) as H80.
----------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (E) (e) (B) H79).
----------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol e E B) /\ ((euclidean__axioms.nCol e B E) /\ ((euclidean__axioms.nCol B E e) /\ ((euclidean__axioms.nCol E B e) /\ (euclidean__axioms.nCol B e E))))) as H81.
------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.nCol e B E) /\ ((euclidean__axioms.nCol B E e) /\ ((euclidean__axioms.nCol E B e) /\ (euclidean__axioms.nCol B e E)))) as H83.
------------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.nCol B E e) /\ ((euclidean__axioms.nCol E B e) /\ (euclidean__axioms.nCol B e E))) as H85.
-------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.nCol E B e) /\ (euclidean__axioms.nCol B e E)) as H87.
--------------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------------- destruct H87 as [H87 H88].
exact H85.
---------------------------------------------------------------------------- assert (* Cut *) (exists (K: euclidean__axioms.Point), (euclidean__axioms.BetS B K C) /\ (euclidean__axioms.BetS e K F)) as H81.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H81.
------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------------------------------ apply (@euclidean__axioms.postulate__Pasch__inner (B) (e) (E) (F) (C) (H72) (H73) H80).
----------------------------------------------------------------------------- assert (exists K: euclidean__axioms.Point, ((euclidean__axioms.BetS B K C) /\ (euclidean__axioms.BetS e K F))) as H82.
------------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------------ destruct H82 as [K H82].
assert (* AndElim *) ((euclidean__axioms.BetS B K C) /\ (euclidean__axioms.BetS e K F)) as H83.
------------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* Cut *) (euclidean__axioms.BetS e F A) as H85.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H85.
--------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
--------------------------------------------------------------------------------- exact H50.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS e K A) as H86.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H86.
---------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
---------------------------------------------------------------------------------- apply (@lemma__3__6b.lemma__3__6b (e) (K) (F) (A) (H84) H85).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A K e) as H87.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H87.
----------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
----------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (e) (K) (A) H86).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A e) as H88.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq K e) /\ ((euclidean__axioms.neq A K) /\ (euclidean__axioms.neq A e))) as H88.
------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (K) (e) H87).
------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq K e) /\ ((euclidean__axioms.neq A K) /\ (euclidean__axioms.neq A e))) as H89.
------------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.neq A K) /\ (euclidean__axioms.neq A e)) as H91.
-------------------------------------------------------------------------------------- exact H90.
-------------------------------------------------------------------------------------- destruct H91 as [H91 H92].
exact H92.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CR A e B C) as H89.
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H89.
------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------------------------------------- exists K.
split.
-------------------------------------------------------------------------------------- exact H87.
-------------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C D e) as H90.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H90.
-------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
-------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (D) (e)).
---------------------------------------------------------------------------------------intro H91.
apply (@euclidean__tactics.Col__nCol__False (C) (D) (e) (H91)).
----------------------------------------------------------------------------------------apply (@lemma__Playfairhelper.lemma__Playfairhelper (A) (B) (C) (D) (e) (H) (H28) (H1) H89).


------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e C D) as H91.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C e) /\ ((euclidean__axioms.Col D e C) /\ ((euclidean__axioms.Col e C D) /\ ((euclidean__axioms.Col C e D) /\ (euclidean__axioms.Col e D C))))) as H91.
--------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (e) H90).
--------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D C e) /\ ((euclidean__axioms.Col D e C) /\ ((euclidean__axioms.Col e C D) /\ ((euclidean__axioms.Col C e D) /\ (euclidean__axioms.Col e D C))))) as H92.
---------------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col D e C) /\ ((euclidean__axioms.Col e C D) /\ ((euclidean__axioms.Col C e D) /\ (euclidean__axioms.Col e D C)))) as H94.
----------------------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col e C D) /\ ((euclidean__axioms.Col C e D) /\ (euclidean__axioms.Col e D C))) as H96.
------------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------------ destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col C e D) /\ (euclidean__axioms.Col e D C)) as H98.
------------------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
exact H96.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e C E) as H92.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C E e) /\ ((euclidean__axioms.Col C e E) /\ ((euclidean__axioms.Col e E C) /\ ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E))))) as H92.
---------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (C) (e) H76).
---------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C E e) /\ ((euclidean__axioms.Col C e E) /\ ((euclidean__axioms.Col e E C) /\ ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E))))) as H93.
----------------------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col C e E) /\ ((euclidean__axioms.Col e E C) /\ ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E)))) as H95.
------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col e E C) /\ ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E))) as H97.
------------------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
assert (* AndElim *) ((euclidean__axioms.Col E e C) /\ (euclidean__axioms.Col e C E)) as H99.
-------------------------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
exact H100.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C e) as H93.
---------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq K e) /\ ((euclidean__axioms.neq A K) /\ (euclidean__axioms.neq A e))) as H93.
----------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (K) (e) H87).
----------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq K e) /\ ((euclidean__axioms.neq A K) /\ (euclidean__axioms.neq A e))) as H94.
------------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------------ destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.neq A K) /\ (euclidean__axioms.neq A e)) as H96.
------------------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
exact H24.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq e C) as H94.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H94.
------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------------------------------------------ exact H25.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D E) as H95.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) as H95.
------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A E B C) \/ (euclidean__defs.CR A C E B)) H4).
------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (D) (E)).
--------------------------------------------------------------------------------------------intro H96.
apply (@euclidean__tactics.Col__nCol__False (C) (D) (E) (H96)).
---------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (e) (C) (D) (E) (H91) (H92) H94).


------------------------------------------------------------------------------------------ exact H95.
------- exact H9.
Qed.
