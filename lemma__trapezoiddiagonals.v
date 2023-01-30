Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__diagonalsbisect.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__trapezoiddiagonals : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__defs.PG A B C D) -> ((euclidean__axioms.BetS A E D) -> (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B X D) /\ (euclidean__axioms.BetS C X E))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
assert (* Cut *) (euclidean__defs.Par A B C D) as H1.
- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H1.
-- exact H.
-- destruct H1 as [H1 H2].
exact H1.
- assert (* Cut *) (euclidean__defs.Par A D B C) as H2.
-- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H2.
--- exact H.
--- destruct H2 as [H2 H3].
exact H3.
-- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H3.
--- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H3.
---- exact H2.
---- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
----- exact H3.
----- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H4.
------ exact __TmpHyp.
------ destruct H4 as [x H4].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H5.
------- exact H4.
------- destruct H5 as [x0 H5].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H6.
-------- exact H5.
-------- destruct H6 as [x1 H6].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H7.
--------- exact H6.
--------- destruct H7 as [x2 H7].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H8.
---------- exact H7.
---------- destruct H8 as [x3 H8].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H9.
----------- exact H8.
----------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H11.
------------ exact H10.
------------ destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H13.
------------- exact H12.
------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H23.
------------------ exact H22.
------------------ destruct H23 as [H23 H24].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H25.
------------------- exact H24.
------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H27.
-------------------- exact H26.
-------------------- destruct H27 as [H27 H28].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H29.
--------------------- exact H1.
--------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
---------------------- exact H29.
---------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H30.
----------------------- exact __TmpHyp0.
----------------------- destruct H30 as [x4 H30].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [x5 H31].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [x6 H32].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [x7 H33].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [x8 H34].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H35.
---------------------------- exact H34.
---------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H37.
----------------------------- exact H36.
----------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H39.
------------------------------ exact H38.
------------------------------ destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H41.
------------------------------- exact H40.
------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H43.
-------------------------------- exact H42.
-------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H45.
--------------------------------- exact H44.
--------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H47.
---------------------------------- exact H46.
---------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H49.
----------------------------------- exact H48.
----------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H51.
------------------------------------ exact H50.
------------------------------------ destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H53.
------------------------------------- exact H52.
------------------------------------- destruct H53 as [H53 H54].
exact H51.
--- assert (* Cut *) (euclidean__axioms.neq A B) as H4.
---- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H4.
----- exact H2.
----- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
------ exact H4.
------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H5.
------- exact __TmpHyp.
------- destruct H5 as [x H5].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H6.
-------- exact H5.
-------- destruct H6 as [x0 H6].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H7.
--------- exact H6.
--------- destruct H7 as [x1 H7].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H8.
---------- exact H7.
---------- destruct H8 as [x2 H8].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H9.
----------- exact H8.
----------- destruct H9 as [x3 H9].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H10.
------------ exact H9.
------------ destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H12.
------------- exact H11.
------------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H14.
-------------- exact H13.
-------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H30.
---------------------- exact H1.
---------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
----------------------- exact H30.
----------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H31.
------------------------ exact __TmpHyp0.
------------------------ destruct H31 as [x4 H31].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [x5 H32].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [x6 H33].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [x7 H34].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H35.
---------------------------- exact H34.
---------------------------- destruct H35 as [x8 H35].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H38.
------------------------------ exact H37.
------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H40.
------------------------------- exact H39.
------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H42.
-------------------------------- exact H41.
-------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H44.
--------------------------------- exact H43.
--------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H46.
---------------------------------- exact H45.
---------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H48.
----------------------------------- exact H47.
----------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H50.
------------------------------------ exact H49.
------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H52.
------------------------------------- exact H51.
------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H54.
-------------------------------------- exact H53.
-------------------------------------- destruct H54 as [H54 H55].
exact H36.
---- assert (* Cut *) (euclidean__axioms.neq C D) as H5.
----- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H5.
------ exact H2.
------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
------- exact H5.
------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H6.
-------- exact __TmpHyp.
-------- destruct H6 as [x H6].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H7.
--------- exact H6.
--------- destruct H7 as [x0 H7].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H8.
---------- exact H7.
---------- destruct H8 as [x1 H8].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H9.
----------- exact H8.
----------- destruct H9 as [x2 H9].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H10.
------------ exact H9.
------------ destruct H10 as [x3 H10].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H11.
------------- exact H10.
------------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H13.
-------------- exact H12.
-------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col A D x) /\ ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col A D x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col B C x1) /\ ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H21.
------------------ exact H20.
------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col B C x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H31.
----------------------- exact H1.
----------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
------------------------ exact H31.
------------------------ assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H32.
------------------------- exact __TmpHyp0.
------------------------- destruct H32 as [x4 H32].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [x5 H33].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [x6 H34].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H35.
---------------------------- exact H34.
---------------------------- destruct H35 as [x7 H35].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [x8 H36].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H37.
------------------------------ exact H36.
------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H39.
------------------------------- exact H38.
------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H41.
-------------------------------- exact H40.
-------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H43.
--------------------------------- exact H42.
--------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H45.
---------------------------------- exact H44.
---------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H47.
----------------------------------- exact H46.
----------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H49.
------------------------------------ exact H48.
------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H51.
------------------------------------- exact H50.
------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H53.
-------------------------------------- exact H52.
-------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H55.
--------------------------------------- exact H54.
--------------------------------------- destruct H55 as [H55 H56].
exact H39.
----- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__defs.Midpoint A M C) /\ (euclidean__defs.Midpoint B M D)) as H6.
------ apply (@lemma__diagonalsbisect.lemma__diagonalsbisect (A) (B) (C) (D) H).
------ assert (exists M: euclidean__axioms.Point, ((euclidean__defs.Midpoint A M C) /\ (euclidean__defs.Midpoint B M D))) as H7.
------- exact H6.
------- destruct H7 as [M H7].
assert (* AndElim *) ((euclidean__defs.Midpoint A M C) /\ (euclidean__defs.Midpoint B M D)) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* Cut *) (euclidean__axioms.BetS A M C) as H10.
--------- assert (* AndElim *) ((euclidean__axioms.BetS B M D) /\ (euclidean__axioms.Cong B M M D)) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.Cong A M M C)) as H12.
----------- exact H8.
----------- destruct H12 as [H12 H13].
exact H12.
--------- assert (* Cut *) (euclidean__axioms.Cong A M M C) as H11.
---------- assert (* AndElim *) ((euclidean__axioms.BetS B M D) /\ (euclidean__axioms.Cong B M M D)) as H11.
----------- exact H9.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.Cong A M M C)) as H13.
------------ exact H8.
------------ destruct H13 as [H13 H14].
exact H14.
---------- assert (* Cut *) (euclidean__axioms.BetS B M D) as H12.
----------- assert (* AndElim *) ((euclidean__axioms.BetS B M D) /\ (euclidean__axioms.Cong B M M D)) as H12.
------------ exact H9.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.Cong A M M C)) as H14.
------------- exact H8.
------------- destruct H14 as [H14 H15].
exact H12.
----------- assert (* Cut *) (euclidean__axioms.Cong B M M D) as H13.
------------ assert (* AndElim *) ((euclidean__axioms.BetS B M D) /\ (euclidean__axioms.Cong B M M D)) as H13.
------------- exact H9.
------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.Cong A M M C)) as H15.
-------------- exact H8.
-------------- destruct H15 as [H15 H16].
exact H14.
------------ assert (* Cut *) (euclidean__axioms.Cong B M D M) as H14.
------------- assert (* Cut *) ((euclidean__axioms.Cong M B D M) /\ ((euclidean__axioms.Cong M B M D) /\ (euclidean__axioms.Cong B M D M))) as H14.
-------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (M) (M) (D) H13).
-------------- assert (* AndElim *) ((euclidean__axioms.Cong M B D M) /\ ((euclidean__axioms.Cong M B M D) /\ (euclidean__axioms.Cong B M D M))) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Cong M B M D) /\ (euclidean__axioms.Cong B M D M)) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
exact H18.
------------- assert (* Cut *) (B = B) as H15.
-------------- apply (@logic.eq__refl (Point) B).
-------------- assert (* Cut *) (~(euclidean__axioms.Col B D C)) as H16.
--------------- intro H16.
assert (* Cut *) (euclidean__axioms.Col C D B) as H17.
---------------- assert (* Cut *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B))))) as H17.
----------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (D) (C) H16).
----------------- assert (* AndElim *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B))))) as H18.
------------------ exact H17.
------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B)))) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B))) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B)) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [H24 H25].
exact H25.
---------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H18.
----------------- right.
right.
left.
exact H15.
----------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H19.
------------------ exists B.
split.
------------------- exact H4.
------------------- split.
-------------------- exact H5.
-------------------- split.
--------------------- exact H18.
--------------------- exact H17.
------------------ apply (@H3 H19).
--------------- assert (* Cut *) (euclidean__axioms.Cong M A M C) as H17.
---------------- assert (* Cut *) ((euclidean__axioms.Cong M A C M) /\ ((euclidean__axioms.Cong M A M C) /\ (euclidean__axioms.Cong A M C M))) as H17.
----------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (M) (M) (C) H11).
----------------- assert (* AndElim *) ((euclidean__axioms.Cong M A C M) /\ ((euclidean__axioms.Cong M A M C) /\ (euclidean__axioms.Cong A M C M))) as H18.
------------------ exact H17.
------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Cong M A M C) /\ (euclidean__axioms.Cong A M C M)) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
exact H20.
---------------- assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.BetS B E P) /\ (euclidean__axioms.BetS C D P)) as H18.
----------------- apply (@euclidean__axioms.postulate__Euclid5 (E) (B) (D) (A) (C) (M) (H10) (H12) (H0) (H14) (H17)).
------------------apply (@euclidean__tactics.nCol__notCol (B) (D) (C) H16).

----------------- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.BetS B E P) /\ (euclidean__axioms.BetS C D P))) as H19.
------------------ exact H18.
------------------ destruct H19 as [P H19].
assert (* AndElim *) ((euclidean__axioms.BetS B E P) /\ (euclidean__axioms.BetS C D P)) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* Cut *) (~(euclidean__axioms.Col B P C)) as H22.
-------------------- intro H22.
assert (* Cut *) (euclidean__axioms.Col P C B) as H23.
--------------------- assert (* Cut *) ((euclidean__axioms.Col P B C) /\ ((euclidean__axioms.Col P C B) /\ ((euclidean__axioms.Col C B P) /\ ((euclidean__axioms.Col B C P) /\ (euclidean__axioms.Col C P B))))) as H23.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (P) (C) H22).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col P B C) /\ ((euclidean__axioms.Col P C B) /\ ((euclidean__axioms.Col C B P) /\ ((euclidean__axioms.Col B C P) /\ (euclidean__axioms.Col C P B))))) as H24.
----------------------- exact H23.
----------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Col P C B) /\ ((euclidean__axioms.Col C B P) /\ ((euclidean__axioms.Col B C P) /\ (euclidean__axioms.Col C P B)))) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col C B P) /\ ((euclidean__axioms.Col B C P) /\ (euclidean__axioms.Col C P B))) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col B C P) /\ (euclidean__axioms.Col C P B)) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
exact H26.
--------------------- assert (* Cut *) (euclidean__axioms.Col C D P) as H24.
---------------------- right.
right.
right.
right.
left.
exact H21.
---------------------- assert (* Cut *) (euclidean__axioms.Col P C D) as H25.
----------------------- assert (* Cut *) ((euclidean__axioms.Col D C P) /\ ((euclidean__axioms.Col D P C) /\ ((euclidean__axioms.Col P C D) /\ ((euclidean__axioms.Col C P D) /\ (euclidean__axioms.Col P D C))))) as H25.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (P) H24).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col D C P) /\ ((euclidean__axioms.Col D P C) /\ ((euclidean__axioms.Col P C D) /\ ((euclidean__axioms.Col C P D) /\ (euclidean__axioms.Col P D C))))) as H26.
------------------------- exact H25.
------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Col D P C) /\ ((euclidean__axioms.Col P C D) /\ ((euclidean__axioms.Col C P D) /\ (euclidean__axioms.Col P D C)))) as H28.
-------------------------- exact H27.
-------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col P C D) /\ ((euclidean__axioms.Col C P D) /\ (euclidean__axioms.Col P D C))) as H30.
--------------------------- exact H29.
--------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col C P D) /\ (euclidean__axioms.Col P D C)) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [H32 H33].
exact H30.
----------------------- assert (* Cut *) (euclidean__axioms.neq C P) as H26.
------------------------ assert (* Cut *) ((euclidean__axioms.neq D P) /\ ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C P))) as H26.
------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (D) (P) H21).
------------------------- assert (* AndElim *) ((euclidean__axioms.neq D P) /\ ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C P))) as H27.
-------------------------- exact H26.
-------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C P)) as H29.
--------------------------- exact H28.
--------------------------- destruct H29 as [H29 H30].
exact H30.
------------------------ assert (* Cut *) (euclidean__axioms.neq P C) as H27.
------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (P) H26).
------------------------- assert (* Cut *) (euclidean__axioms.Col C B D) as H28.
-------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (B) (D)).
---------------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False (C) (B) (D) (H28)).
----------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (C) (B) (D) (H23) (H25) H27).


-------------------------- assert (* Cut *) (euclidean__axioms.Col C D B) as H29.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H29.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (D) H28).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H30.
----------------------------- exact H29.
----------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)))) as H32.
------------------------------ exact H31.
------------------------------ destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))) as H34.
------------------------------- exact H33.
------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C)) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
exact H36.
--------------------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H30.
---------------------------- right.
right.
left.
exact H15.
---------------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H31.
----------------------------- exists B.
split.
------------------------------ exact H4.
------------------------------ split.
------------------------------- exact H5.
------------------------------- split.
-------------------------------- exact H30.
-------------------------------- exact H29.
----------------------------- apply (@H3 H31).
-------------------- assert (* Cut *) (exists (H': euclidean__axioms.Point), (euclidean__axioms.BetS B H' D) /\ (euclidean__axioms.BetS C H' E)) as H23.
--------------------- apply (@euclidean__axioms.postulate__Pasch__inner (B) (C) (P) (E) (D) (H20) (H21)).
----------------------apply (@euclidean__tactics.nCol__notCol (B) (P) (C) H22).

--------------------- assert (exists H': euclidean__axioms.Point, ((euclidean__axioms.BetS B H' D) /\ (euclidean__axioms.BetS C H' E))) as H24.
---------------------- exact H23.
---------------------- destruct H24 as [H' H24].
assert (* AndElim *) ((euclidean__axioms.BetS B H' D) /\ (euclidean__axioms.BetS C H' E)) as H25.
----------------------- exact H24.
----------------------- destruct H25 as [H25 H26].
exists H'.
split.
------------------------ exact H25.
------------------------ exact H26.
Qed.
