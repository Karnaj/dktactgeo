Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__Playfairhelper2.
Require Export lemma__betweennotequal.
Require Export lemma__crisscross.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelflip.
Require Export logic.
Definition lemma__Playfair : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__defs.Par A B C D) -> ((euclidean__defs.Par A B C E) -> (euclidean__axioms.Col C D E)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.neq A B) as H1.
- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H1.
-- exact H0.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
--- exact H1.
--- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H2.
---- exact __TmpHyp.
---- destruct H2 as [x H2].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H3.
----- exact H2.
----- destruct H3 as [x0 H3].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H4.
------ exact H3.
------ destruct H4 as [x1 H4].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H5.
------- exact H4.
------- destruct H5 as [x2 H5].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H6.
-------- exact H5.
-------- destruct H6 as [x3 H6].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H7.
--------- exact H6.
--------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H9.
---------- exact H8.
---------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H25.
------------------ exact H24.
------------------ destruct H25 as [H25 H26].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H27.
------------------- exact H.
------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
-------------------- exact H27.
-------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H28.
--------------------- exact __TmpHyp0.
--------------------- destruct H28 as [x4 H28].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [x5 H29].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H30.
----------------------- exact H29.
----------------------- destruct H30 as [x6 H30].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [x7 H31].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [x8 H32].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H35.
--------------------------- exact H34.
--------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H37.
---------------------------- exact H36.
---------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H39.
----------------------------- exact H38.
----------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H41.
------------------------------ exact H40.
------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H43.
------------------------------- exact H42.
------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H45.
-------------------------------- exact H44.
-------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H47.
--------------------------------- exact H46.
--------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H49.
---------------------------------- exact H48.
---------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H51.
----------------------------------- exact H50.
----------------------------------- destruct H51 as [H51 H52].
exact H33.
- assert (* Cut *) (euclidean__axioms.neq C D) as H2.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H2.
--- exact H0.
--- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
---- exact H2.
---- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H3.
----- exact __TmpHyp.
----- destruct H3 as [x H3].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H4.
------ exact H3.
------ destruct H4 as [x0 H4].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H5.
------- exact H4.
------- destruct H5 as [x1 H5].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H6.
-------- exact H5.
-------- destruct H6 as [x2 H6].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H7.
--------- exact H6.
--------- destruct H7 as [x3 H7].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H8.
---------- exact H7.
---------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H10.
----------- exact H9.
----------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col C E x1) /\ ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col C E x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C E)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H26.
------------------- exact H25.
------------------- destruct H26 as [H26 H27].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H28.
-------------------- exact H.
-------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0.
--------------------- exact H28.
--------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H29.
---------------------- exact __TmpHyp0.
---------------------- destruct H29 as [x4 H29].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x4 V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H30.
----------------------- exact H29.
----------------------- destruct H30 as [x5 H30].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS u X x5)))))))))))) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [x6 H31].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x6 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X v) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [x7 H32].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 X x7) /\ (euclidean__axioms.BetS x6 X x5)))))))))))) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [x8 H33].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))))) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))))) as H36.
---------------------------- exact H35.
---------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col A B x4) /\ ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))))) as H38.
----------------------------- exact H37.
----------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A B x5) /\ ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))))) as H40.
------------------------------ exact H39.
------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq x4 x5) /\ ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))))) as H42.
------------------------------- exact H41.
------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col C D x6) /\ ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))))) as H44.
-------------------------------- exact H43.
-------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col C D x7) /\ ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))))) as H46.
--------------------------------- exact H45.
--------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq x6 x7) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)))) as H48.
---------------------------------- exact H47.
---------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5))) as H50.
----------------------------------- exact H49.
----------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.BetS x4 x8 x7) /\ (euclidean__axioms.BetS x6 x8 x5)) as H52.
------------------------------------ exact H51.
------------------------------------ destruct H52 as [H52 H53].
exact H36.
-- assert (* Cut *) (~(~((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)))) as H3.
--- intro H3.
assert (* Cut *) (euclidean__defs.Par A B D C) as H4.
---- assert (* Cut *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H4.
----- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (C) (D) H).
----- assert (* AndElim *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C)) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
exact H7.
---- assert (* Cut *) (euclidean__defs.CR A C D B) as H5.
----- apply (@lemma__crisscross.lemma__crisscross (A) (D) (B) (C) (H4)).
------intro H5.
apply (@H3).
-------left.
exact H5.


----- assert (* Cut *) (exists (p: euclidean__axioms.Point), (euclidean__axioms.BetS A p C) /\ (euclidean__axioms.BetS D p B)) as H6.
------ exact H5.
------ assert (exists p: euclidean__axioms.Point, ((euclidean__axioms.BetS A p C) /\ (euclidean__axioms.BetS D p B))) as H7.
------- exact H6.
------- destruct H7 as [p H7].
assert (* AndElim *) ((euclidean__axioms.BetS A p C) /\ (euclidean__axioms.BetS D p B)) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* Cut *) (euclidean__axioms.neq D B) as H10.
--------- assert (* Cut *) ((euclidean__axioms.neq p B) /\ ((euclidean__axioms.neq D p) /\ (euclidean__axioms.neq D B))) as H10.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (p) (B) H9).
---------- assert (* AndElim *) ((euclidean__axioms.neq p B) /\ ((euclidean__axioms.neq D p) /\ (euclidean__axioms.neq D B))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq D p) /\ (euclidean__axioms.neq D B)) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
exact H14.
--------- assert (* Cut *) (euclidean__axioms.neq B D) as H11.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (B) H10).
---------- assert (* Cut *) (euclidean__axioms.BetS B p D) as H12.
----------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (p) (B) H9).
----------- assert (* Cut *) (euclidean__defs.CR A C B D) as H13.
------------ exists p.
split.
------------- exact H8.
------------- exact H12.
------------ apply (@H3).
-------------right.
exact H13.

--- assert (* Cut *) (euclidean__axioms.Col C D E) as H4.
---- assert (* Cut *) ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as H4.
----- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D))).
------intro H4.
assert (* Cut *) (False) as H5.
------- apply (@H3 H4).
------- assert (* Cut *) ((euclidean__defs.CR A D B C) -> False) as H6.
-------- intro H6.
apply (@H4).
---------left.
exact H6.

-------- assert (* Cut *) ((euclidean__defs.CR A C B D) -> False) as H7.
--------- intro H7.
apply (@H4).
----------right.
exact H7.

--------- assert False.
----------exact H5.
---------- contradiction.

----- assert (* Cut *) ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as H5.
------ exact H4.
------ assert (* Cut *) ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as __TmpHyp.
------- exact H5.
------- assert (euclidean__defs.CR A D B C \/ euclidean__defs.CR A C B D) as H6.
-------- exact __TmpHyp.
-------- destruct H6 as [H6|H6].
--------- assert (* Cut *) (euclidean__axioms.Col C D E) as H7.
---------- assert (* Cut *) ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as H7.
----------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) H3).
----------- apply (@euclidean__tactics.not__nCol__Col (C) (D) (E)).
------------intro H8.
apply (@euclidean__tactics.Col__nCol__False (C) (D) (E) (H8)).
-------------apply (@lemma__Playfairhelper2.lemma__Playfairhelper2 (A) (B) (C) (D) (E) (H) (H0) H6).


---------- exact H7.
--------- assert (* Cut *) (exists (p: euclidean__axioms.Point), (euclidean__axioms.BetS A p C) /\ (euclidean__axioms.BetS B p D)) as H7.
---------- exact H6.
---------- assert (exists p: euclidean__axioms.Point, ((euclidean__axioms.BetS A p C) /\ (euclidean__axioms.BetS B p D))) as H8.
----------- exact H7.
----------- destruct H8 as [p H8].
assert (* AndElim *) ((euclidean__axioms.BetS A p C) /\ (euclidean__axioms.BetS B p D)) as H9.
------------ exact H8.
------------ destruct H9 as [H9 H10].
assert (* Cut *) (euclidean__defs.CR B D A C) as H11.
------------- assert (* Cut *) ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as H11.
-------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) H3).
-------------- exists p.
split.
--------------- exact H10.
--------------- exact H9.
------------- assert (* Cut *) (euclidean__defs.Par B A C D) as H12.
-------------- assert (* Cut *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H12.
--------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (C) (D) H).
--------------- assert (* AndElim *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H13.
---------------- exact H12.
---------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C)) as H15.
----------------- exact H14.
----------------- destruct H15 as [H15 H16].
exact H13.
-------------- assert (* Cut *) (euclidean__defs.Par B A C E) as H13.
--------------- assert (* Cut *) ((euclidean__defs.Par B A C E) /\ ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C))) as H13.
---------------- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (C) (E) H0).
---------------- assert (* AndElim *) ((euclidean__defs.Par B A C E) /\ ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C))) as H14.
----------------- exact H13.
----------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__defs.Par A B E C) /\ (euclidean__defs.Par B A E C)) as H16.
------------------ exact H15.
------------------ destruct H16 as [H16 H17].
exact H14.
--------------- assert (* Cut *) (euclidean__axioms.Col C D E) as H14.
---------------- assert (* Cut *) ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) as H14.
----------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A D B C) \/ (euclidean__defs.CR A C B D)) H3).
----------------- apply (@euclidean__tactics.not__nCol__Col (C) (D) (E)).
------------------intro H15.
apply (@euclidean__tactics.Col__nCol__False (C) (D) (E) (H15)).
-------------------apply (@lemma__Playfairhelper2.lemma__Playfairhelper2 (B) (A) (C) (D) (E) (H12) (H13) H11).


---------------- exact H14.
---- exact H4.
Qed.
