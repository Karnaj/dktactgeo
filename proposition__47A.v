Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__8__3.
Require Export lemma__8__7.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__Playfair.
Require Export lemma__altitudeofrighttriangle.
Require Export lemma__betweennesspreserved.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__collinearright.
Require Export lemma__equaltorightisright.
Require Export lemma__erectedperpendicularunique.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__rightangleNC.
Require Export lemma__sameside2.
Require Export lemma__samesideflip.
Require Export lemma__samesidesymmetric.
Require Export lemma__squareparallelogram.
Require Export lemma__twoperpsparallel.
Require Export logic.
Require Export proposition__12.
Require Export proposition__29C.
Require Export proposition__34.
Definition proposition__47A : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.Per B A C) -> ((euclidean__defs.SQ B C E D) -> ((euclidean__axioms.TS D C B A) -> (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point), (euclidean__defs.PG B X Y D) /\ ((euclidean__axioms.BetS B X C) /\ ((euclidean__defs.PG X C E Y) /\ ((euclidean__axioms.BetS D Y E) /\ ((euclidean__axioms.BetS Y X A) /\ (euclidean__defs.Per D Y A))))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (exists (N: euclidean__axioms.Point), (euclidean__axioms.BetS D N A) /\ ((euclidean__axioms.Col C B N) /\ (euclidean__axioms.nCol C B D))) as H3.
- exact H2.
- assert (exists N: euclidean__axioms.Point, ((euclidean__axioms.BetS D N A) /\ ((euclidean__axioms.Col C B N) /\ (euclidean__axioms.nCol C B D)))) as H4.
-- exact H3.
-- destruct H4 as [N H4].
assert (* AndElim *) ((euclidean__axioms.BetS D N A) /\ ((euclidean__axioms.Col C B N) /\ (euclidean__axioms.nCol C B D))) as H5.
--- exact H4.
--- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Col C B N) /\ (euclidean__axioms.nCol C B D)) as H7.
---- exact H6.
---- destruct H7 as [H7 H8].
assert (* Cut *) (euclidean__defs.Per C A B) as H9.
----- apply (@lemma__8__2.lemma__8__2 (B) (A) (C) H0).
----- assert (* Cut *) (euclidean__axioms.nCol C A B) as H10.
------ apply (@lemma__rightangleNC.lemma__rightangleNC (C) (A) (B) H9).
------ assert (* Cut *) (euclidean__axioms.neq A B) as H11.
------- assert (* Cut *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B C)))))) as H11.
-------- apply (@lemma__NCdistinct.lemma__NCdistinct (C) (A) (B) H10).
-------- assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B C)))))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B C))))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B C)))) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B C))) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B C)) as H20.
------------- exact H19.
------------- destruct H20 as [H20 H21].
exact H14.
------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H12.
-------- exact H.
-------- assert (* Cut *) (euclidean__axioms.neq B C) as H13.
--------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H13.
---------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H12).
---------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
exact H16.
--------- assert (* Cut *) (euclidean__axioms.Cong B C E D) as H14.
---------- assert (* AndElim *) ((euclidean__axioms.Cong B C E D) /\ ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))))) as H14.
----------- exact H1.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))))) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)) as H24.
---------------- exact H23.
---------------- destruct H24 as [H24 H25].
exact H14.
---------- assert (* Cut *) (euclidean__axioms.neq E D) as H15.
----------- apply (@euclidean__axioms.axiom__nocollapse (B) (C) (E) (D) (H13) H14).
----------- assert (* Cut *) (euclidean__axioms.neq D E) as H16.
------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (D) H15).
------------ assert (* Cut *) (exists (q: euclidean__axioms.Point), (euclidean__axioms.BetS D q A) /\ ((euclidean__axioms.Col C B q) /\ (euclidean__axioms.nCol C B D))) as H17.
------------- exact H2.
------------- assert (exists q: euclidean__axioms.Point, ((euclidean__axioms.BetS D q A) /\ ((euclidean__axioms.Col C B q) /\ (euclidean__axioms.nCol C B D)))) as H18.
-------------- exact H17.
-------------- destruct H18 as [q H18].
assert (* AndElim *) ((euclidean__axioms.BetS D q A) /\ ((euclidean__axioms.Col C B q) /\ (euclidean__axioms.nCol C B D))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col C B q) /\ (euclidean__axioms.nCol C B D)) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* Cut *) (euclidean__defs.PG B C E D) as H23.
----------------- apply (@lemma__squareparallelogram.lemma__squareparallelogram (B) (C) (E) (D) H1).
----------------- assert (* Cut *) (euclidean__defs.Par B C E D) as H24.
------------------ assert (* AndElim *) ((euclidean__defs.Par B C E D) /\ (euclidean__defs.Par B D C E)) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
exact H24.
------------------ assert (* Cut *) (~(euclidean__defs.Meet B C E D)) as H25.
------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E D u) /\ ((euclidean__axioms.Col E D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H25.
-------------------- exact H24.
-------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E D u) /\ ((euclidean__axioms.Col E D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
--------------------- exact H25.
--------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.Col B C U) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E D u) /\ ((euclidean__axioms.Col E D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H26.
---------------------- exact __TmpHyp.
---------------------- destruct H26 as [x H26].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.Col B C x) /\ ((euclidean__axioms.Col B C V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col E D u) /\ ((euclidean__axioms.Col E D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H27.
----------------------- exact H26.
----------------------- destruct H27 as [x0 H27].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.Col B C x) /\ ((euclidean__axioms.Col B C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E D u) /\ ((euclidean__axioms.Col E D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [x1 H28].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.Col B C x) /\ ((euclidean__axioms.Col B C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E D x1) /\ ((euclidean__axioms.Col E D v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [x2 H29].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.Col B C x) /\ ((euclidean__axioms.Col B C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E D x1) /\ ((euclidean__axioms.Col E D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [x3 H30].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.Col B C x) /\ ((euclidean__axioms.Col B C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E D x1) /\ ((euclidean__axioms.Col E D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H31.
--------------------------- exact H30.
--------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.Col B C x) /\ ((euclidean__axioms.Col B C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E D x1) /\ ((euclidean__axioms.Col E D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col B C x) /\ ((euclidean__axioms.Col B C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E D x1) /\ ((euclidean__axioms.Col E D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col B C x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E D x1) /\ ((euclidean__axioms.Col E D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H37.
------------------------------ exact H36.
------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col E D x1) /\ ((euclidean__axioms.Col E D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H39.
------------------------------- exact H38.
------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col E D x1) /\ ((euclidean__axioms.Col E D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H41.
-------------------------------- exact H40.
-------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col E D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H43.
--------------------------------- exact H42.
--------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H45.
---------------------------------- exact H44.
---------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((~(euclidean__defs.Meet B C E D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H47.
----------------------------------- exact H46.
----------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H49.
------------------------------------ exact H48.
------------------------------------ destruct H49 as [H49 H50].
exact H47.
------------------- assert (* Cut *) (~(A = E)) as H26.
-------------------- intro H26.
assert (* Cut *) (euclidean__axioms.BetS D q E) as H27.
--------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun A0: euclidean__axioms.Point => (euclidean__axioms.Triangle A0 B C) -> ((euclidean__defs.Per B A0 C) -> ((euclidean__axioms.TS D C B A0) -> ((euclidean__axioms.BetS D N A0) -> ((euclidean__defs.Per C A0 B) -> ((euclidean__axioms.nCol C A0 B) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__axioms.BetS D q A0) -> (euclidean__axioms.BetS D q E))))))))))) with (x := A).
----------------------intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
exact H35.

---------------------- exact H26.
---------------------- exact H.
---------------------- exact H0.
---------------------- exact H2.
---------------------- exact H5.
---------------------- exact H9.
---------------------- exact H10.
---------------------- exact H11.
---------------------- exact H12.
---------------------- exact H19.
--------------------- assert (* Cut *) (euclidean__axioms.Col D q E) as H28.
---------------------- right.
right.
right.
right.
left.
exact H27.
---------------------- assert (* Cut *) (euclidean__axioms.Col E D q) as H29.
----------------------- assert (* Cut *) ((euclidean__axioms.Col q D E) /\ ((euclidean__axioms.Col q E D) /\ ((euclidean__axioms.Col E D q) /\ ((euclidean__axioms.Col D E q) /\ (euclidean__axioms.Col E q D))))) as H29.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder (D) (q) (E) H28).
------------------------ assert (* AndElim *) ((euclidean__axioms.Col q D E) /\ ((euclidean__axioms.Col q E D) /\ ((euclidean__axioms.Col E D q) /\ ((euclidean__axioms.Col D E q) /\ (euclidean__axioms.Col E q D))))) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col q E D) /\ ((euclidean__axioms.Col E D q) /\ ((euclidean__axioms.Col D E q) /\ (euclidean__axioms.Col E q D)))) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col E D q) /\ ((euclidean__axioms.Col D E q) /\ (euclidean__axioms.Col E q D))) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col D E q) /\ (euclidean__axioms.Col E q D)) as H36.
---------------------------- exact H35.
---------------------------- destruct H36 as [H36 H37].
exact H34.
----------------------- assert (* Cut *) (euclidean__axioms.Col B C q) as H30.
------------------------ assert (* Cut *) ((euclidean__axioms.Col B C q) /\ ((euclidean__axioms.Col B q C) /\ ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C))))) as H30.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (q) H21).
------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C q) /\ ((euclidean__axioms.Col B q C) /\ ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C))))) as H31.
-------------------------- exact H30.
-------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col B q C) /\ ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C)))) as H33.
--------------------------- exact H32.
--------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C))) as H35.
---------------------------- exact H34.
---------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C)) as H37.
----------------------------- exact H36.
----------------------------- destruct H37 as [H37 H38].
exact H31.
------------------------ assert (* Cut *) (euclidean__defs.Meet B C E D) as H31.
------------------------- exists q.
split.
-------------------------- exact H13.
-------------------------- split.
--------------------------- exact H15.
--------------------------- split.
---------------------------- exact H30.
---------------------------- exact H29.
------------------------- apply (@H25 H31).
-------------------- assert (* Cut *) (~(euclidean__axioms.Col D E A)) as H27.
--------------------- intro H27.
assert (* Cut *) (euclidean__axioms.Col D A E) as H28.
---------------------- assert (* Cut *) ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D A E) /\ (euclidean__axioms.Col A E D))))) as H28.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (E) (A) H27).
----------------------- assert (* AndElim *) ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D A E) /\ (euclidean__axioms.Col A E D))))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D A E) /\ (euclidean__axioms.Col A E D)))) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col D A E) /\ (euclidean__axioms.Col A E D))) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ (euclidean__axioms.Col A E D)) as H35.
--------------------------- exact H34.
--------------------------- destruct H35 as [H35 H36].
exact H35.
---------------------- assert (* Cut *) (euclidean__axioms.Col D q A) as H29.
----------------------- right.
right.
right.
right.
left.
exact H19.
----------------------- assert (* Cut *) (euclidean__axioms.Col D A q) as H30.
------------------------ assert (* Cut *) ((euclidean__axioms.Col q D A) /\ ((euclidean__axioms.Col q A D) /\ ((euclidean__axioms.Col A D q) /\ ((euclidean__axioms.Col D A q) /\ (euclidean__axioms.Col A q D))))) as H30.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (q) (A) H29).
------------------------- assert (* AndElim *) ((euclidean__axioms.Col q D A) /\ ((euclidean__axioms.Col q A D) /\ ((euclidean__axioms.Col A D q) /\ ((euclidean__axioms.Col D A q) /\ (euclidean__axioms.Col A q D))))) as H31.
-------------------------- exact H30.
-------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col q A D) /\ ((euclidean__axioms.Col A D q) /\ ((euclidean__axioms.Col D A q) /\ (euclidean__axioms.Col A q D)))) as H33.
--------------------------- exact H32.
--------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col A D q) /\ ((euclidean__axioms.Col D A q) /\ (euclidean__axioms.Col A q D))) as H35.
---------------------------- exact H34.
---------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col D A q) /\ (euclidean__axioms.Col A q D)) as H37.
----------------------------- exact H36.
----------------------------- destruct H37 as [H37 H38].
exact H37.
------------------------ assert (* Cut *) (euclidean__axioms.neq D A) as H31.
------------------------- assert (* Cut *) ((euclidean__axioms.neq q A) /\ ((euclidean__axioms.neq D q) /\ (euclidean__axioms.neq D A))) as H31.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (q) (A) H19).
-------------------------- assert (* AndElim *) ((euclidean__axioms.neq q A) /\ ((euclidean__axioms.neq D q) /\ (euclidean__axioms.neq D A))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq D q) /\ (euclidean__axioms.neq D A)) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
exact H35.
------------------------- assert (* Cut *) (euclidean__axioms.Col A E q) as H32.
-------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (E) (q)).
---------------------------intro H32.
apply (@euclidean__tactics.Col__nCol__False (A) (E) (q) (H32)).
----------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (A) (E) (q) (H28) (H30) H31).


-------------------------- assert (* Cut *) (euclidean__axioms.Col q A E) as H33.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col E A q) /\ ((euclidean__axioms.Col E q A) /\ ((euclidean__axioms.Col q A E) /\ ((euclidean__axioms.Col A q E) /\ (euclidean__axioms.Col q E A))))) as H33.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (q) H32).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A q) /\ ((euclidean__axioms.Col E q A) /\ ((euclidean__axioms.Col q A E) /\ ((euclidean__axioms.Col A q E) /\ (euclidean__axioms.Col q E A))))) as H34.
----------------------------- exact H33.
----------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col E q A) /\ ((euclidean__axioms.Col q A E) /\ ((euclidean__axioms.Col A q E) /\ (euclidean__axioms.Col q E A)))) as H36.
------------------------------ exact H35.
------------------------------ destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col q A E) /\ ((euclidean__axioms.Col A q E) /\ (euclidean__axioms.Col q E A))) as H38.
------------------------------- exact H37.
------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A q E) /\ (euclidean__axioms.Col q E A)) as H40.
-------------------------------- exact H39.
-------------------------------- destruct H40 as [H40 H41].
exact H38.
--------------------------- assert (* Cut *) (euclidean__axioms.Col q A D) as H34.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col A D q) /\ ((euclidean__axioms.Col A q D) /\ ((euclidean__axioms.Col q D A) /\ ((euclidean__axioms.Col D q A) /\ (euclidean__axioms.Col q A D))))) as H34.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (A) (q) H30).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col A D q) /\ ((euclidean__axioms.Col A q D) /\ ((euclidean__axioms.Col q D A) /\ ((euclidean__axioms.Col D q A) /\ (euclidean__axioms.Col q A D))))) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col A q D) /\ ((euclidean__axioms.Col q D A) /\ ((euclidean__axioms.Col D q A) /\ (euclidean__axioms.Col q A D)))) as H37.
------------------------------- exact H36.
------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col q D A) /\ ((euclidean__axioms.Col D q A) /\ (euclidean__axioms.Col q A D))) as H39.
-------------------------------- exact H38.
-------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col D q A) /\ (euclidean__axioms.Col q A D)) as H41.
--------------------------------- exact H40.
--------------------------------- destruct H41 as [H41 H42].
exact H42.
---------------------------- assert (* Cut *) (euclidean__axioms.neq q A) as H35.
----------------------------- assert (* Cut *) ((euclidean__axioms.neq q A) /\ ((euclidean__axioms.neq D q) /\ (euclidean__axioms.neq D A))) as H35.
------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (D) (q) (A) H19).
------------------------------ assert (* AndElim *) ((euclidean__axioms.neq q A) /\ ((euclidean__axioms.neq D q) /\ (euclidean__axioms.neq D A))) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq D q) /\ (euclidean__axioms.neq D A)) as H38.
-------------------------------- exact H37.
-------------------------------- destruct H38 as [H38 H39].
exact H36.
----------------------------- assert (* Cut *) (euclidean__axioms.Col A E D) as H36.
------------------------------ apply (@euclidean__tactics.not__nCol__Col (A) (E) (D)).
-------------------------------intro H36.
apply (@euclidean__tactics.Col__nCol__False (A) (E) (D) (H36)).
--------------------------------apply (@lemma__collinear4.lemma__collinear4 (q) (A) (E) (D) (H33) (H34) H35).


------------------------------ assert (* Cut *) (euclidean__axioms.Col A E q) as H37.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))))) as H37.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (E) (D) H36).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A)))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A)) as H44.
------------------------------------ exact H43.
------------------------------------ destruct H44 as [H44 H45].
exact H32.
------------------------------- assert (* Cut *) (euclidean__axioms.Col E D q) as H38.
-------------------------------- apply (@euclidean__tactics.not__nCol__Col (E) (D) (q)).
---------------------------------intro H38.
apply (@euclidean__tactics.Col__nCol__False (E) (D) (q) (H38)).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (E) (D) (q) (H36) (H37) H26).


-------------------------------- assert (* Cut *) (euclidean__axioms.Col B C q) as H39.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C q) /\ ((euclidean__axioms.Col B q C) /\ ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C))))) as H39.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (q) H21).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C q) /\ ((euclidean__axioms.Col B q C) /\ ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C))))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col B q C) /\ ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C)))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col q C B) /\ ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col C q B) /\ (euclidean__axioms.Col q B C)) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
exact H40.
--------------------------------- assert (* Cut *) (euclidean__defs.Meet B C E D) as H40.
---------------------------------- exists q.
split.
----------------------------------- exact H13.
----------------------------------- split.
------------------------------------ exact H15.
------------------------------------ split.
------------------------------------- exact H39.
------------------------------------- exact H38.
---------------------------------- apply (@H25 H40).
--------------------- assert (* Cut *) (exists (L: euclidean__axioms.Point), euclidean__defs.Perp__at A L D E L) as H28.
---------------------- apply (@proposition__12.proposition__12 (D) (E) (A)).
-----------------------apply (@euclidean__tactics.nCol__notCol (D) (E) (A) H27).

---------------------- assert (exists L: euclidean__axioms.Point, (euclidean__defs.Perp__at A L D E L)) as H29.
----------------------- exact H28.
----------------------- destruct H29 as [L H29].
assert (* Cut *) (exists (p: euclidean__axioms.Point), (euclidean__axioms.Col A L L) /\ ((euclidean__axioms.Col D E L) /\ ((euclidean__axioms.Col D E p) /\ (euclidean__defs.Per p L A)))) as H30.
------------------------ exact H29.
------------------------ assert (exists p: euclidean__axioms.Point, ((euclidean__axioms.Col A L L) /\ ((euclidean__axioms.Col D E L) /\ ((euclidean__axioms.Col D E p) /\ (euclidean__defs.Per p L A))))) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [p H31].
assert (* AndElim *) ((euclidean__axioms.Col A L L) /\ ((euclidean__axioms.Col D E L) /\ ((euclidean__axioms.Col D E p) /\ (euclidean__defs.Per p L A)))) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col D E L) /\ ((euclidean__axioms.Col D E p) /\ (euclidean__defs.Per p L A))) as H34.
--------------------------- exact H33.
--------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col D E p) /\ (euclidean__defs.Per p L A)) as H36.
---------------------------- exact H35.
---------------------------- destruct H36 as [H36 H37].
assert (* Cut *) (euclidean__defs.Per A L p) as H38.
----------------------------- apply (@lemma__8__2.lemma__8__2 (p) (L) (A) H37).
----------------------------- assert (* Cut *) (~(B = N)) as H39.
------------------------------ intro H39.
assert (* Cut *) (euclidean__axioms.BetS D B A) as H40.
------------------------------- apply (@eq__ind__r euclidean__axioms.Point N (fun B0: euclidean__axioms.Point => (euclidean__axioms.Triangle A B0 C) -> ((euclidean__defs.Per B0 A C) -> ((euclidean__defs.SQ B0 C E D) -> ((euclidean__axioms.TS D C B0 A) -> ((euclidean__axioms.Col C B0 N) -> ((euclidean__axioms.nCol C B0 D) -> ((euclidean__defs.Per C A B0) -> ((euclidean__axioms.nCol C A B0) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__axioms.neq B0 C) -> ((euclidean__axioms.Cong B0 C E D) -> ((euclidean__axioms.Col C B0 q) -> ((euclidean__axioms.nCol C B0 D) -> ((euclidean__defs.PG B0 C E D) -> ((euclidean__defs.Par B0 C E D) -> ((~(euclidean__defs.Meet B0 C E D)) -> (euclidean__axioms.BetS D B0 A))))))))))))))))))) with (x := B).
--------------------------------intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
exact H5.

-------------------------------- exact H39.
-------------------------------- exact H.
-------------------------------- exact H0.
-------------------------------- exact H1.
-------------------------------- exact H2.
-------------------------------- exact H7.
-------------------------------- exact H8.
-------------------------------- exact H9.
-------------------------------- exact H10.
-------------------------------- exact H11.
-------------------------------- exact H12.
-------------------------------- exact H13.
-------------------------------- exact H14.
-------------------------------- exact H21.
-------------------------------- exact H22.
-------------------------------- exact H23.
-------------------------------- exact H24.
-------------------------------- exact H25.
------------------------------- assert (* Cut *) (euclidean__axioms.Col D B A) as H41.
-------------------------------- right.
right.
right.
right.
left.
exact H40.
-------------------------------- assert (* Cut *) (euclidean__defs.Per D B C) as H42.
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B C E D) /\ ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))))) as H42.
---------------------------------- exact H1.
---------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))))) as H44.
----------------------------------- exact H43.
----------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))) as H46.
------------------------------------ exact H45.
------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))) as H48.
------------------------------------- exact H47.
------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))) as H50.
-------------------------------------- exact H49.
-------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)) as H52.
--------------------------------------- exact H51.
--------------------------------------- destruct H52 as [H52 H53].
exact H48.
--------------------------------- assert (* Cut *) (euclidean__defs.Per A B C) as H43.
---------------------------------- apply (@lemma__collinearright.lemma__collinearright (D) (B) (A) (C) (H42) (H41) H11).
---------------------------------- assert (* Cut *) (~(euclidean__defs.Per C A B)) as H44.
----------------------------------- apply (@lemma__8__7.lemma__8__7 (C) (B) (A) H43).
----------------------------------- assert (* Cut *) (euclidean__defs.Per C A B) as H45.
------------------------------------ apply (@eq__ind__r euclidean__axioms.Point N (fun B0: euclidean__axioms.Point => (euclidean__axioms.Triangle A B0 C) -> ((euclidean__defs.Per B0 A C) -> ((euclidean__defs.SQ B0 C E D) -> ((euclidean__axioms.TS D C B0 A) -> ((euclidean__axioms.Col C B0 N) -> ((euclidean__axioms.nCol C B0 D) -> ((euclidean__defs.Per C A B0) -> ((euclidean__axioms.nCol C A B0) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__axioms.neq B0 C) -> ((euclidean__axioms.Cong B0 C E D) -> ((euclidean__axioms.Col C B0 q) -> ((euclidean__axioms.nCol C B0 D) -> ((euclidean__defs.PG B0 C E D) -> ((euclidean__defs.Par B0 C E D) -> ((~(euclidean__defs.Meet B0 C E D)) -> ((euclidean__axioms.BetS D B0 A) -> ((euclidean__axioms.Col D B0 A) -> ((euclidean__defs.Per D B0 C) -> ((euclidean__defs.Per A B0 C) -> ((~(euclidean__defs.Per C A B0)) -> (euclidean__defs.Per C A B0)))))))))))))))))))))))) with (x := B).
-------------------------------------intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
exact H51.

------------------------------------- exact H39.
------------------------------------- exact H.
------------------------------------- exact H0.
------------------------------------- exact H1.
------------------------------------- exact H2.
------------------------------------- exact H7.
------------------------------------- exact H8.
------------------------------------- exact H9.
------------------------------------- exact H10.
------------------------------------- exact H11.
------------------------------------- exact H12.
------------------------------------- exact H13.
------------------------------------- exact H14.
------------------------------------- exact H21.
------------------------------------- exact H22.
------------------------------------- exact H23.
------------------------------------- exact H24.
------------------------------------- exact H25.
------------------------------------- exact H40.
------------------------------------- exact H41.
------------------------------------- exact H42.
------------------------------------- exact H43.
------------------------------------- exact H44.
------------------------------------ apply (@H27).
-------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (E) (A)).
--------------------------------------intro H46.
apply (@H44 H45).


------------------------------ assert (* Cut *) (euclidean__defs.Par B C E D) as H40.
------------------------------- assert (* AndElim *) ((euclidean__defs.Par B C E D) /\ (euclidean__defs.Par B D C E)) as H40.
-------------------------------- exact H23.
-------------------------------- destruct H40 as [H40 H41].
exact H24.
------------------------------- assert (* Cut *) (euclidean__defs.Par B C D E) as H41.
-------------------------------- assert (* Cut *) ((euclidean__defs.Par C B E D) /\ ((euclidean__defs.Par B C D E) /\ (euclidean__defs.Par C B D E))) as H41.
--------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (C) (E) (D) H40).
--------------------------------- assert (* AndElim *) ((euclidean__defs.Par C B E D) /\ ((euclidean__defs.Par B C D E) /\ (euclidean__defs.Par C B D E))) as H42.
---------------------------------- exact H41.
---------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__defs.Par B C D E) /\ (euclidean__defs.Par C B D E)) as H44.
----------------------------------- exact H43.
----------------------------------- destruct H44 as [H44 H45].
exact H44.
-------------------------------- assert (* Cut *) (euclidean__defs.Par D E B C) as H42.
--------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (B) (C) (D) (E) H41).
--------------------------------- assert (* Cut *) (euclidean__defs.Par D E C B) as H43.
---------------------------------- assert (* Cut *) ((euclidean__defs.Par E D B C) /\ ((euclidean__defs.Par D E C B) /\ (euclidean__defs.Par E D C B))) as H43.
----------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (D) (E) (B) (C) H42).
----------------------------------- assert (* AndElim *) ((euclidean__defs.Par E D B C) /\ ((euclidean__defs.Par D E C B) /\ (euclidean__defs.Par E D C B))) as H44.
------------------------------------ exact H43.
------------------------------------ destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__defs.Par D E C B) /\ (euclidean__defs.Par E D C B)) as H46.
------------------------------------- exact H45.
------------------------------------- destruct H46 as [H46 H47].
exact H46.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq N B) as H44.
----------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (N) H39).
----------------------------------- assert (* Cut *) (euclidean__defs.Par D E N B) as H45.
------------------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel (D) (E) (N) (C) (B) (H43) (H7) H44).
------------------------------------ assert (* Cut *) (euclidean__defs.Par D E B N) as H46.
------------------------------------- assert (* Cut *) ((euclidean__defs.Par E D N B) /\ ((euclidean__defs.Par D E B N) /\ (euclidean__defs.Par E D B N))) as H46.
-------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (D) (E) (N) (B) H45).
-------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E D N B) /\ ((euclidean__defs.Par D E B N) /\ (euclidean__defs.Par E D B N))) as H47.
--------------------------------------- exact H46.
--------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__defs.Par D E B N) /\ (euclidean__defs.Par E D B N)) as H49.
---------------------------------------- exact H48.
---------------------------------------- destruct H49 as [H49 H50].
exact H49.
------------------------------------- assert (* Cut *) (euclidean__defs.TP D E B N) as H47.
-------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B (D) (E) (B) (N) H46).
-------------------------------------- assert (* Cut *) (euclidean__defs.OS B N D E) as H48.
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B N) /\ ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E)))) as H48.
---------------------------------------- exact H47.
---------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq B N) /\ ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E))) as H50.
----------------------------------------- exact H49.
----------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E)) as H52.
------------------------------------------ exact H51.
------------------------------------------ destruct H52 as [H52 H53].
exact H53.
--------------------------------------- assert (* Cut *) (D = D) as H49.
---------------------------------------- apply (@logic.eq__refl (Point) D).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col D D E) as H50.
----------------------------------------- left.
exact H49.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq D N) as H51.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq N A) /\ ((euclidean__axioms.neq D N) /\ (euclidean__axioms.neq D A))) as H51.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (N) (A) H5).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq N A) /\ ((euclidean__axioms.neq D N) /\ (euclidean__axioms.neq D A))) as H52.
-------------------------------------------- exact H51.
-------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq D N) /\ (euclidean__axioms.neq D A)) as H54.
--------------------------------------------- exact H53.
--------------------------------------------- destruct H54 as [H54 H55].
exact H54.
------------------------------------------ assert (* Cut *) (euclidean__defs.Out D N A) as H52.
------------------------------------------- apply (@lemma__ray4.lemma__ray4 (D) (N) (A)).
--------------------------------------------right.
right.
exact H5.

-------------------------------------------- exact H51.
------------------------------------------- assert (* Cut *) (euclidean__defs.OS B A D E) as H53.
-------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 (D) (D) (E) (B) (N) (A) (H48) (H50) H52).
-------------------------------------------- assert (* Cut *) (euclidean__defs.OS B A E D) as H54.
--------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip (D) (E) (B) (A) H53).
--------------------------------------------- assert (* Cut *) (euclidean__defs.OS A B E D) as H55.
---------------------------------------------- assert (* Cut *) ((euclidean__defs.OS A B E D) /\ ((euclidean__defs.OS B A D E) /\ (euclidean__defs.OS A B D E))) as H55.
----------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (E) (D) (B) (A) H54).
----------------------------------------------- assert (* AndElim *) ((euclidean__defs.OS A B E D) /\ ((euclidean__defs.OS B A D E) /\ (euclidean__defs.OS A B D E))) as H56.
------------------------------------------------ exact H55.
------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__defs.OS B A D E) /\ (euclidean__defs.OS A B D E)) as H58.
------------------------------------------------- exact H57.
------------------------------------------------- destruct H58 as [H58 H59].
exact H56.
---------------------------------------------- assert (* Cut *) (~(D = L)) as H56.
----------------------------------------------- intro H56.
assert (* Cut *) (euclidean__defs.Per A D p) as H57.
------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point L (fun D0: euclidean__axioms.Point => (euclidean__defs.SQ B C E D0) -> ((euclidean__axioms.TS D0 C B A) -> ((euclidean__axioms.BetS D0 N A) -> ((euclidean__axioms.nCol C B D0) -> ((euclidean__axioms.Cong B C E D0) -> ((euclidean__axioms.neq E D0) -> ((euclidean__axioms.neq D0 E) -> ((euclidean__axioms.BetS D0 q A) -> ((euclidean__axioms.nCol C B D0) -> ((euclidean__defs.PG B C E D0) -> ((euclidean__defs.Par B C E D0) -> ((~(euclidean__defs.Meet B C E D0)) -> ((~(euclidean__axioms.Col D0 E A)) -> ((euclidean__defs.Perp__at A L D0 E L) -> ((euclidean__axioms.Col D0 E L) -> ((euclidean__axioms.Col D0 E p) -> ((euclidean__defs.Par B C E D0) -> ((euclidean__defs.Par B C D0 E) -> ((euclidean__defs.Par D0 E B C) -> ((euclidean__defs.Par D0 E C B) -> ((euclidean__defs.Par D0 E N B) -> ((euclidean__defs.Par D0 E B N) -> ((euclidean__defs.TP D0 E B N) -> ((euclidean__defs.OS B N D0 E) -> ((D0 = D0) -> ((euclidean__axioms.Col D0 D0 E) -> ((euclidean__axioms.neq D0 N) -> ((euclidean__defs.Out D0 N A) -> ((euclidean__defs.OS B A D0 E) -> ((euclidean__defs.OS B A E D0) -> ((euclidean__defs.OS A B E D0) -> (euclidean__defs.Per A D0 p))))))))))))))))))))))))))))))))) with (x := D).
-------------------------------------------------intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
exact H38.

------------------------------------------------- exact H56.
------------------------------------------------- exact H1.
------------------------------------------------- exact H2.
------------------------------------------------- exact H5.
------------------------------------------------- exact H8.
------------------------------------------------- exact H14.
------------------------------------------------- exact H15.
------------------------------------------------- exact H16.
------------------------------------------------- exact H19.
------------------------------------------------- exact H22.
------------------------------------------------- exact H23.
------------------------------------------------- exact H24.
------------------------------------------------- exact H25.
------------------------------------------------- exact H27.
------------------------------------------------- exact H29.
------------------------------------------------- exact H34.
------------------------------------------------- exact H36.
------------------------------------------------- exact H40.
------------------------------------------------- exact H41.
------------------------------------------------- exact H42.
------------------------------------------------- exact H43.
------------------------------------------------- exact H45.
------------------------------------------------- exact H46.
------------------------------------------------- exact H47.
------------------------------------------------- exact H48.
------------------------------------------------- exact H49.
------------------------------------------------- exact H50.
------------------------------------------------- exact H51.
------------------------------------------------- exact H52.
------------------------------------------------- exact H53.
------------------------------------------------- exact H54.
------------------------------------------------- exact H55.
------------------------------------------------ assert (* Cut *) (euclidean__defs.Per p D A) as H58.
------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point L (fun D0: euclidean__axioms.Point => (euclidean__defs.SQ B C E D0) -> ((euclidean__axioms.TS D0 C B A) -> ((euclidean__axioms.BetS D0 N A) -> ((euclidean__axioms.nCol C B D0) -> ((euclidean__axioms.Cong B C E D0) -> ((euclidean__axioms.neq E D0) -> ((euclidean__axioms.neq D0 E) -> ((euclidean__axioms.BetS D0 q A) -> ((euclidean__axioms.nCol C B D0) -> ((euclidean__defs.PG B C E D0) -> ((euclidean__defs.Par B C E D0) -> ((~(euclidean__defs.Meet B C E D0)) -> ((~(euclidean__axioms.Col D0 E A)) -> ((euclidean__defs.Perp__at A L D0 E L) -> ((euclidean__axioms.Col D0 E L) -> ((euclidean__axioms.Col D0 E p) -> ((euclidean__defs.Par B C E D0) -> ((euclidean__defs.Par B C D0 E) -> ((euclidean__defs.Par D0 E B C) -> ((euclidean__defs.Par D0 E C B) -> ((euclidean__defs.Par D0 E N B) -> ((euclidean__defs.Par D0 E B N) -> ((euclidean__defs.TP D0 E B N) -> ((euclidean__defs.OS B N D0 E) -> ((D0 = D0) -> ((euclidean__axioms.Col D0 D0 E) -> ((euclidean__axioms.neq D0 N) -> ((euclidean__defs.Out D0 N A) -> ((euclidean__defs.OS B A D0 E) -> ((euclidean__defs.OS B A E D0) -> ((euclidean__defs.OS A B E D0) -> ((euclidean__defs.Per A D0 p) -> (euclidean__defs.Per p D0 A)))))))))))))))))))))))))))))))))) with (x := D).
--------------------------------------------------intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
exact H37.

-------------------------------------------------- exact H56.
-------------------------------------------------- exact H1.
-------------------------------------------------- exact H2.
-------------------------------------------------- exact H5.
-------------------------------------------------- exact H8.
-------------------------------------------------- exact H14.
-------------------------------------------------- exact H15.
-------------------------------------------------- exact H16.
-------------------------------------------------- exact H19.
-------------------------------------------------- exact H22.
-------------------------------------------------- exact H23.
-------------------------------------------------- exact H24.
-------------------------------------------------- exact H25.
-------------------------------------------------- exact H27.
-------------------------------------------------- exact H29.
-------------------------------------------------- exact H34.
-------------------------------------------------- exact H36.
-------------------------------------------------- exact H40.
-------------------------------------------------- exact H41.
-------------------------------------------------- exact H42.
-------------------------------------------------- exact H43.
-------------------------------------------------- exact H45.
-------------------------------------------------- exact H46.
-------------------------------------------------- exact H47.
-------------------------------------------------- exact H48.
-------------------------------------------------- exact H49.
-------------------------------------------------- exact H50.
-------------------------------------------------- exact H51.
-------------------------------------------------- exact H52.
-------------------------------------------------- exact H53.
-------------------------------------------------- exact H54.
-------------------------------------------------- exact H55.
-------------------------------------------------- exact H57.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p D E) as H59.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E D p) /\ ((euclidean__axioms.Col E p D) /\ ((euclidean__axioms.Col p D E) /\ ((euclidean__axioms.Col D p E) /\ (euclidean__axioms.Col p E D))))) as H59.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (E) (p) H36).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E D p) /\ ((euclidean__axioms.Col E p D) /\ ((euclidean__axioms.Col p D E) /\ ((euclidean__axioms.Col D p E) /\ (euclidean__axioms.Col p E D))))) as H60.
---------------------------------------------------- exact H59.
---------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col E p D) /\ ((euclidean__axioms.Col p D E) /\ ((euclidean__axioms.Col D p E) /\ (euclidean__axioms.Col p E D)))) as H62.
----------------------------------------------------- exact H61.
----------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col p D E) /\ ((euclidean__axioms.Col D p E) /\ (euclidean__axioms.Col p E D))) as H64.
------------------------------------------------------ exact H63.
------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col D p E) /\ (euclidean__axioms.Col p E D)) as H66.
------------------------------------------------------- exact H65.
------------------------------------------------------- destruct H66 as [H66 H67].
exact H64.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E D A) as H60.
--------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (p) (D) (E) (A) (H58) (H59) H15).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E D B) as H61.
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B C E D) /\ ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))))) as H61.
----------------------------------------------------- exact H1.
----------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))))) as H63.
------------------------------------------------------ exact H62.
------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))) as H65.
------------------------------------------------------- exact H64.
------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))) as H67.
-------------------------------------------------------- exact H66.
-------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))) as H69.
--------------------------------------------------------- exact H68.
--------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)) as H71.
---------------------------------------------------------- exact H70.
---------------------------------------------------------- destruct H71 as [H71 H72].
exact H72.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Out D A B) as H62.
----------------------------------------------------- apply (@lemma__erectedperpendicularunique.lemma__erectedperpendicularunique (E) (D) (A) (B) (H60) (H61) H55).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D A B) as H63.
------------------------------------------------------ apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (D) (A) (B) H62).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A D B) as H64.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A D B) /\ ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D B A) /\ (euclidean__axioms.Col B A D))))) as H64.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (A) (B) H63).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A D B) /\ ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D B A) /\ (euclidean__axioms.Col B A D))))) as H65.
--------------------------------------------------------- exact H64.
--------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D B A) /\ (euclidean__axioms.Col B A D)))) as H67.
---------------------------------------------------------- exact H66.
---------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D B A) /\ (euclidean__axioms.Col B A D))) as H69.
----------------------------------------------------------- exact H68.
----------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col D B A) /\ (euclidean__axioms.Col B A D)) as H71.
------------------------------------------------------------ exact H70.
------------------------------------------------------------ destruct H71 as [H71 H72].
exact H65.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D N A) as H65.
-------------------------------------------------------- right.
right.
right.
right.
left.
exact H5.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D N) as H66.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col N D A) /\ ((euclidean__axioms.Col N A D) /\ ((euclidean__axioms.Col A D N) /\ ((euclidean__axioms.Col D A N) /\ (euclidean__axioms.Col A N D))))) as H66.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (N) (A) H65).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col N D A) /\ ((euclidean__axioms.Col N A D) /\ ((euclidean__axioms.Col A D N) /\ ((euclidean__axioms.Col D A N) /\ (euclidean__axioms.Col A N D))))) as H67.
----------------------------------------------------------- exact H66.
----------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col N A D) /\ ((euclidean__axioms.Col A D N) /\ ((euclidean__axioms.Col D A N) /\ (euclidean__axioms.Col A N D)))) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A D N) /\ ((euclidean__axioms.Col D A N) /\ (euclidean__axioms.Col A N D))) as H71.
------------------------------------------------------------- exact H70.
------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col D A N) /\ (euclidean__axioms.Col A N D)) as H73.
-------------------------------------------------------------- exact H72.
-------------------------------------------------------------- destruct H73 as [H73 H74].
exact H71.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D A) as H67.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq q A) /\ ((euclidean__axioms.neq D q) /\ (euclidean__axioms.neq D A))) as H67.
----------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (q) (A) H19).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq q A) /\ ((euclidean__axioms.neq D q) /\ (euclidean__axioms.neq D A))) as H68.
------------------------------------------------------------ exact H67.
------------------------------------------------------------ destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq D q) /\ (euclidean__axioms.neq D A)) as H70.
------------------------------------------------------------- exact H69.
------------------------------------------------------------- destruct H70 as [H70 H71].
exact H71.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H68.
----------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (A) H67).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B N) as H69.
------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (D) (B) (N)).
-------------------------------------------------------------intro H69.
apply (@euclidean__tactics.Col__nCol__False (D) (B) (N) (H69)).
--------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (D) (B) (N) (H64) (H66) H68).


------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col N B C) as H70.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C N) /\ ((euclidean__axioms.Col B N C) /\ ((euclidean__axioms.Col N C B) /\ ((euclidean__axioms.Col C N B) /\ (euclidean__axioms.Col N B C))))) as H70.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (N) H7).
-------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C N) /\ ((euclidean__axioms.Col B N C) /\ ((euclidean__axioms.Col N C B) /\ ((euclidean__axioms.Col C N B) /\ (euclidean__axioms.Col N B C))))) as H71.
--------------------------------------------------------------- exact H70.
--------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col B N C) /\ ((euclidean__axioms.Col N C B) /\ ((euclidean__axioms.Col C N B) /\ (euclidean__axioms.Col N B C)))) as H73.
---------------------------------------------------------------- exact H72.
---------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col N C B) /\ ((euclidean__axioms.Col C N B) /\ (euclidean__axioms.Col N B C))) as H75.
----------------------------------------------------------------- exact H74.
----------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col C N B) /\ (euclidean__axioms.Col N B C)) as H77.
------------------------------------------------------------------ exact H76.
------------------------------------------------------------------ destruct H77 as [H77 H78].
exact H78.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col N B D) as H71.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B D N) /\ ((euclidean__axioms.Col B N D) /\ ((euclidean__axioms.Col N D B) /\ ((euclidean__axioms.Col D N B) /\ (euclidean__axioms.Col N B D))))) as H71.
--------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (B) (N) H69).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B D N) /\ ((euclidean__axioms.Col B N D) /\ ((euclidean__axioms.Col N D B) /\ ((euclidean__axioms.Col D N B) /\ (euclidean__axioms.Col N B D))))) as H72.
---------------------------------------------------------------- exact H71.
---------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col B N D) /\ ((euclidean__axioms.Col N D B) /\ ((euclidean__axioms.Col D N B) /\ (euclidean__axioms.Col N B D)))) as H74.
----------------------------------------------------------------- exact H73.
----------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col N D B) /\ ((euclidean__axioms.Col D N B) /\ (euclidean__axioms.Col N B D))) as H76.
------------------------------------------------------------------ exact H75.
------------------------------------------------------------------ destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col D N B) /\ (euclidean__axioms.Col N B D)) as H78.
------------------------------------------------------------------- exact H77.
------------------------------------------------------------------- destruct H78 as [H78 H79].
exact H79.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H72.
--------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (C) (D)).
----------------------------------------------------------------intro H72.
apply (@euclidean__tactics.Col__nCol__False (B) (C) (D) (H72)).
-----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (N) (B) (C) (D) (H70) (H71) H44).


--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C D) as H73.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol D B C))))) as H73.
----------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (C) (B) (D) H22).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol D B C))))) as H74.
------------------------------------------------------------------ exact H73.
------------------------------------------------------------------ destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol D B C)))) as H76.
------------------------------------------------------------------- exact H75.
------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol D B C))) as H78.
-------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol D B C)) as H80.
--------------------------------------------------------------------- exact H79.
--------------------------------------------------------------------- destruct H80 as [H80 H81].
exact H74.
---------------------------------------------------------------- apply (@H27).
-----------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (E) (A)).
------------------------------------------------------------------intro H74.
apply (@euclidean__tactics.Col__nCol__False (B) (C) (D) (H73) H72).


----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L D) as H57.
------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (L) H56).
------------------------------------------------ assert (* Cut *) (euclidean__defs.Par B C E D) as H58.
------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par E D B N) /\ ((euclidean__defs.Par D E N B) /\ (euclidean__defs.Par E D N B))) as H58.
-------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (D) (E) (B) (N) H46).
-------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par E D B N) /\ ((euclidean__defs.Par D E N B) /\ (euclidean__defs.Par E D N B))) as H59.
--------------------------------------------------- exact H58.
--------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__defs.Par D E N B) /\ (euclidean__defs.Par E D N B)) as H61.
---------------------------------------------------- exact H60.
---------------------------------------------------- destruct H61 as [H61 H62].
exact H40.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D L) as H59.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E D L) /\ ((euclidean__axioms.Col E L D) /\ ((euclidean__axioms.Col L D E) /\ ((euclidean__axioms.Col D L E) /\ (euclidean__axioms.Col L E D))))) as H59.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (E) (L) H34).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E D L) /\ ((euclidean__axioms.Col E L D) /\ ((euclidean__axioms.Col L D E) /\ ((euclidean__axioms.Col D L E) /\ (euclidean__axioms.Col L E D))))) as H60.
---------------------------------------------------- exact H59.
---------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col E L D) /\ ((euclidean__axioms.Col L D E) /\ ((euclidean__axioms.Col D L E) /\ (euclidean__axioms.Col L E D)))) as H62.
----------------------------------------------------- exact H61.
----------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col L D E) /\ ((euclidean__axioms.Col D L E) /\ (euclidean__axioms.Col L E D))) as H64.
------------------------------------------------------ exact H63.
------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col D L E) /\ (euclidean__axioms.Col L E D)) as H66.
------------------------------------------------------- exact H65.
------------------------------------------------------- destruct H66 as [H66 H67].
exact H60.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B C L D) as H60.
--------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (B) (C) (L) (E) (D) (H58) (H59) H57).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Par L D B C) as H61.
---------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (B) (C) (L) (D) H60).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.TP B C L D) as H62.
----------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B (B) (C) (L) (D) H60).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.OS L D B C) as H63.
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq L D) /\ ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C)))) as H63.
------------------------------------------------------- exact H62.
------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.neq L D) /\ ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C))) as H65.
-------------------------------------------------------- exact H64.
-------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C)) as H67.
--------------------------------------------------------- exact H66.
--------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B N) /\ ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E)))) as H69.
---------------------------------------------------------- exact H47.
---------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.neq B N) /\ ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E))) as H71.
----------------------------------------------------------- exact H70.
----------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E)) as H73.
------------------------------------------------------------ exact H72.
------------------------------------------------------------ destruct H73 as [H73 H74].
exact H68.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B C D) as H64.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B C L) /\ ((euclidean__axioms.nCol B L D) /\ ((euclidean__axioms.nCol C L D) /\ (euclidean__axioms.nCol B C D)))) as H64.
-------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (B) (C) (L) (D) H60).
-------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B C L) /\ ((euclidean__axioms.nCol B L D) /\ ((euclidean__axioms.nCol C L D) /\ (euclidean__axioms.nCol B C D)))) as H65.
--------------------------------------------------------- exact H64.
--------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.nCol B L D) /\ ((euclidean__axioms.nCol C L D) /\ (euclidean__axioms.nCol B C D))) as H67.
---------------------------------------------------------- exact H66.
---------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.nCol C L D) /\ (euclidean__axioms.nCol B C D)) as H69.
----------------------------------------------------------- exact H68.
----------------------------------------------------------- destruct H69 as [H69 H70].
exact H70.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C N) as H65.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C N) /\ ((euclidean__axioms.Col B N C) /\ ((euclidean__axioms.Col N C B) /\ ((euclidean__axioms.Col C N B) /\ (euclidean__axioms.Col N B C))))) as H65.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (N) H7).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C N) /\ ((euclidean__axioms.Col B N C) /\ ((euclidean__axioms.Col N C B) /\ ((euclidean__axioms.Col C N B) /\ (euclidean__axioms.Col N B C))))) as H66.
---------------------------------------------------------- exact H65.
---------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col B N C) /\ ((euclidean__axioms.Col N C B) /\ ((euclidean__axioms.Col C N B) /\ (euclidean__axioms.Col N B C)))) as H68.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col N C B) /\ ((euclidean__axioms.Col C N B) /\ (euclidean__axioms.Col N B C))) as H70.
------------------------------------------------------------ exact H69.
------------------------------------------------------------ destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col C N B) /\ (euclidean__axioms.Col N B C)) as H72.
------------------------------------------------------------- exact H71.
------------------------------------------------------------- destruct H72 as [H72 H73].
exact H66.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS D B C A) as H66.
--------------------------------------------------------- exists N.
split.
---------------------------------------------------------- exact H5.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H65.
----------------------------------------------------------- exact H64.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS L B C A) as H67.
---------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation (B) (C) (L) (D) (A) (H63) H66).
---------------------------------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS L M A) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.nCol B C L))) as H68.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS L M A) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.nCol B C L)))) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [M H69].
assert (* AndElim *) ((euclidean__axioms.BetS L M A) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.nCol B C L))) as H70.
------------------------------------------------------------- exact H69.
------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.nCol B C L)) as H72.
-------------------------------------------------------------- exact H71.
-------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* Cut *) (euclidean__axioms.neq D E) as H74.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq C L) /\ ((euclidean__axioms.neq B L) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq L C) /\ (euclidean__axioms.neq L B)))))) as H74.
---------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (B) (C) (L) H73).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq C L) /\ ((euclidean__axioms.neq B L) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq L C) /\ (euclidean__axioms.neq L B)))))) as H75.
----------------------------------------------------------------- exact H74.
----------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.neq C L) /\ ((euclidean__axioms.neq B L) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq L C) /\ (euclidean__axioms.neq L B))))) as H77.
------------------------------------------------------------------ exact H76.
------------------------------------------------------------------ destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq B L) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq L C) /\ (euclidean__axioms.neq L B)))) as H79.
------------------------------------------------------------------- exact H78.
------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq L C) /\ (euclidean__axioms.neq L B))) as H81.
-------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.neq L C) /\ (euclidean__axioms.neq L B)) as H83.
--------------------------------------------------------------------- exact H82.
--------------------------------------------------------------------- destruct H83 as [H83 H84].
exact H16.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E D) as H75.
---------------------------------------------------------------- exact H15.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L M) as H76.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A))) as H76.
------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (L) (M) (A) H70).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A))) as H77.
------------------------------------------------------------------- exact H76.
------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A)) as H79.
-------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------- destruct H79 as [H79 H80].
exact H79.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out L M A) as H77.
------------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 (L) (M) (A)).
-------------------------------------------------------------------right.
right.
exact H70.

------------------------------------------------------------------- exact H76.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out L A M) as H78.
------------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (L) (M) (A) H77).
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E D B) as H79.
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B C E D) /\ ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))))) as H79.
--------------------------------------------------------------------- exact H1.
--------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))))) as H81.
---------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))) as H83.
----------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))) as H85.
------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------ destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))) as H87.
------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)) as H89.
-------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------- destruct H89 as [H89 H90].
exact H90.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D p) as H80.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E D p) /\ ((euclidean__axioms.Col E p D) /\ ((euclidean__axioms.Col p D E) /\ ((euclidean__axioms.Col D p E) /\ (euclidean__axioms.Col p E D))))) as H80.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (E) (p) H36).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E D p) /\ ((euclidean__axioms.Col E p D) /\ ((euclidean__axioms.Col p D E) /\ ((euclidean__axioms.Col D p E) /\ (euclidean__axioms.Col p E D))))) as H81.
----------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col E p D) /\ ((euclidean__axioms.Col p D E) /\ ((euclidean__axioms.Col D p E) /\ (euclidean__axioms.Col p E D)))) as H83.
------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------ destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col p D E) /\ ((euclidean__axioms.Col D p E) /\ (euclidean__axioms.Col p E D))) as H85.
------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col D p E) /\ (euclidean__axioms.Col p E D)) as H87.
-------------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------------- destruct H87 as [H87 H88].
exact H81.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E D L) as H81.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D E p) /\ ((euclidean__axioms.Col D p E) /\ ((euclidean__axioms.Col p E D) /\ ((euclidean__axioms.Col E p D) /\ (euclidean__axioms.Col p D E))))) as H81.
----------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (E) (D) (p) H80).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D E p) /\ ((euclidean__axioms.Col D p E) /\ ((euclidean__axioms.Col p E D) /\ ((euclidean__axioms.Col E p D) /\ (euclidean__axioms.Col p D E))))) as H82.
------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------ destruct H82 as [H82 H83].
assert (* AndElim *) ((euclidean__axioms.Col D p E) /\ ((euclidean__axioms.Col p E D) /\ ((euclidean__axioms.Col E p D) /\ (euclidean__axioms.Col p D E)))) as H84.
------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col p E D) /\ ((euclidean__axioms.Col E p D) /\ (euclidean__axioms.Col p D E))) as H86.
-------------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col E p D) /\ (euclidean__axioms.Col p D E)) as H88.
--------------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------------- destruct H88 as [H88 H89].
exact H59.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D p L) as H82.
----------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (D) (p) (L)).
------------------------------------------------------------------------intro H82.
apply (@euclidean__tactics.Col__nCol__False (D) (p) (L) (H82)).
-------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (E) (D) (p) (L) (H80) (H81) H75).


----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p L D) as H83.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col p D L) /\ ((euclidean__axioms.Col p L D) /\ ((euclidean__axioms.Col L D p) /\ ((euclidean__axioms.Col D L p) /\ (euclidean__axioms.Col L p D))))) as H83.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (p) (L) H82).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p D L) /\ ((euclidean__axioms.Col p L D) /\ ((euclidean__axioms.Col L D p) /\ ((euclidean__axioms.Col D L p) /\ (euclidean__axioms.Col L p D))))) as H84.
-------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------- destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.Col p L D) /\ ((euclidean__axioms.Col L D p) /\ ((euclidean__axioms.Col D L p) /\ (euclidean__axioms.Col L p D)))) as H86.
--------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.Col L D p) /\ ((euclidean__axioms.Col D L p) /\ (euclidean__axioms.Col L p D))) as H88.
---------------------------------------------------------------------------- exact H87.
---------------------------------------------------------------------------- destruct H88 as [H88 H89].
assert (* AndElim *) ((euclidean__axioms.Col D L p) /\ (euclidean__axioms.Col L p D)) as H90.
----------------------------------------------------------------------------- exact H89.
----------------------------------------------------------------------------- destruct H90 as [H90 H91].
exact H86.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Per D L A) as H84.
------------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (p) (L) (D) (A) (H37) (H83) H56).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per D L M) as H85.
-------------------------------------------------------------------------- apply (@lemma__8__3.lemma__8__3 (D) (L) (A) (M) (H84) H78).
-------------------------------------------------------------------------- assert (* Cut *) (~(B = M)) as H86.
--------------------------------------------------------------------------- intro H86.
assert (* Cut *) (euclidean__defs.Per D L B) as H87.
---------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point M (fun B0: euclidean__axioms.Point => (euclidean__axioms.Triangle A B0 C) -> ((euclidean__defs.Per B0 A C) -> ((euclidean__defs.SQ B0 C E D) -> ((euclidean__axioms.TS D C B0 A) -> ((euclidean__axioms.Col C B0 N) -> ((euclidean__axioms.nCol C B0 D) -> ((euclidean__defs.Per C A B0) -> ((euclidean__axioms.nCol C A B0) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__axioms.neq B0 C) -> ((euclidean__axioms.Cong B0 C E D) -> ((euclidean__axioms.Col C B0 q) -> ((euclidean__axioms.nCol C B0 D) -> ((euclidean__defs.PG B0 C E D) -> ((euclidean__defs.Par B0 C E D) -> ((~(euclidean__defs.Meet B0 C E D)) -> ((~(B0 = N)) -> ((euclidean__defs.Par B0 C E D) -> ((euclidean__defs.Par B0 C D E) -> ((euclidean__defs.Par D E B0 C) -> ((euclidean__defs.Par D E C B0) -> ((euclidean__axioms.neq N B0) -> ((euclidean__defs.Par D E N B0) -> ((euclidean__defs.Par D E B0 N) -> ((euclidean__defs.TP D E B0 N) -> ((euclidean__defs.OS B0 N D E) -> ((euclidean__defs.OS B0 A D E) -> ((euclidean__defs.OS B0 A E D) -> ((euclidean__defs.OS A B0 E D) -> ((euclidean__defs.Par B0 C E D) -> ((euclidean__defs.Par B0 C L D) -> ((euclidean__defs.Par L D B0 C) -> ((euclidean__defs.TP B0 C L D) -> ((euclidean__defs.OS L D B0 C) -> ((euclidean__axioms.nCol B0 C D) -> ((euclidean__axioms.Col B0 C N) -> ((euclidean__axioms.TS D B0 C A) -> ((euclidean__axioms.TS L B0 C A) -> ((euclidean__axioms.Col B0 C M) -> ((euclidean__axioms.nCol B0 C L) -> ((euclidean__defs.Per E D B0) -> (euclidean__defs.Per D L B0)))))))))))))))))))))))))))))))))))))))))))) with (x := B).
-----------------------------------------------------------------------------intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
exact H85.

----------------------------------------------------------------------------- exact H86.
----------------------------------------------------------------------------- exact H.
----------------------------------------------------------------------------- exact H0.
----------------------------------------------------------------------------- exact H1.
----------------------------------------------------------------------------- exact H2.
----------------------------------------------------------------------------- exact H7.
----------------------------------------------------------------------------- exact H8.
----------------------------------------------------------------------------- exact H9.
----------------------------------------------------------------------------- exact H10.
----------------------------------------------------------------------------- exact H11.
----------------------------------------------------------------------------- exact H12.
----------------------------------------------------------------------------- exact H13.
----------------------------------------------------------------------------- exact H14.
----------------------------------------------------------------------------- exact H21.
----------------------------------------------------------------------------- exact H22.
----------------------------------------------------------------------------- exact H23.
----------------------------------------------------------------------------- exact H24.
----------------------------------------------------------------------------- exact H25.
----------------------------------------------------------------------------- exact H39.
----------------------------------------------------------------------------- exact H40.
----------------------------------------------------------------------------- exact H41.
----------------------------------------------------------------------------- exact H42.
----------------------------------------------------------------------------- exact H43.
----------------------------------------------------------------------------- exact H44.
----------------------------------------------------------------------------- exact H45.
----------------------------------------------------------------------------- exact H46.
----------------------------------------------------------------------------- exact H47.
----------------------------------------------------------------------------- exact H48.
----------------------------------------------------------------------------- exact H53.
----------------------------------------------------------------------------- exact H54.
----------------------------------------------------------------------------- exact H55.
----------------------------------------------------------------------------- exact H58.
----------------------------------------------------------------------------- exact H60.
----------------------------------------------------------------------------- exact H61.
----------------------------------------------------------------------------- exact H62.
----------------------------------------------------------------------------- exact H63.
----------------------------------------------------------------------------- exact H64.
----------------------------------------------------------------------------- exact H65.
----------------------------------------------------------------------------- exact H66.
----------------------------------------------------------------------------- exact H67.
----------------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------------- exact H79.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per L D B) as H88.
----------------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (E) (D) (L) (B) (H79) (H81) H57).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B D L) as H89.
------------------------------------------------------------------------------ apply (@lemma__8__2.lemma__8__2 (L) (D) (B) H88).
------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__defs.Per B D L)) as H90.
------------------------------------------------------------------------------- apply (@lemma__8__7.lemma__8__7 (B) (L) (D) H87).
------------------------------------------------------------------------------- apply (@H27).
--------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (E) (A)).
---------------------------------------------------------------------------------intro H91.
apply (@H90 H89).


--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M B) as H87.
---------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (M) H86).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par L D C B) as H88.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par D L B C) /\ ((euclidean__defs.Par L D C B) /\ (euclidean__defs.Par D L C B))) as H88.
------------------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip (L) (D) (B) (C) H61).
------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__defs.Par D L B C) /\ ((euclidean__defs.Par L D C B) /\ (euclidean__defs.Par D L C B))) as H89.
------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__defs.Par L D C B) /\ (euclidean__defs.Par D L C B)) as H91.
-------------------------------------------------------------------------------- exact H90.
-------------------------------------------------------------------------------- destruct H91 as [H91 H92].
exact H91.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B M) as H89.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col C M B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B))))) as H89.
------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (M) H72).
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col C M B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B))))) as H90.
-------------------------------------------------------------------------------- exact H89.
-------------------------------------------------------------------------------- destruct H90 as [H90 H91].
assert (* AndElim *) ((euclidean__axioms.Col C M B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B)))) as H92.
--------------------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B))) as H94.
---------------------------------------------------------------------------------- exact H93.
---------------------------------------------------------------------------------- destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B)) as H96.
----------------------------------------------------------------------------------- exact H95.
----------------------------------------------------------------------------------- destruct H96 as [H96 H97].
exact H90.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par L D M B) as H90.
------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (L) (D) (M) (C) (B) (H88) (H89) H87).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par L D B M) as H91.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par D L M B) /\ ((euclidean__defs.Par L D B M) /\ (euclidean__defs.Par D L B M))) as H91.
--------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (L) (D) (M) (B) H90).
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par D L M B) /\ ((euclidean__defs.Par L D B M) /\ (euclidean__defs.Par D L B M))) as H92.
---------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------- destruct H92 as [H92 H93].
assert (* AndElim *) ((euclidean__defs.Par L D B M) /\ (euclidean__defs.Par D L B M)) as H94.
----------------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------------- destruct H94 as [H94 H95].
exact H94.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B M L D) as H92.
--------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (L) (D) (B) (M) H91).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B M D L) as H93.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par M B L D) /\ ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L))) as H93.
----------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (M) (L) (D) H92).
----------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par M B L D) /\ ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L))) as H94.
------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------ destruct H94 as [H94 H95].
assert (* AndElim *) ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L)) as H96.
------------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
exact H96.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par D L B M) as H94.
----------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (B) (M) (D) (L) H93).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP D L B M) as H95.
------------------------------------------------------------------------------------ apply (@lemma__paralleldef2B.lemma__paralleldef2B (D) (L) (B) (M) H94).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS B M D L) as H96.
------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.neq B M) /\ ((~(euclidean__defs.Meet D L B M)) /\ (euclidean__defs.OS B M D L)))) as H96.
-------------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.neq B M) /\ ((~(euclidean__defs.Meet D L B M)) /\ (euclidean__defs.OS B M D L))) as H98.
--------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((~(euclidean__defs.Meet D L B M)) /\ (euclidean__defs.OS B M D L)) as H100.
---------------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq L D) /\ ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C)))) as H102.
----------------------------------------------------------------------------------------- exact H62.
----------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__axioms.neq L D) /\ ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C))) as H104.
------------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------------ destruct H104 as [H104 H105].
assert (* AndElim *) ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C)) as H106.
------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B N) /\ ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E)))) as H108.
-------------------------------------------------------------------------------------------- exact H47.
-------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.neq B N) /\ ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E))) as H110.
--------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
assert (* AndElim *) ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E)) as H112.
---------------------------------------------------------------------------------------------- exact H111.
---------------------------------------------------------------------------------------------- destruct H112 as [H112 H113].
exact H101.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B M L D) as H97.
-------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per L D B) as H98.
--------------------------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (E) (D) (L) (B) (H79) (H81) H57).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B D L) as H99.
---------------------------------------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (L) (D) (B) H98).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D L M) as H100.
----------------------------------------------------------------------------------------- apply (@lemma__twoperpsparallel.lemma__twoperpsparallel (B) (D) (L) (M) (H99) (H85) H96).
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D M L) as H101.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par D B L M) /\ ((euclidean__defs.Par B D M L) /\ (euclidean__defs.Par D B M L))) as H101.
------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (D) (L) (M) H100).
------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par D B L M) /\ ((euclidean__defs.Par B D M L) /\ (euclidean__defs.Par D B M L))) as H102.
-------------------------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------------------------- destruct H102 as [H102 H103].
assert (* AndElim *) ((euclidean__defs.Par B D M L) /\ (euclidean__defs.Par D B M L)) as H104.
--------------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
exact H104.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.PG B M L D) as H102.
------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M L B D) as H103.
-------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (B) (D) (M) (L) H101).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP M L B D) as H104.
--------------------------------------------------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B (M) (L) (B) (D) H103).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS B D M L) as H105.
---------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__defs.Meet M L B D)) /\ (euclidean__defs.OS B D M L)))) as H105.
----------------------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__defs.Meet M L B D)) /\ (euclidean__defs.OS B D M L))) as H107.
------------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------------ destruct H107 as [H107 H108].
assert (* AndElim *) ((~(euclidean__defs.Meet M L B D)) /\ (euclidean__defs.OS B D M L)) as H109.
------------------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.neq B M) /\ ((~(euclidean__defs.Meet D L B M)) /\ (euclidean__defs.OS B M D L)))) as H111.
-------------------------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.neq B M) /\ ((~(euclidean__defs.Meet D L B M)) /\ (euclidean__defs.OS B M D L))) as H113.
--------------------------------------------------------------------------------------------------- exact H112.
--------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((~(euclidean__defs.Meet D L B M)) /\ (euclidean__defs.OS B M D L)) as H115.
---------------------------------------------------------------------------------------------------- exact H114.
---------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq L D) /\ ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C)))) as H117.
----------------------------------------------------------------------------------------------------- exact H62.
----------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.neq L D) /\ ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C))) as H119.
------------------------------------------------------------------------------------------------------ exact H118.
------------------------------------------------------------------------------------------------------ destruct H119 as [H119 H120].
assert (* AndElim *) ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C)) as H121.
------------------------------------------------------------------------------------------------------- exact H120.
------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B N) /\ ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E)))) as H123.
-------------------------------------------------------------------------------------------------------- exact H47.
-------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.neq B N) /\ ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E))) as H125.
--------------------------------------------------------------------------------------------------------- exact H124.
--------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E)) as H127.
---------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
exact H110.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A M L) as H106.
----------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (L) (M) (A) H70).
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M B L D) as H107.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par M B L D) /\ ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L))) as H107.
------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (M) (L) (D) H97).
------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par M B L D) /\ ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L))) as H108.
-------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------- destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L)) as H110.
--------------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
exact H108.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A M B M L D) as H108.
------------------------------------------------------------------------------------------------- assert (* Cut *) (forall (B0: euclidean__axioms.Point) (D0: euclidean__axioms.Point) (E0: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H108: euclidean__axioms.Point), (euclidean__defs.Par G B0 H108 D0) -> ((euclidean__defs.OS B0 D0 G H108) -> ((euclidean__axioms.BetS E0 G H108) -> (euclidean__defs.CongA E0 G B0 G H108 D0)))) as H108.
-------------------------------------------------------------------------------------------------- intro B0.
intro D0.
intro E0.
intro G.
intro H108.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA E0 G B0 G H108 D0) /\ (euclidean__defs.RT B0 G H108 G H108 D0)) as __2.
--------------------------------------------------------------------------------------------------- apply (@proposition__29C.proposition__29C (B0) (D0) (E0) (G) (H108) (__) (__0) __1).
--------------------------------------------------------------------------------------------------- destruct __2 as [__2 __3].
exact __2.
-------------------------------------------------------------------------------------------------- apply (@H108 (B) (D) (A) (M) (L) (H107) (H105) H106).
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per M L D) as H109.
-------------------------------------------------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (D) (L) (M) H85).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per A M B) as H110.
--------------------------------------------------------------------------------------------------- apply (@lemma__equaltorightisright.lemma__equaltorightisright (M) (L) (D) (A) (M) (B) (H109) H108).
--------------------------------------------------------------------------------------------------- assert (* Cut *) (B = B) as H111.
---------------------------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) B).
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C B) as H112.
----------------------------------------------------------------------------------------------------- right.
left.
exact H111.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B M C) as H113.
------------------------------------------------------------------------------------------------------ apply (@lemma__altitudeofrighttriangle.lemma__altitudeofrighttriangle (A) (B) (C) (M) (B) (H0) (H110) (H112) H72).
------------------------------------------------------------------------------------------------------ assert (* Cut *) (~(M = C)) as H114.
------------------------------------------------------------------------------------------------------- intro H114.
assert (* Cut *) (euclidean__defs.Per A C B) as H115.
-------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun M0: euclidean__axioms.Point => (euclidean__axioms.BetS L M0 A) -> ((euclidean__axioms.Col B C M0) -> ((euclidean__axioms.neq L M0) -> ((euclidean__defs.Out L M0 A) -> ((euclidean__defs.Out L A M0) -> ((euclidean__defs.Per D L M0) -> ((~(B = M0)) -> ((euclidean__axioms.neq M0 B) -> ((euclidean__axioms.Col C B M0) -> ((euclidean__defs.Par L D M0 B) -> ((euclidean__defs.Par L D B M0) -> ((euclidean__defs.Par B M0 L D) -> ((euclidean__defs.Par B M0 D L) -> ((euclidean__defs.Par D L B M0) -> ((euclidean__defs.TP D L B M0) -> ((euclidean__defs.OS B M0 D L) -> ((euclidean__defs.Par B M0 L D) -> ((euclidean__defs.Par B D L M0) -> ((euclidean__defs.Par B D M0 L) -> ((euclidean__defs.PG B M0 L D) -> ((euclidean__defs.Par M0 L B D) -> ((euclidean__defs.TP M0 L B D) -> ((euclidean__defs.OS B D M0 L) -> ((euclidean__axioms.BetS A M0 L) -> ((euclidean__defs.Par M0 B L D) -> ((euclidean__defs.CongA A M0 B M0 L D) -> ((euclidean__defs.Per M0 L D) -> ((euclidean__defs.Per A M0 B) -> ((euclidean__axioms.BetS B M0 C) -> (euclidean__defs.Per A C B))))))))))))))))))))))))))))))) with (x := M).
---------------------------------------------------------------------------------------------------------intro H115.
intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
exact H142.

--------------------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------------------- exact H70.
--------------------------------------------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------------------------------------------- exact H76.
--------------------------------------------------------------------------------------------------------- exact H77.
--------------------------------------------------------------------------------------------------------- exact H78.
--------------------------------------------------------------------------------------------------------- exact H85.
--------------------------------------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------------------------------------------- exact H89.
--------------------------------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------------------------------- exact H91.
--------------------------------------------------------------------------------------------------------- exact H92.
--------------------------------------------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------------------------------------------- exact H94.
--------------------------------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------------------------------- exact H96.
--------------------------------------------------------------------------------------------------------- exact H97.
--------------------------------------------------------------------------------------------------------- exact H100.
--------------------------------------------------------------------------------------------------------- exact H101.
--------------------------------------------------------------------------------------------------------- exact H102.
--------------------------------------------------------------------------------------------------------- exact H103.
--------------------------------------------------------------------------------------------------------- exact H104.
--------------------------------------------------------------------------------------------------------- exact H105.
--------------------------------------------------------------------------------------------------------- exact H106.
--------------------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------------------------- exact H109.
--------------------------------------------------------------------------------------------------------- exact H110.
--------------------------------------------------------------------------------------------------------- exact H113.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Per B A C)) as H116.
--------------------------------------------------------------------------------------------------------- apply (@lemma__8__7.lemma__8__7 (B) (C) (A) H115).
--------------------------------------------------------------------------------------------------------- apply (@H27).
----------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (E) (A)).
-----------------------------------------------------------------------------------------------------------intro H117.
apply (@H116 H0).


------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(L = E)) as H115.
-------------------------------------------------------------------------------------------------------- intro H115.
assert (* Cut *) (euclidean__defs.Par B D C E) as H116.
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par B M L D) /\ (euclidean__defs.Par B D M L)) as H116.
---------------------------------------------------------------------------------------------------------- exact H102.
---------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__defs.Par B C E D) /\ (euclidean__defs.Par B D C E)) as H118.
----------------------------------------------------------------------------------------------------------- exact H23.
----------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
exact H119.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C E B D) as H117.
---------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (B) (D) (C) (E) H116).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M E B D) as H118.
----------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun L0: euclidean__axioms.Point => (euclidean__defs.Perp__at A L0 D E L0) -> ((euclidean__axioms.Col A L0 L0) -> ((euclidean__axioms.Col D E L0) -> ((euclidean__defs.Per p L0 A) -> ((euclidean__defs.Per A L0 p) -> ((~(D = L0)) -> ((euclidean__axioms.neq L0 D) -> ((euclidean__axioms.Col E D L0) -> ((euclidean__defs.Par B C L0 D) -> ((euclidean__defs.Par L0 D B C) -> ((euclidean__defs.TP B C L0 D) -> ((euclidean__defs.OS L0 D B C) -> ((euclidean__axioms.TS L0 B C A) -> ((euclidean__axioms.BetS L0 M A) -> ((euclidean__axioms.nCol B C L0) -> ((euclidean__axioms.neq L0 M) -> ((euclidean__defs.Out L0 M A) -> ((euclidean__defs.Out L0 A M) -> ((euclidean__axioms.Col E D L0) -> ((euclidean__axioms.Col D p L0) -> ((euclidean__axioms.Col p L0 D) -> ((euclidean__defs.Per D L0 A) -> ((euclidean__defs.Per D L0 M) -> ((euclidean__defs.Par L0 D C B) -> ((euclidean__defs.Par L0 D M B) -> ((euclidean__defs.Par L0 D B M) -> ((euclidean__defs.Par B M L0 D) -> ((euclidean__defs.Par B M D L0) -> ((euclidean__defs.Par D L0 B M) -> ((euclidean__defs.TP D L0 B M) -> ((euclidean__defs.OS B M D L0) -> ((euclidean__defs.Par B M L0 D) -> ((euclidean__defs.Per L0 D B) -> ((euclidean__defs.Per B D L0) -> ((euclidean__defs.Par B D L0 M) -> ((euclidean__defs.Par B D M L0) -> ((euclidean__defs.PG B M L0 D) -> ((euclidean__defs.Par M L0 B D) -> ((euclidean__defs.TP M L0 B D) -> ((euclidean__defs.OS B D M L0) -> ((euclidean__axioms.BetS A M L0) -> ((euclidean__defs.Par M B L0 D) -> ((euclidean__defs.CongA A M B M L0 D) -> ((euclidean__defs.Per M L0 D) -> (euclidean__defs.Par M E B D)))))))))))))))))))))))))))))))))))))))))))))) with (x := L).
------------------------------------------------------------------------------------------------------------intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
exact H155.

------------------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------------------ exact H29.
------------------------------------------------------------------------------------------------------------ exact H32.
------------------------------------------------------------------------------------------------------------ exact H34.
------------------------------------------------------------------------------------------------------------ exact H37.
------------------------------------------------------------------------------------------------------------ exact H38.
------------------------------------------------------------------------------------------------------------ exact H56.
------------------------------------------------------------------------------------------------------------ exact H57.
------------------------------------------------------------------------------------------------------------ exact H59.
------------------------------------------------------------------------------------------------------------ exact H60.
------------------------------------------------------------------------------------------------------------ exact H61.
------------------------------------------------------------------------------------------------------------ exact H62.
------------------------------------------------------------------------------------------------------------ exact H63.
------------------------------------------------------------------------------------------------------------ exact H67.
------------------------------------------------------------------------------------------------------------ exact H70.
------------------------------------------------------------------------------------------------------------ exact H73.
------------------------------------------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------------------------------ exact H96.
------------------------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------------------------------ exact H101.
------------------------------------------------------------------------------------------------------------ exact H102.
------------------------------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------------------------ exact H109.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D M E) as H119.
------------------------------------------------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point E (fun L0: euclidean__axioms.Point => (euclidean__defs.Perp__at A L0 D E L0) -> ((euclidean__axioms.Col A L0 L0) -> ((euclidean__axioms.Col D E L0) -> ((euclidean__defs.Per p L0 A) -> ((euclidean__defs.Per A L0 p) -> ((~(D = L0)) -> ((euclidean__axioms.neq L0 D) -> ((euclidean__axioms.Col E D L0) -> ((euclidean__defs.Par B C L0 D) -> ((euclidean__defs.Par L0 D B C) -> ((euclidean__defs.TP B C L0 D) -> ((euclidean__defs.OS L0 D B C) -> ((euclidean__axioms.TS L0 B C A) -> ((euclidean__axioms.BetS L0 M A) -> ((euclidean__axioms.nCol B C L0) -> ((euclidean__axioms.neq L0 M) -> ((euclidean__defs.Out L0 M A) -> ((euclidean__defs.Out L0 A M) -> ((euclidean__axioms.Col E D L0) -> ((euclidean__axioms.Col D p L0) -> ((euclidean__axioms.Col p L0 D) -> ((euclidean__defs.Per D L0 A) -> ((euclidean__defs.Per D L0 M) -> ((euclidean__defs.Par L0 D C B) -> ((euclidean__defs.Par L0 D M B) -> ((euclidean__defs.Par L0 D B M) -> ((euclidean__defs.Par B M L0 D) -> ((euclidean__defs.Par B M D L0) -> ((euclidean__defs.Par D L0 B M) -> ((euclidean__defs.TP D L0 B M) -> ((euclidean__defs.OS B M D L0) -> ((euclidean__defs.Par B M L0 D) -> ((euclidean__defs.Per L0 D B) -> ((euclidean__defs.Per B D L0) -> ((euclidean__defs.Par B D L0 M) -> ((euclidean__defs.Par B D M L0) -> ((euclidean__defs.PG B M L0 D) -> ((euclidean__defs.Par M L0 B D) -> ((euclidean__defs.TP M L0 B D) -> ((euclidean__defs.OS B D M L0) -> ((euclidean__axioms.BetS A M L0) -> ((euclidean__defs.Par M B L0 D) -> ((euclidean__defs.CongA A M B M L0 D) -> ((euclidean__defs.Per M L0 D) -> (euclidean__defs.Par B D M E)))))))))))))))))))))))))))))))))))))))))))))) with (x := L).
-------------------------------------------------------------------------------------------------------------intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
exact H154.

------------------------------------------------------------------------------------------------------------- exact H115.
------------------------------------------------------------------------------------------------------------- exact H29.
------------------------------------------------------------------------------------------------------------- exact H32.
------------------------------------------------------------------------------------------------------------- exact H34.
------------------------------------------------------------------------------------------------------------- exact H37.
------------------------------------------------------------------------------------------------------------- exact H38.
------------------------------------------------------------------------------------------------------------- exact H56.
------------------------------------------------------------------------------------------------------------- exact H57.
------------------------------------------------------------------------------------------------------------- exact H59.
------------------------------------------------------------------------------------------------------------- exact H60.
------------------------------------------------------------------------------------------------------------- exact H61.
------------------------------------------------------------------------------------------------------------- exact H62.
------------------------------------------------------------------------------------------------------------- exact H63.
------------------------------------------------------------------------------------------------------------- exact H67.
------------------------------------------------------------------------------------------------------------- exact H70.
------------------------------------------------------------------------------------------------------------- exact H73.
------------------------------------------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------------------------------------------- exact H77.
------------------------------------------------------------------------------------------------------------- exact H78.
------------------------------------------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------------------------------------------- exact H83.
------------------------------------------------------------------------------------------------------------- exact H84.
------------------------------------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------------------------------------- exact H88.
------------------------------------------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------------------------------------------- exact H91.
------------------------------------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------------------------------------- exact H93.
------------------------------------------------------------------------------------------------------------- exact H94.
------------------------------------------------------------------------------------------------------------- exact H95.
------------------------------------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------------------------------------- exact H100.
------------------------------------------------------------------------------------------------------------- exact H101.
------------------------------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------------------------------------- exact H104.
------------------------------------------------------------------------------------------------------------- exact H105.
------------------------------------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------------------------------------- exact H107.
------------------------------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par B D C E) as H120.
------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun L0: euclidean__axioms.Point => (euclidean__defs.Perp__at A L0 D E L0) -> ((euclidean__axioms.Col A L0 L0) -> ((euclidean__axioms.Col D E L0) -> ((euclidean__defs.Per p L0 A) -> ((euclidean__defs.Per A L0 p) -> ((~(D = L0)) -> ((euclidean__axioms.neq L0 D) -> ((euclidean__axioms.Col E D L0) -> ((euclidean__defs.Par B C L0 D) -> ((euclidean__defs.Par L0 D B C) -> ((euclidean__defs.TP B C L0 D) -> ((euclidean__defs.OS L0 D B C) -> ((euclidean__axioms.TS L0 B C A) -> ((euclidean__axioms.BetS L0 M A) -> ((euclidean__axioms.nCol B C L0) -> ((euclidean__axioms.neq L0 M) -> ((euclidean__defs.Out L0 M A) -> ((euclidean__defs.Out L0 A M) -> ((euclidean__axioms.Col E D L0) -> ((euclidean__axioms.Col D p L0) -> ((euclidean__axioms.Col p L0 D) -> ((euclidean__defs.Per D L0 A) -> ((euclidean__defs.Per D L0 M) -> ((euclidean__defs.Par L0 D C B) -> ((euclidean__defs.Par L0 D M B) -> ((euclidean__defs.Par L0 D B M) -> ((euclidean__defs.Par B M L0 D) -> ((euclidean__defs.Par B M D L0) -> ((euclidean__defs.Par D L0 B M) -> ((euclidean__defs.TP D L0 B M) -> ((euclidean__defs.OS B M D L0) -> ((euclidean__defs.Par B M L0 D) -> ((euclidean__defs.Per L0 D B) -> ((euclidean__defs.Per B D L0) -> ((euclidean__defs.Par B D L0 M) -> ((euclidean__defs.Par B D M L0) -> ((euclidean__defs.PG B M L0 D) -> ((euclidean__defs.Par M L0 B D) -> ((euclidean__defs.TP M L0 B D) -> ((euclidean__defs.OS B D M L0) -> ((euclidean__axioms.BetS A M L0) -> ((euclidean__defs.Par M B L0 D) -> ((euclidean__defs.CongA A M B M L0 D) -> ((euclidean__defs.Per M L0 D) -> (euclidean__defs.Par B D C E)))))))))))))))))))))))))))))))))))))))))))))) with (x := L).
--------------------------------------------------------------------------------------------------------------intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
exact H116.

-------------------------------------------------------------------------------------------------------------- exact H115.
-------------------------------------------------------------------------------------------------------------- exact H29.
-------------------------------------------------------------------------------------------------------------- exact H32.
-------------------------------------------------------------------------------------------------------------- exact H34.
-------------------------------------------------------------------------------------------------------------- exact H37.
-------------------------------------------------------------------------------------------------------------- exact H38.
-------------------------------------------------------------------------------------------------------------- exact H56.
-------------------------------------------------------------------------------------------------------------- exact H57.
-------------------------------------------------------------------------------------------------------------- exact H59.
-------------------------------------------------------------------------------------------------------------- exact H60.
-------------------------------------------------------------------------------------------------------------- exact H61.
-------------------------------------------------------------------------------------------------------------- exact H62.
-------------------------------------------------------------------------------------------------------------- exact H63.
-------------------------------------------------------------------------------------------------------------- exact H67.
-------------------------------------------------------------------------------------------------------------- exact H70.
-------------------------------------------------------------------------------------------------------------- exact H73.
-------------------------------------------------------------------------------------------------------------- exact H76.
-------------------------------------------------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------------------------------------------- exact H81.
-------------------------------------------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------------------------------------------- exact H83.
-------------------------------------------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------------------------------------------- exact H90.
-------------------------------------------------------------------------------------------------------------- exact H91.
-------------------------------------------------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------------------------------------------------- exact H93.
-------------------------------------------------------------------------------------------------------------- exact H94.
-------------------------------------------------------------------------------------------------------------- exact H95.
-------------------------------------------------------------------------------------------------------------- exact H96.
-------------------------------------------------------------------------------------------------------------- exact H97.
-------------------------------------------------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------------------------------------------- exact H102.
-------------------------------------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------------------------- exact H105.
-------------------------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------------------------- exact H107.
-------------------------------------------------------------------------------------------------------------- exact H108.
-------------------------------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D E C) as H121.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par D B C E) /\ ((euclidean__defs.Par B D E C) /\ (euclidean__defs.Par D B E C))) as H121.
--------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (D) (C) (E) H120).
--------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par D B C E) /\ ((euclidean__defs.Par B D E C) /\ (euclidean__defs.Par D B E C))) as H122.
---------------------------------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__defs.Par B D E C) /\ (euclidean__defs.Par D B E C)) as H124.
----------------------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
exact H124.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D E M) as H122.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par D B M E) /\ ((euclidean__defs.Par B D E M) /\ (euclidean__defs.Par D B E M))) as H122.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (D) (M) (E) H119).
---------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par D B M E) /\ ((euclidean__defs.Par B D E M) /\ (euclidean__defs.Par D B E M))) as H123.
----------------------------------------------------------------------------------------------------------------- exact H122.
----------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__defs.Par B D E M) /\ (euclidean__defs.Par D B E M)) as H125.
------------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------------ destruct H125 as [H125 H126].
exact H125.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C M) as H123.
---------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (E) (C) (M)).
-----------------------------------------------------------------------------------------------------------------intro H123.
apply (@euclidean__tactics.Col__nCol__False (E) (C) (M) (H123)).
------------------------------------------------------------------------------------------------------------------apply (@lemma__Playfair.lemma__Playfair (B) (D) (E) (C) (M) (H121) H122).


---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M C E) as H124.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C E M) /\ ((euclidean__axioms.Col C M E) /\ ((euclidean__axioms.Col M E C) /\ ((euclidean__axioms.Col E M C) /\ (euclidean__axioms.Col M C E))))) as H124.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (E) (C) (M) H123).
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col C E M) /\ ((euclidean__axioms.Col C M E) /\ ((euclidean__axioms.Col M E C) /\ ((euclidean__axioms.Col E M C) /\ (euclidean__axioms.Col M C E))))) as H125.
------------------------------------------------------------------------------------------------------------------- exact H124.
------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col C M E) /\ ((euclidean__axioms.Col M E C) /\ ((euclidean__axioms.Col E M C) /\ (euclidean__axioms.Col M C E)))) as H127.
-------------------------------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col M E C) /\ ((euclidean__axioms.Col E M C) /\ (euclidean__axioms.Col M C E))) as H129.
--------------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col E M C) /\ (euclidean__axioms.Col M C E)) as H131.
---------------------------------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
exact H132.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M C B) as H125.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B C M) /\ ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))))) as H125.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (M) H89).
------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C M) /\ ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))))) as H126.
-------------------------------------------------------------------------------------------------------------------- exact H125.
-------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C)))) as H128.
--------------------------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))) as H130.
---------------------------------------------------------------------------------------------------------------------- exact H129.
---------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C)) as H132.
----------------------------------------------------------------------------------------------------------------------- exact H131.
----------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
exact H130.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C E B) as H126.
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (C) (E) (B)).
--------------------------------------------------------------------------------------------------------------------intro H126.
apply (@euclidean__tactics.Col__nCol__False (C) (E) (B) (H126)).
---------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (M) (C) (E) (B) (H124) (H125) H114).


------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C E) as H127.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B C E) /\ ((euclidean__axioms.Col C B E) /\ (euclidean__axioms.Col B E C))))) as H127.
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (E) (B) H126).
--------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B C E) /\ ((euclidean__axioms.Col C B E) /\ (euclidean__axioms.Col B E C))))) as H128.
---------------------------------------------------------------------------------------------------------------------- exact H127.
---------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B C E) /\ ((euclidean__axioms.Col C B E) /\ (euclidean__axioms.Col B E C)))) as H130.
----------------------------------------------------------------------------------------------------------------------- exact H129.
----------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Col B C E) /\ ((euclidean__axioms.Col C B E) /\ (euclidean__axioms.Col B E C))) as H132.
------------------------------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------------------------------ destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ (euclidean__axioms.Col B E C)) as H134.
------------------------------------------------------------------------------------------------------------------------- exact H133.
------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
exact H132.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C E) as H128.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol B C E) /\ ((euclidean__axioms.nCol D C E) /\ (euclidean__axioms.nCol B D E)))) as H128.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC (B) (D) (C) (E) H120).
---------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol B C E) /\ ((euclidean__axioms.nCol D C E) /\ (euclidean__axioms.nCol B D E)))) as H129.
----------------------------------------------------------------------------------------------------------------------- exact H128.
----------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.nCol B C E) /\ ((euclidean__axioms.nCol D C E) /\ (euclidean__axioms.nCol B D E))) as H131.
------------------------------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------------------------------ destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.nCol D C E) /\ (euclidean__axioms.nCol B D E)) as H133.
------------------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
exact H131.
--------------------------------------------------------------------------------------------------------------------- apply (@H27).
----------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (D) (E) (A)).
-----------------------------------------------------------------------------------------------------------------------intro H129.
apply (@euclidean__tactics.Col__nCol__False (B) (C) (E) (H128) H127).


-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B M L D) as H116.
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par B M L D) /\ (euclidean__defs.Par B D M L)) as H116.
---------------------------------------------------------------------------------------------------------- exact H102.
---------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__defs.Par B C E D) /\ (euclidean__defs.Par B D C E)) as H118.
----------------------------------------------------------------------------------------------------------- exact H23.
----------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
exact H116.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B M D L) as H117.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par M B L D) /\ ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L))) as H117.
----------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (B) (M) (L) (D) H116).
----------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par M B L D) /\ ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L))) as H118.
------------------------------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------------------------------ destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L)) as H120.
------------------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
exact H120.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D L E) as H118.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D E L) /\ ((euclidean__axioms.Col D L E) /\ ((euclidean__axioms.Col L E D) /\ ((euclidean__axioms.Col E L D) /\ (euclidean__axioms.Col L D E))))) as H118.
------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (E) (D) (L) H81).
------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col D E L) /\ ((euclidean__axioms.Col D L E) /\ ((euclidean__axioms.Col L E D) /\ ((euclidean__axioms.Col E L D) /\ (euclidean__axioms.Col L D E))))) as H119.
------------------------------------------------------------------------------------------------------------- exact H118.
------------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
assert (* AndElim *) ((euclidean__axioms.Col D L E) /\ ((euclidean__axioms.Col L E D) /\ ((euclidean__axioms.Col E L D) /\ (euclidean__axioms.Col L D E)))) as H121.
-------------------------------------------------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col L E D) /\ ((euclidean__axioms.Col E L D) /\ (euclidean__axioms.Col L D E))) as H123.
--------------------------------------------------------------------------------------------------------------- exact H122.
--------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col E L D) /\ (euclidean__axioms.Col L D E)) as H125.
---------------------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
exact H121.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E L) as H119.
------------------------------------------------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (L) (E) H115).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par B M E L) as H120.
------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (B) (M) (E) (D) (L) (H117) (H118) H119).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E L B M) as H121.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (B) (M) (E) (L) H120).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B M C) as H122.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C M) /\ ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))))) as H122.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (M) H89).
---------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B C M) /\ ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))))) as H123.
----------------------------------------------------------------------------------------------------------------- exact H122.
----------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C)))) as H125.
------------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------------ destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))) as H127.
------------------------------------------------------------------------------------------------------------------- exact H126.
------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C)) as H129.
-------------------------------------------------------------------------------------------------------------------- exact H128.
-------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
exact H125.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C M) as H123.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (M) (C) H114).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E L C M) as H124.
----------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel (E) (L) (C) (B) (M) (H121) (H122) H123).
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C M E L) as H125.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (E) (L) (C) (M) H124).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par M C E L) as H126.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par M C E L) /\ ((euclidean__defs.Par C M L E) /\ (euclidean__defs.Par M C L E))) as H126.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (C) (M) (E) (L) H125).
-------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par M C E L) /\ ((euclidean__defs.Par C M L E) /\ (euclidean__defs.Par M C L E))) as H127.
--------------------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__defs.Par C M L E) /\ (euclidean__defs.Par M C L E)) as H129.
---------------------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
exact H127.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D L E) as H127.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H127.
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (M) (C) H122).
--------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H128.
---------------------------------------------------------------------------------------------------------------------- exact H127.
---------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B)))) as H130.
----------------------------------------------------------------------------------------------------------------------- exact H129.
----------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))) as H132.
------------------------------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------------------------------ destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B)) as H134.
------------------------------------------------------------------------------------------------------------------------- exact H133.
------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
exact H118.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E L M) as H128.
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (D) (L) (E) (M) (H85) (H127) H119).
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per M L E) as H129.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (E) (L) (M) H128).
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per C E D) as H130.
----------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B C E D) /\ ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))))) as H130.
------------------------------------------------------------------------------------------------------------------------ exact H1.
------------------------------------------------------------------------------------------------------------------------ destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Cong B C C E) /\ ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))))) as H132.
------------------------------------------------------------------------------------------------------------------------- exact H131.
------------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.Cong B C D B) /\ ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))))) as H134.
-------------------------------------------------------------------------------------------------------------------------- exact H133.
-------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__defs.Per D B C) /\ ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)))) as H136.
--------------------------------------------------------------------------------------------------------------------------- exact H135.
--------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__defs.Per B C E) /\ ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B))) as H138.
---------------------------------------------------------------------------------------------------------------------------- exact H137.
---------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__defs.Per C E D) /\ (euclidean__defs.Per E D B)) as H140.
----------------------------------------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
exact H140.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per D E C) as H131.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__8__2.lemma__8__2 (C) (E) (D) H130).
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Per L E C) as H132.
------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright (D) (E) (L) (C) (H131) (H34) H115).
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M C L E) as H133.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par C M E L) /\ ((euclidean__defs.Par M C L E) /\ (euclidean__defs.Par C M L E))) as H133.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (M) (C) (E) (L) H126).
--------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par C M E L) /\ ((euclidean__defs.Par M C L E) /\ (euclidean__defs.Par C M L E))) as H134.
---------------------------------------------------------------------------------------------------------------------------- exact H133.
---------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__defs.Par M C L E) /\ (euclidean__defs.Par C M L E)) as H136.
----------------------------------------------------------------------------------------------------------------------------- exact H135.
----------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
exact H136.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par L E M C) as H134.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (M) (C) (L) (E) H133).
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP L E M C) as H135.
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B (L) (E) (M) (C) H134).
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS M C L E) as H136.
----------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq L E) /\ ((euclidean__axioms.neq M C) /\ ((~(euclidean__defs.Meet L E M C)) /\ (euclidean__defs.OS M C L E)))) as H136.
------------------------------------------------------------------------------------------------------------------------------ exact H135.
------------------------------------------------------------------------------------------------------------------------------ destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.neq M C) /\ ((~(euclidean__defs.Meet L E M C)) /\ (euclidean__defs.OS M C L E))) as H138.
------------------------------------------------------------------------------------------------------------------------------- exact H137.
------------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((~(euclidean__defs.Meet L E M C)) /\ (euclidean__defs.OS M C L E)) as H140.
-------------------------------------------------------------------------------------------------------------------------------- exact H139.
-------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq B D) /\ ((~(euclidean__defs.Meet M L B D)) /\ (euclidean__defs.OS B D M L)))) as H142.
--------------------------------------------------------------------------------------------------------------------------------- exact H104.
--------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((~(euclidean__defs.Meet M L B D)) /\ (euclidean__defs.OS B D M L))) as H144.
---------------------------------------------------------------------------------------------------------------------------------- exact H143.
---------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((~(euclidean__defs.Meet M L B D)) /\ (euclidean__defs.OS B D M L)) as H146.
----------------------------------------------------------------------------------------------------------------------------------- exact H145.
----------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.neq B M) /\ ((~(euclidean__defs.Meet D L B M)) /\ (euclidean__defs.OS B M D L)))) as H148.
------------------------------------------------------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------------------------------------------------------ destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.neq B M) /\ ((~(euclidean__defs.Meet D L B M)) /\ (euclidean__defs.OS B M D L))) as H150.
------------------------------------------------------------------------------------------------------------------------------------- exact H149.
------------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* AndElim *) ((~(euclidean__defs.Meet D L B M)) /\ (euclidean__defs.OS B M D L)) as H152.
-------------------------------------------------------------------------------------------------------------------------------------- exact H151.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H152 H153].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq L D) /\ ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C)))) as H154.
--------------------------------------------------------------------------------------------------------------------------------------- exact H62.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.neq L D) /\ ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C))) as H156.
---------------------------------------------------------------------------------------------------------------------------------------- exact H155.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((~(euclidean__defs.Meet B C L D)) /\ (euclidean__defs.OS L D B C)) as H158.
----------------------------------------------------------------------------------------------------------------------------------------- exact H157.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq B N) /\ ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E)))) as H160.
------------------------------------------------------------------------------------------------------------------------------------------ exact H47.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H160 as [H160 H161].
assert (* AndElim *) ((euclidean__axioms.neq B N) /\ ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E))) as H162.
------------------------------------------------------------------------------------------------------------------------------------------- exact H161.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H162 H163].
assert (* AndElim *) ((~(euclidean__defs.Meet D E B N)) /\ (euclidean__defs.OS B N D E)) as H164.
-------------------------------------------------------------------------------------------------------------------------------------------- exact H163.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H164 as [H164 H165].
exact H141.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M L E C) as H137.
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__twoperpsparallel.lemma__twoperpsparallel (M) (L) (E) (C) (H129) (H132) H136).
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par M L C E) as H138.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par L M E C) /\ ((euclidean__defs.Par M L C E) /\ (euclidean__defs.Par L M C E))) as H138.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip (M) (L) (E) (C) H137).
-------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__defs.Par L M E C) /\ ((euclidean__defs.Par M L C E) /\ (euclidean__defs.Par L M C E))) as H139.
--------------------------------------------------------------------------------------------------------------------------------- exact H138.
--------------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__defs.Par M L C E) /\ (euclidean__defs.Par L M C E)) as H141.
---------------------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
exact H141.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG M C E L) as H139.
-------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------------------------------- exact H138.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B M D L) as H140.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B D M L) /\ ((euclidean__axioms.Cong B M D L) /\ ((euclidean__defs.CongA M B D D L M) /\ ((euclidean__defs.CongA B D L L M B) /\ (euclidean__axioms.Cong__3 M B D D L M))))) as H140.
---------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__34.proposition__34 (B) (D) (M) (L) H102).
---------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B D M L) /\ ((euclidean__axioms.Cong B M D L) /\ ((euclidean__defs.CongA M B D D L M) /\ ((euclidean__defs.CongA B D L L M B) /\ (euclidean__axioms.Cong__3 M B D D L M))))) as H141.
----------------------------------------------------------------------------------------------------------------------------------- exact H140.
----------------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
assert (* AndElim *) ((euclidean__axioms.Cong B M D L) /\ ((euclidean__defs.CongA M B D D L M) /\ ((euclidean__defs.CongA B D L L M B) /\ (euclidean__axioms.Cong__3 M B D D L M)))) as H143.
------------------------------------------------------------------------------------------------------------------------------------ exact H142.
------------------------------------------------------------------------------------------------------------------------------------ destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__defs.CongA M B D D L M) /\ ((euclidean__defs.CongA B D L L M B) /\ (euclidean__axioms.Cong__3 M B D D L M))) as H145.
------------------------------------------------------------------------------------------------------------------------------------- exact H144.
------------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__defs.CongA B D L L M B) /\ (euclidean__axioms.Cong__3 M B D D L M)) as H147.
-------------------------------------------------------------------------------------------------------------------------------------- exact H146.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
exact H143.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M C L E) as H141.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M L C E) /\ ((euclidean__axioms.Cong M C L E) /\ ((euclidean__defs.CongA C M L L E C) /\ ((euclidean__defs.CongA M L E E C M) /\ (euclidean__axioms.Cong__3 C M L L E C))))) as H141.
----------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__34.proposition__34 (M) (L) (C) (E) H139).
----------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong M L C E) /\ ((euclidean__axioms.Cong M C L E) /\ ((euclidean__defs.CongA C M L L E C) /\ ((euclidean__defs.CongA M L E E C M) /\ (euclidean__axioms.Cong__3 C M L L E C))))) as H142.
------------------------------------------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------------------------------------------ destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.Cong M C L E) /\ ((euclidean__defs.CongA C M L L E C) /\ ((euclidean__defs.CongA M L E E C M) /\ (euclidean__axioms.Cong__3 C M L L E C)))) as H144.
------------------------------------------------------------------------------------------------------------------------------------- exact H143.
------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__defs.CongA C M L L E C) /\ ((euclidean__defs.CongA M L E E C M) /\ (euclidean__axioms.Cong__3 C M L L E C))) as H146.
-------------------------------------------------------------------------------------------------------------------------------------- exact H145.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__defs.CongA M L E E C M) /\ (euclidean__axioms.Cong__3 C M L L E C)) as H148.
--------------------------------------------------------------------------------------------------------------------------------------- exact H147.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
exact H144.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C D E) as H142.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B D C E) /\ ((euclidean__axioms.Cong B C D E) /\ ((euclidean__defs.CongA C B D D E C) /\ ((euclidean__defs.CongA B D E E C B) /\ (euclidean__axioms.Cong__3 C B D D E C))))) as H142.
------------------------------------------------------------------------------------------------------------------------------------ apply (@proposition__34.proposition__34 (B) (D) (C) (E) H23).
------------------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong B D C E) /\ ((euclidean__axioms.Cong B C D E) /\ ((euclidean__defs.CongA C B D D E C) /\ ((euclidean__defs.CongA B D E E C B) /\ (euclidean__axioms.Cong__3 C B D D E C))))) as H143.
------------------------------------------------------------------------------------------------------------------------------------- exact H142.
------------------------------------------------------------------------------------------------------------------------------------- destruct H143 as [H143 H144].
assert (* AndElim *) ((euclidean__axioms.Cong B C D E) /\ ((euclidean__defs.CongA C B D D E C) /\ ((euclidean__defs.CongA B D E E C B) /\ (euclidean__axioms.Cong__3 C B D D E C)))) as H145.
-------------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__defs.CongA C B D D E C) /\ ((euclidean__defs.CongA B D E E C B) /\ (euclidean__axioms.Cong__3 C B D D E C))) as H147.
--------------------------------------------------------------------------------------------------------------------------------------- exact H146.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
assert (* AndElim *) ((euclidean__defs.CongA B D E E C B) /\ (euclidean__axioms.Cong__3 C B D D E C)) as H149.
---------------------------------------------------------------------------------------------------------------------------------------- exact H148.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H149 as [H149 H150].
exact H145.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D L E) as H143.
------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__betweennesspreserved.lemma__betweennesspreserved (B) (M) (C) (D) (L) (E) (H140) (H142) (H141) H113).
------------------------------------------------------------------------------------------------------------------------------------ exists M.
exists L.
split.
------------------------------------------------------------------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------------- exact H113.
-------------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------------- exact H139.
--------------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------------- exact H143.
---------------------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------------------- exact H70.
----------------------------------------------------------------------------------------------------------------------------------------- exact H84.
Qed.
