Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__collinearparallel : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point), (euclidean__defs.Par A B c d) -> ((euclidean__axioms.Col c d C) -> ((euclidean__axioms.neq C d) -> (euclidean__defs.Par A B C d))).
Proof.
intro A.
intro B.
intro C.
intro c.
intro d.
intro H.
intro H0.
intro H1.
assert (* Cut *) (exists (R: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (p: euclidean__axioms.Point) (q: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b))))))))))) as H2.
- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col c d u) /\ ((euclidean__axioms.Col c d v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H2.
-- exact H.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col c d u) /\ ((euclidean__axioms.Col c d v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
--- exact H2.
--- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col c d u) /\ ((euclidean__axioms.Col c d v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H3.
---- exact __TmpHyp.
---- destruct H3 as [x H3].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col c d u) /\ ((euclidean__axioms.Col c d v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H4.
----- exact H3.
----- destruct H4 as [x0 H4].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col c d u) /\ ((euclidean__axioms.Col c d v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H5.
------ exact H4.
------ destruct H5 as [x1 H5].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col c d x1) /\ ((euclidean__axioms.Col c d v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H6.
------- exact H5.
------- destruct H6 as [x2 H6].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col c d x1) /\ ((euclidean__axioms.Col c d x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H7.
-------- exact H6.
-------- destruct H7 as [x3 H7].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col c d x1) /\ ((euclidean__axioms.Col c d x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col c d x1) /\ ((euclidean__axioms.Col c d x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col c d x1) /\ ((euclidean__axioms.Col c d x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col c d x1) /\ ((euclidean__axioms.Col c d x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col c d x1) /\ ((euclidean__axioms.Col c d x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col c d x1) /\ ((euclidean__axioms.Col c d x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H18.
-------------- exact H17.
-------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col c d x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H20.
--------------- exact H19.
--------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H22.
---------------- exact H21.
---------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H24.
----------------- exact H23.
----------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H26.
------------------ exact H25.
------------------ destruct H26 as [H26 H27].
exists x3.
exists x.
exists x0.
exists x1.
exists x2.
split.
------------------- exact H8.
------------------- split.
-------------------- exact H10.
-------------------- split.
--------------------- exact H12.
--------------------- split.
---------------------- exact H14.
---------------------- split.
----------------------- exact H16.
----------------------- split.
------------------------ exact H18.
------------------------ split.
------------------------- exact H20.
------------------------- split.
-------------------------- exact H22.
-------------------------- split.
--------------------------- exact H24.
--------------------------- split.
---------------------------- exact H26.
---------------------------- exact H27.
- assert (exists R: euclidean__axioms.Point, (exists (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (p: euclidean__axioms.Point) (q: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b)))))))))))) as H3.
-- exact H2.
-- destruct H3 as [R H3].
assert (exists a: euclidean__axioms.Point, (exists (b: euclidean__axioms.Point) (p: euclidean__axioms.Point) (q: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b)))))))))))) as H4.
--- exact H3.
--- destruct H4 as [a H4].
assert (exists b: euclidean__axioms.Point, (exists (p: euclidean__axioms.Point) (q: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b)))))))))))) as H5.
---- exact H4.
---- destruct H5 as [b H5].
assert (exists p: euclidean__axioms.Point, (exists (q: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b)))))))))))) as H6.
----- exact H5.
----- destruct H6 as [p H6].
assert (exists q: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b)))))))))))) as H7.
------ exact H6.
------ destruct H7 as [q H7].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b))))))))))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b)))))))))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b))))))))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b)))))))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b))))))) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b)))))) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b))))) as H20.
------------- exact H19.
------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b)))) as H22.
-------------- exact H21.
-------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b))) as H24.
--------------- exact H23.
--------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b)) as H26.
---------------- exact H25.
---------------- destruct H26 as [H26 H27].
assert (* Cut *) (euclidean__axioms.neq d C) as H28.
----------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (d) H1).
----------------- assert (* Cut *) (euclidean__axioms.Col d C p) as H29.
------------------ apply (@euclidean__tactics.not__nCol__Col (d) (C) (p)).
-------------------intro H29.
apply (@euclidean__tactics.Col__nCol__False (d) (C) (p) (H29)).
--------------------apply (@lemma__collinear4.lemma__collinear4 (c) (d) (C) (p) (H0) (H18) H10).


------------------ assert (* Cut *) (euclidean__axioms.Col C d p) as H30.
------------------- assert (* Cut *) ((euclidean__axioms.Col C d p) /\ ((euclidean__axioms.Col C p d) /\ ((euclidean__axioms.Col p d C) /\ ((euclidean__axioms.Col d p C) /\ (euclidean__axioms.Col p C d))))) as H30.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder (d) (C) (p) H29).
-------------------- assert (* AndElim *) ((euclidean__axioms.Col C d p) /\ ((euclidean__axioms.Col C p d) /\ ((euclidean__axioms.Col p d C) /\ ((euclidean__axioms.Col d p C) /\ (euclidean__axioms.Col p C d))))) as H31.
--------------------- exact H30.
--------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col C p d) /\ ((euclidean__axioms.Col p d C) /\ ((euclidean__axioms.Col d p C) /\ (euclidean__axioms.Col p C d)))) as H33.
---------------------- exact H32.
---------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col p d C) /\ ((euclidean__axioms.Col d p C) /\ (euclidean__axioms.Col p C d))) as H35.
----------------------- exact H34.
----------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col d p C) /\ (euclidean__axioms.Col p C d)) as H37.
------------------------ exact H36.
------------------------ destruct H37 as [H37 H38].
exact H31.
------------------- assert (* Cut *) (euclidean__axioms.Col d C q) as H31.
-------------------- apply (@euclidean__tactics.not__nCol__Col (d) (C) (q)).
---------------------intro H31.
apply (@euclidean__tactics.Col__nCol__False (d) (C) (q) (H31)).
----------------------apply (@lemma__collinear4.lemma__collinear4 (c) (d) (C) (q) (H0) (H20) H10).


-------------------- assert (* Cut *) (euclidean__axioms.Col C d q) as H32.
--------------------- assert (* Cut *) ((euclidean__axioms.Col C d q) /\ ((euclidean__axioms.Col C q d) /\ ((euclidean__axioms.Col q d C) /\ ((euclidean__axioms.Col d q C) /\ (euclidean__axioms.Col q C d))))) as H32.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (d) (C) (q) H31).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col C d q) /\ ((euclidean__axioms.Col C q d) /\ ((euclidean__axioms.Col q d C) /\ ((euclidean__axioms.Col d q C) /\ (euclidean__axioms.Col q C d))))) as H33.
----------------------- exact H32.
----------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col C q d) /\ ((euclidean__axioms.Col q d C) /\ ((euclidean__axioms.Col d q C) /\ (euclidean__axioms.Col q C d)))) as H35.
------------------------ exact H34.
------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col q d C) /\ ((euclidean__axioms.Col d q C) /\ (euclidean__axioms.Col q C d))) as H37.
------------------------- exact H36.
------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col d q C) /\ (euclidean__axioms.Col q C d)) as H39.
-------------------------- exact H38.
-------------------------- destruct H39 as [H39 H40].
exact H33.
--------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C d)) as H33.
---------------------- intro H33.
assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col C d E)))) as H34.
----------------------- exact H33.
----------------------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col C d E))))) as H35.
------------------------ exact H34.
------------------------ destruct H35 as [E H35].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col C d E)))) as H36.
------------------------- exact H35.
------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col C d E))) as H38.
-------------------------- exact H37.
-------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col C d E)) as H40.
--------------------------- exact H39.
--------------------------- destruct H40 as [H40 H41].
assert (* Cut *) (euclidean__axioms.Col C d c) as H42.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col d c C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C c d) /\ ((euclidean__axioms.Col c C d) /\ (euclidean__axioms.Col C d c))))) as H42.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (c) (d) (C) H0).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col d c C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C c d) /\ ((euclidean__axioms.Col c C d) /\ (euclidean__axioms.Col C d c))))) as H43.
------------------------------ exact H42.
------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C c d) /\ ((euclidean__axioms.Col c C d) /\ (euclidean__axioms.Col C d c)))) as H45.
------------------------------- exact H44.
------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col C c d) /\ ((euclidean__axioms.Col c C d) /\ (euclidean__axioms.Col C d c))) as H47.
-------------------------------- exact H46.
-------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col c C d) /\ (euclidean__axioms.Col C d c)) as H49.
--------------------------------- exact H48.
--------------------------------- destruct H49 as [H49 H50].
exact H50.
---------------------------- assert (* Cut *) (euclidean__axioms.Col d E c) as H43.
----------------------------- apply (@euclidean__tactics.not__nCol__Col (d) (E) (c)).
------------------------------intro H43.
apply (@euclidean__tactics.Col__nCol__False (d) (E) (c) (H43)).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (d) (E) (c) (H41) (H42) H38).


----------------------------- assert (* Cut *) (euclidean__axioms.Col c d E) as H44.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col E d c) /\ ((euclidean__axioms.Col E c d) /\ ((euclidean__axioms.Col c d E) /\ ((euclidean__axioms.Col d c E) /\ (euclidean__axioms.Col c E d))))) as H44.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (d) (E) (c) H43).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E d c) /\ ((euclidean__axioms.Col E c d) /\ ((euclidean__axioms.Col c d E) /\ ((euclidean__axioms.Col d c E) /\ (euclidean__axioms.Col c E d))))) as H45.
-------------------------------- exact H44.
-------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col E c d) /\ ((euclidean__axioms.Col c d E) /\ ((euclidean__axioms.Col d c E) /\ (euclidean__axioms.Col c E d)))) as H47.
--------------------------------- exact H46.
--------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col c d E) /\ ((euclidean__axioms.Col d c E) /\ (euclidean__axioms.Col c E d))) as H49.
---------------------------------- exact H48.
---------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col d c E) /\ (euclidean__axioms.Col c E d)) as H51.
----------------------------------- exact H50.
----------------------------------- destruct H51 as [H51 H52].
exact H49.
------------------------------ assert (* Cut *) (euclidean__defs.Meet A B c d) as H45.
------------------------------- exists E.
split.
-------------------------------- exact H36.
-------------------------------- split.
--------------------------------- exact H10.
--------------------------------- split.
---------------------------------- exact H40.
---------------------------------- exact H44.
------------------------------- apply (@H24 H45).
---------------------- assert (* Cut *) (euclidean__defs.Par A B C d) as H34.
----------------------- exists a.
exists b.
exists p.
exists q.
exists R.
split.
------------------------ exact H8.
------------------------ split.
------------------------- exact H1.
------------------------- split.
-------------------------- exact H12.
-------------------------- split.
--------------------------- exact H14.
--------------------------- split.
---------------------------- exact H16.
---------------------------- split.
----------------------------- exact H30.
----------------------------- split.
------------------------------ exact H32.
------------------------------ split.
------------------------------- exact H22.
------------------------------- split.
-------------------------------- exact H33.
-------------------------------- split.
--------------------------------- exact H26.
--------------------------------- exact H27.
----------------------- exact H34.
Qed.
