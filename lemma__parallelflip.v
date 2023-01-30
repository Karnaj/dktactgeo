Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__parallelflip : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.Par A B C D) -> ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (exists (M: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b))))))))))) as H0.
- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H0.
-- exact H.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
--- exact H0.
--- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H1.
---- exact __TmpHyp.
---- destruct H1 as [x H1].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H2.
----- exact H1.
----- destruct H2 as [x0 H2].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H3.
------ exact H2.
------ destruct H3 as [x1 H3].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H4.
------- exact H3.
------- destruct H4 as [x2 H4].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H5.
-------- exact H4.
-------- destruct H5 as [x3 H5].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H6.
--------- exact H5.
--------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H8.
---------- exact H7.
---------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col A B x) /\ ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H10.
----------- exact H9.
----------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col C D x1) /\ ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col C D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
exists x3.
exists x.
exists x0.
exists x1.
exists x2.
split.
------------------- exact H6.
------------------- split.
-------------------- exact H8.
-------------------- split.
--------------------- exact H10.
--------------------- split.
---------------------- exact H12.
---------------------- split.
----------------------- exact H14.
----------------------- split.
------------------------ exact H16.
------------------------ split.
------------------------- exact H18.
------------------------- split.
-------------------------- exact H20.
-------------------------- split.
--------------------------- exact H22.
--------------------------- split.
---------------------------- exact H24.
---------------------------- exact H25.
- assert (exists M: euclidean__axioms.Point, (exists (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b)))))))))))) as H1.
-- exact H0.
-- destruct H1 as [M H1].
assert (exists a: euclidean__axioms.Point, (exists (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b)))))))))))) as H2.
--- exact H1.
--- destruct H2 as [a H2].
assert (exists b: euclidean__axioms.Point, (exists (c: euclidean__axioms.Point) (d: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b)))))))))))) as H3.
---- exact H2.
---- destruct H3 as [b H3].
assert (exists c: euclidean__axioms.Point, (exists (d: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b)))))))))))) as H4.
----- exact H3.
----- destruct H4 as [c H4].
assert (exists d: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b)))))))))))) as H5.
------ exact H4.
------ destruct H5 as [d H5].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b))))))))))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b)))))))))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b))))))))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b)))))))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b))))))) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b)))))) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b))))) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b)))) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b))) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b)) as H24.
---------------- exact H23.
---------------- destruct H24 as [H24 H25].
assert (* Cut *) (euclidean__axioms.Col B A a) as H26.
----------------- assert (* Cut *) ((euclidean__axioms.Col B A a) /\ ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A))))) as H26.
------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (a) H10).
------------------ assert (* AndElim *) ((euclidean__axioms.Col B A a) /\ ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A))))) as H27.
------------------- exact H26.
------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A)))) as H29.
-------------------- exact H28.
-------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A))) as H31.
--------------------- exact H30.
--------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A)) as H33.
---------------------- exact H32.
---------------------- destruct H33 as [H33 H34].
exact H27.
----------------- assert (* Cut *) (euclidean__axioms.Col B A b) as H27.
------------------ assert (* Cut *) ((euclidean__axioms.Col B A b) /\ ((euclidean__axioms.Col B b A) /\ ((euclidean__axioms.Col b A B) /\ ((euclidean__axioms.Col A b B) /\ (euclidean__axioms.Col b B A))))) as H27.
------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (b) H12).
------------------- assert (* AndElim *) ((euclidean__axioms.Col B A b) /\ ((euclidean__axioms.Col B b A) /\ ((euclidean__axioms.Col b A B) /\ ((euclidean__axioms.Col A b B) /\ (euclidean__axioms.Col b B A))))) as H28.
-------------------- exact H27.
-------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col B b A) /\ ((euclidean__axioms.Col b A B) /\ ((euclidean__axioms.Col A b B) /\ (euclidean__axioms.Col b B A)))) as H30.
--------------------- exact H29.
--------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col b A B) /\ ((euclidean__axioms.Col A b B) /\ (euclidean__axioms.Col b B A))) as H32.
---------------------- exact H31.
---------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col A b B) /\ (euclidean__axioms.Col b B A)) as H34.
----------------------- exact H33.
----------------------- destruct H34 as [H34 H35].
exact H28.
------------------ assert (* Cut *) (euclidean__axioms.Col D C c) as H28.
------------------- assert (* Cut *) ((euclidean__axioms.Col D C c) /\ ((euclidean__axioms.Col D c C) /\ ((euclidean__axioms.Col c C D) /\ ((euclidean__axioms.Col C c D) /\ (euclidean__axioms.Col c D C))))) as H28.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (c) H16).
-------------------- assert (* AndElim *) ((euclidean__axioms.Col D C c) /\ ((euclidean__axioms.Col D c C) /\ ((euclidean__axioms.Col c C D) /\ ((euclidean__axioms.Col C c D) /\ (euclidean__axioms.Col c D C))))) as H29.
--------------------- exact H28.
--------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col D c C) /\ ((euclidean__axioms.Col c C D) /\ ((euclidean__axioms.Col C c D) /\ (euclidean__axioms.Col c D C)))) as H31.
---------------------- exact H30.
---------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col c C D) /\ ((euclidean__axioms.Col C c D) /\ (euclidean__axioms.Col c D C))) as H33.
----------------------- exact H32.
----------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col C c D) /\ (euclidean__axioms.Col c D C)) as H35.
------------------------ exact H34.
------------------------ destruct H35 as [H35 H36].
exact H29.
------------------- assert (* Cut *) (euclidean__axioms.Col D C d) as H29.
-------------------- assert (* Cut *) ((euclidean__axioms.Col D C d) /\ ((euclidean__axioms.Col D d C) /\ ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col C d D) /\ (euclidean__axioms.Col d D C))))) as H29.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (D) (d) H18).
--------------------- assert (* AndElim *) ((euclidean__axioms.Col D C d) /\ ((euclidean__axioms.Col D d C) /\ ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col C d D) /\ (euclidean__axioms.Col d D C))))) as H30.
---------------------- exact H29.
---------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col D d C) /\ ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col C d D) /\ (euclidean__axioms.Col d D C)))) as H32.
----------------------- exact H31.
----------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col C d D) /\ (euclidean__axioms.Col d D C))) as H34.
------------------------ exact H33.
------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col C d D) /\ (euclidean__axioms.Col d D C)) as H36.
------------------------- exact H35.
------------------------- destruct H36 as [H36 H37].
exact H30.
-------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H30.
--------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H6).
--------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H31.
---------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (D) H8).
---------------------- assert (* Cut *) (euclidean__axioms.BetS d M a) as H32.
----------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (a) (M) (d) H24).
----------------------- assert (* Cut *) (euclidean__axioms.BetS b M c) as H33.
------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (c) (M) (b) H25).
------------------------ assert (* Cut *) (euclidean__axioms.neq d c) as H34.
------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (c) (d) H20).
------------------------- assert (* Cut *) (euclidean__axioms.neq b a) as H35.
-------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (a) (b) H14).
-------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B D C)) as H36.
--------------------------- intro H36.
assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col D C P)))) as H37.
---------------------------- exact H36.
---------------------------- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col D C P))))) as H38.
----------------------------- exact H37.
----------------------------- destruct H38 as [P H38].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col D C P)))) as H39.
------------------------------ exact H38.
------------------------------ destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col D C P))) as H41.
------------------------------- exact H40.
------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col D C P)) as H43.
-------------------------------- exact H42.
-------------------------------- destruct H43 as [H43 H44].
assert (* Cut *) (euclidean__axioms.Col C D P) as H45.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col C D P) /\ ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D))))) as H45.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (P) H44).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C D P) /\ ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D))))) as H46.
----------------------------------- exact H45.
----------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D)))) as H48.
------------------------------------ exact H47.
------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D))) as H50.
------------------------------------- exact H49.
------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D)) as H52.
-------------------------------------- exact H51.
-------------------------------------- destruct H52 as [H52 H53].
exact H46.
--------------------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H46.
---------------------------------- exists P.
split.
----------------------------------- exact H39.
----------------------------------- split.
------------------------------------ exact H8.
------------------------------------ split.
------------------------------------- exact H43.
------------------------------------- exact H45.
---------------------------------- apply (@H22 H46).
--------------------------- assert (* Cut *) (~(euclidean__defs.Meet B A C D)) as H37.
---------------------------- intro H37.
assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col C D P)))) as H38.
----------------------------- exact H37.
----------------------------- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col C D P))))) as H39.
------------------------------ exact H38.
------------------------------ destruct H39 as [P H39].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col C D P)))) as H40.
------------------------------- exact H39.
------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col C D P))) as H42.
-------------------------------- exact H41.
-------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col C D P)) as H44.
--------------------------------- exact H43.
--------------------------------- destruct H44 as [H44 H45].
assert (* Cut *) (euclidean__axioms.Col A B P) as H46.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))))) as H46.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (P) H44).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))))) as H47.
------------------------------------ exact H46.
------------------------------------ destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B)))) as H49.
------------------------------------- exact H48.
------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))) as H51.
-------------------------------------- exact H50.
-------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B)) as H53.
--------------------------------------- exact H52.
--------------------------------------- destruct H53 as [H53 H54].
exact H47.
---------------------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H47.
----------------------------------- exists P.
split.
------------------------------------ exact H6.
------------------------------------ split.
------------------------------------- exact H42.
------------------------------------- split.
-------------------------------------- exact H46.
-------------------------------------- exact H45.
----------------------------------- apply (@H22 H47).
---------------------------- assert (* Cut *) (~(euclidean__defs.Meet B A D C)) as H38.
----------------------------- intro H38.
assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col D C P)))) as H39.
------------------------------ exact H38.
------------------------------ assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col D C P))))) as H40.
------------------------------- exact H39.
------------------------------- destruct H40 as [P H40].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col D C P)))) as H41.
-------------------------------- exact H40.
-------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col D C P))) as H43.
--------------------------------- exact H42.
--------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col D C P)) as H45.
---------------------------------- exact H44.
---------------------------------- destruct H45 as [H45 H46].
assert (* Cut *) (euclidean__axioms.Col A B P) as H47.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))))) as H47.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (P) H45).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))))) as H48.
------------------------------------- exact H47.
------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B)))) as H50.
-------------------------------------- exact H49.
-------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))) as H52.
--------------------------------------- exact H51.
--------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B)) as H54.
---------------------------------------- exact H53.
---------------------------------------- destruct H54 as [H54 H55].
exact H48.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col C D P) as H48.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C D P) /\ ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D))))) as H48.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (P) H46).
------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C D P) /\ ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D))))) as H49.
-------------------------------------- exact H48.
-------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D)))) as H51.
--------------------------------------- exact H50.
--------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D))) as H53.
---------------------------------------- exact H52.
---------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D)) as H55.
----------------------------------------- exact H54.
----------------------------------------- destruct H55 as [H55 H56].
exact H49.
------------------------------------ assert (* Cut *) (euclidean__defs.Meet A B C D) as H49.
------------------------------------- exists P.
split.
-------------------------------------- exact H6.
-------------------------------------- split.
--------------------------------------- exact H8.
--------------------------------------- split.
---------------------------------------- exact H47.
---------------------------------------- exact H48.
------------------------------------- apply (@H22 H49).
----------------------------- assert (* Cut *) (euclidean__defs.Par B A C D) as H39.
------------------------------ exists b.
exists a.
exists d.
exists c.
exists M.
split.
------------------------------- exact H30.
------------------------------- split.
-------------------------------- exact H8.
-------------------------------- split.
--------------------------------- exact H27.
--------------------------------- split.
---------------------------------- exact H26.
---------------------------------- split.
----------------------------------- exact H35.
----------------------------------- split.
------------------------------------ exact H18.
------------------------------------ split.
------------------------------------- exact H16.
------------------------------------- split.
-------------------------------------- exact H34.
-------------------------------------- split.
--------------------------------------- exact H37.
--------------------------------------- split.
---------------------------------------- exact H33.
---------------------------------------- exact H32.
------------------------------ assert (* Cut *) (euclidean__defs.Par A B D C) as H40.
------------------------------- exists b.
exists a.
exists d.
exists c.
exists M.
split.
-------------------------------- exact H6.
-------------------------------- split.
--------------------------------- exact H31.
--------------------------------- split.
---------------------------------- exact H12.
---------------------------------- split.
----------------------------------- exact H10.
----------------------------------- split.
------------------------------------ exact H35.
------------------------------------ split.
------------------------------------- exact H29.
------------------------------------- split.
-------------------------------------- exact H28.
-------------------------------------- split.
--------------------------------------- exact H34.
--------------------------------------- split.
---------------------------------------- exact H36.
---------------------------------------- split.
----------------------------------------- exact H33.
----------------------------------------- exact H32.
------------------------------- assert (* Cut *) (euclidean__defs.Par B A D C) as H41.
-------------------------------- exists b.
exists a.
exists d.
exists c.
exists M.
split.
--------------------------------- exact H30.
--------------------------------- split.
---------------------------------- exact H31.
---------------------------------- split.
----------------------------------- exact H27.
----------------------------------- split.
------------------------------------ exact H26.
------------------------------------ split.
------------------------------------- exact H35.
------------------------------------- split.
-------------------------------------- exact H29.
-------------------------------------- split.
--------------------------------------- exact H28.
--------------------------------------- split.
---------------------------------------- exact H34.
---------------------------------------- split.
----------------------------------------- exact H38.
----------------------------------------- split.
------------------------------------------ exact H33.
------------------------------------------ exact H32.
-------------------------------- split.
--------------------------------- exact H39.
--------------------------------- split.
---------------------------------- exact H40.
---------------------------------- exact H41.
Qed.
