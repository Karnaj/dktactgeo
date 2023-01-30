Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__collinearorder.
Require Export logic.
Definition lemma__parallelNC : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.Par A B C D) -> ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))).
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
assert (* Cut *) (~(euclidean__axioms.Col A C D)) as H26.
----------------- intro H26.
assert (* Cut *) (euclidean__axioms.Col C D A) as H27.
------------------ assert (* Cut *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H27.
------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (C) (D) H26).
------------------- assert (* AndElim *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H28.
-------------------- exact H27.
-------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A)))) as H30.
--------------------- exact H29.
--------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))) as H32.
---------------------- exact H31.
---------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A)) as H34.
----------------------- exact H33.
----------------------- destruct H34 as [H34 H35].
exact H30.
------------------ assert (* Cut *) (A = A) as H28.
------------------- apply (@logic.eq__refl (Point) A).
------------------- assert (* Cut *) (euclidean__axioms.Col A B A) as H29.
-------------------- right.
left.
exact H28.
-------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H30.
--------------------- exists A.
split.
---------------------- exact H6.
---------------------- split.
----------------------- exact H8.
----------------------- split.
------------------------ exact H29.
------------------------ exact H27.
--------------------- apply (@H22 H30).
----------------- assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H27.
------------------ intro H27.
assert (* Cut *) (C = C) as H28.
------------------- apply (@logic.eq__refl (Point) C).
------------------- assert (* Cut *) (euclidean__axioms.Col C D C) as H29.
-------------------- right.
left.
exact H28.
-------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H30.
--------------------- exists C.
split.
---------------------- exact H6.
---------------------- split.
----------------------- exact H8.
----------------------- split.
------------------------ exact H27.
------------------------ exact H29.
--------------------- apply (@H22 H30).
------------------ assert (* Cut *) (~(euclidean__axioms.Col B C D)) as H28.
------------------- intro H28.
assert (* Cut *) (euclidean__axioms.Col C D B) as H29.
-------------------- assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H29.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (D) H28).
--------------------- assert (* AndElim *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H30.
---------------------- exact H29.
---------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)))) as H32.
----------------------- exact H31.
----------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))) as H34.
------------------------ exact H33.
------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)) as H36.
------------------------- exact H35.
------------------------- destruct H36 as [H36 H37].
exact H32.
-------------------- assert (* Cut *) (B = B) as H30.
--------------------- apply (@logic.eq__refl (Point) B).
--------------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H31.
---------------------- right.
right.
left.
exact H30.
---------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H32.
----------------------- exists B.
split.
------------------------ exact H6.
------------------------ split.
------------------------- exact H8.
------------------------- split.
-------------------------- exact H31.
-------------------------- exact H29.
----------------------- apply (@H22 H32).
------------------- assert (* Cut *) (~(euclidean__axioms.Col A B D)) as H29.
-------------------- intro H29.
assert (* Cut *) (D = D) as H30.
--------------------- apply (@logic.eq__refl (Point) D).
--------------------- assert (* Cut *) (euclidean__axioms.Col C D D) as H31.
---------------------- right.
right.
left.
exact H30.
---------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H32.
----------------------- exists D.
split.
------------------------ exact H6.
------------------------ split.
------------------------- exact H8.
------------------------- split.
-------------------------- exact H29.
-------------------------- exact H31.
----------------------- apply (@H22 H32).
-------------------- split.
--------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (C) H27).
--------------------- split.
---------------------- apply (@euclidean__tactics.nCol__notCol (A) (C) (D) H26).
---------------------- split.
----------------------- apply (@euclidean__tactics.nCol__notCol (B) (C) (D) H28).
----------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (D) H29).
Qed.
