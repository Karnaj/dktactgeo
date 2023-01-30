Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__collinearorder.
Require Export lemma__parallelNC.
Require Export logic.
Definition lemma__parallelbetween : forall (B: euclidean__axioms.Point) (H: euclidean__axioms.Point) (K: euclidean__axioms.Point) (L: euclidean__axioms.Point) (M: euclidean__axioms.Point), (euclidean__axioms.BetS H B K) -> ((euclidean__defs.Par M B H L) -> ((euclidean__axioms.Col L M K) -> (euclidean__axioms.BetS L M K))).
Proof.
intro B.
intro H.
intro K.
intro L.
intro M.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (~(euclidean__defs.Meet M B H L)) as H3.
- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.Col M B U) /\ ((euclidean__axioms.Col M B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H L u) /\ ((euclidean__axioms.Col H L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H3.
-- exact H1.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.Col M B U) /\ ((euclidean__axioms.Col M B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H L u) /\ ((euclidean__axioms.Col H L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
--- exact H3.
--- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.Col M B U) /\ ((euclidean__axioms.Col M B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H L u) /\ ((euclidean__axioms.Col H L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H4.
---- exact __TmpHyp.
---- destruct H4 as [x H4].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.Col M B x) /\ ((euclidean__axioms.Col M B V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col H L u) /\ ((euclidean__axioms.Col H L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H5.
----- exact H4.
----- destruct H5 as [x0 H5].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.Col M B x) /\ ((euclidean__axioms.Col M B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H L u) /\ ((euclidean__axioms.Col H L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H6.
------ exact H5.
------ destruct H6 as [x1 H6].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.Col M B x) /\ ((euclidean__axioms.Col M B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H L x1) /\ ((euclidean__axioms.Col H L v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H7.
------- exact H6.
------- destruct H7 as [x2 H7].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.Col M B x) /\ ((euclidean__axioms.Col M B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H L x1) /\ ((euclidean__axioms.Col H L x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H8.
-------- exact H7.
-------- destruct H8 as [x3 H8].
assert (* AndElim *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.Col M B x) /\ ((euclidean__axioms.Col M B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H L x1) /\ ((euclidean__axioms.Col H L x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.Col M B x) /\ ((euclidean__axioms.Col M B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H L x1) /\ ((euclidean__axioms.Col H L x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col M B x) /\ ((euclidean__axioms.Col M B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H L x1) /\ ((euclidean__axioms.Col H L x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col M B x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H L x1) /\ ((euclidean__axioms.Col H L x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H L x1) /\ ((euclidean__axioms.Col H L x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col H L x1) /\ ((euclidean__axioms.Col H L x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col H L x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H23.
---------------- exact H22.
---------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((~(euclidean__defs.Meet M B H L)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H25.
----------------- exact H24.
----------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H27.
------------------ exact H26.
------------------ destruct H27 as [H27 H28].
exact H25.
- assert (* Cut *) (euclidean__axioms.nCol M B H) as H4.
-- assert (* Cut *) ((euclidean__axioms.nCol M B H) /\ ((euclidean__axioms.nCol M H L) /\ ((euclidean__axioms.nCol B H L) /\ (euclidean__axioms.nCol M B L)))) as H4.
--- apply (@lemma__parallelNC.lemma__parallelNC (M) (B) (H) (L) H1).
--- assert (* AndElim *) ((euclidean__axioms.nCol M B H) /\ ((euclidean__axioms.nCol M H L) /\ ((euclidean__axioms.nCol B H L) /\ (euclidean__axioms.nCol M B L)))) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.nCol M H L) /\ ((euclidean__axioms.nCol B H L) /\ (euclidean__axioms.nCol M B L))) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.nCol B H L) /\ (euclidean__axioms.nCol M B L)) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
exact H5.
-- assert (* Cut *) (euclidean__axioms.nCol M H L) as H5.
--- assert (* Cut *) ((euclidean__axioms.nCol M B H) /\ ((euclidean__axioms.nCol M H L) /\ ((euclidean__axioms.nCol B H L) /\ (euclidean__axioms.nCol M B L)))) as H5.
---- apply (@lemma__parallelNC.lemma__parallelNC (M) (B) (H) (L) H1).
---- assert (* AndElim *) ((euclidean__axioms.nCol M B H) /\ ((euclidean__axioms.nCol M H L) /\ ((euclidean__axioms.nCol B H L) /\ (euclidean__axioms.nCol M B L)))) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.nCol M H L) /\ ((euclidean__axioms.nCol B H L) /\ (euclidean__axioms.nCol M B L))) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.nCol B H L) /\ (euclidean__axioms.nCol M B L)) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
exact H8.
--- assert (* Cut *) (euclidean__axioms.neq M B) as H6.
---- assert (* Cut *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq B H) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B M) /\ ((euclidean__axioms.neq H B) /\ (euclidean__axioms.neq H M)))))) as H6.
----- apply (@lemma__NCdistinct.lemma__NCdistinct (M) (B) (H) H4).
----- assert (* AndElim *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq B H) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B M) /\ ((euclidean__axioms.neq H B) /\ (euclidean__axioms.neq H M)))))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq B H) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B M) /\ ((euclidean__axioms.neq H B) /\ (euclidean__axioms.neq H M))))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B M) /\ ((euclidean__axioms.neq H B) /\ (euclidean__axioms.neq H M)))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq B M) /\ ((euclidean__axioms.neq H B) /\ (euclidean__axioms.neq H M))) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq H B) /\ (euclidean__axioms.neq H M)) as H15.
---------- exact H14.
---------- destruct H15 as [H15 H16].
exact H7.
---- assert (* Cut *) (euclidean__axioms.neq H L) as H7.
----- assert (* Cut *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H M) /\ ((euclidean__axioms.neq L H) /\ (euclidean__axioms.neq L M)))))) as H7.
------ apply (@lemma__NCdistinct.lemma__NCdistinct (M) (H) (L) H5).
------ assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H M) /\ ((euclidean__axioms.neq L H) /\ (euclidean__axioms.neq L M)))))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq H L) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H M) /\ ((euclidean__axioms.neq L H) /\ (euclidean__axioms.neq L M))))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H M) /\ ((euclidean__axioms.neq L H) /\ (euclidean__axioms.neq L M)))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq H M) /\ ((euclidean__axioms.neq L H) /\ (euclidean__axioms.neq L M))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq L H) /\ (euclidean__axioms.neq L M)) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
exact H10.
----- assert (* Cut *) (euclidean__axioms.nCol M L H) as H8.
------ assert (* Cut *) ((euclidean__axioms.nCol H M L) /\ ((euclidean__axioms.nCol H L M) /\ ((euclidean__axioms.nCol L M H) /\ ((euclidean__axioms.nCol M L H) /\ (euclidean__axioms.nCol L H M))))) as H8.
------- apply (@lemma__NCorder.lemma__NCorder (M) (H) (L) H5).
------- assert (* AndElim *) ((euclidean__axioms.nCol H M L) /\ ((euclidean__axioms.nCol H L M) /\ ((euclidean__axioms.nCol L M H) /\ ((euclidean__axioms.nCol M L H) /\ (euclidean__axioms.nCol L H M))))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.nCol H L M) /\ ((euclidean__axioms.nCol L M H) /\ ((euclidean__axioms.nCol M L H) /\ (euclidean__axioms.nCol L H M)))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.nCol L M H) /\ ((euclidean__axioms.nCol M L H) /\ (euclidean__axioms.nCol L H M))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.nCol M L H) /\ (euclidean__axioms.nCol L H M)) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
exact H15.
------ assert (* Cut *) (euclidean__axioms.Col M L K) as H9.
------- assert (* Cut *) ((euclidean__axioms.Col M L K) /\ ((euclidean__axioms.Col M K L) /\ ((euclidean__axioms.Col K L M) /\ ((euclidean__axioms.Col L K M) /\ (euclidean__axioms.Col K M L))))) as H9.
-------- apply (@lemma__collinearorder.lemma__collinearorder (L) (M) (K) H2).
-------- assert (* AndElim *) ((euclidean__axioms.Col M L K) /\ ((euclidean__axioms.Col M K L) /\ ((euclidean__axioms.Col K L M) /\ ((euclidean__axioms.Col L K M) /\ (euclidean__axioms.Col K M L))))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col M K L) /\ ((euclidean__axioms.Col K L M) /\ ((euclidean__axioms.Col L K M) /\ (euclidean__axioms.Col K M L)))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col K L M) /\ ((euclidean__axioms.Col L K M) /\ (euclidean__axioms.Col K M L))) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col L K M) /\ (euclidean__axioms.Col K M L)) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
exact H10.
------- assert (* Cut *) (euclidean__axioms.Col H B K) as H10.
-------- right.
right.
right.
right.
left.
exact H0.
-------- assert (* Cut *) (M = M) as H11.
--------- apply (@logic.eq__refl (Point) M).
--------- assert (* Cut *) (L = L) as H12.
---------- apply (@logic.eq__refl (Point) L).
---------- assert (* Cut *) (B = B) as H13.
----------- apply (@logic.eq__refl (Point) B).
----------- assert (* Cut *) (H = H) as H14.
------------ apply (@logic.eq__refl (Point) H).
------------ assert (* Cut *) (~(M = K)) as H15.
------------- intro H15.
assert (* Cut *) (euclidean__axioms.Col H B M) as H16.
-------------- apply (@eq__ind__r euclidean__axioms.Point K (fun M0: euclidean__axioms.Point => (euclidean__defs.Par M0 B H L) -> ((euclidean__axioms.Col L M0 K) -> ((~(euclidean__defs.Meet M0 B H L)) -> ((euclidean__axioms.nCol M0 B H) -> ((euclidean__axioms.nCol M0 H L) -> ((euclidean__axioms.neq M0 B) -> ((euclidean__axioms.nCol M0 L H) -> ((euclidean__axioms.Col M0 L K) -> ((M0 = M0) -> (euclidean__axioms.Col H B M0))))))))))) with (x := M).
---------------intro H16.
intro H17.
intro H18.
intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
exact H10.

--------------- exact H15.
--------------- exact H1.
--------------- exact H2.
--------------- exact H3.
--------------- exact H4.
--------------- exact H5.
--------------- exact H6.
--------------- exact H8.
--------------- exact H9.
--------------- exact H11.
-------------- assert (* Cut *) (euclidean__axioms.Col M B H) as H17.
--------------- assert (* Cut *) ((euclidean__axioms.Col B H M) /\ ((euclidean__axioms.Col B M H) /\ ((euclidean__axioms.Col M H B) /\ ((euclidean__axioms.Col H M B) /\ (euclidean__axioms.Col M B H))))) as H17.
---------------- apply (@lemma__collinearorder.lemma__collinearorder (H) (B) (M) H16).
---------------- assert (* AndElim *) ((euclidean__axioms.Col B H M) /\ ((euclidean__axioms.Col B M H) /\ ((euclidean__axioms.Col M H B) /\ ((euclidean__axioms.Col H M B) /\ (euclidean__axioms.Col M B H))))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col B M H) /\ ((euclidean__axioms.Col M H B) /\ ((euclidean__axioms.Col H M B) /\ (euclidean__axioms.Col M B H)))) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col M H B) /\ ((euclidean__axioms.Col H M B) /\ (euclidean__axioms.Col M B H))) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Col H M B) /\ (euclidean__axioms.Col M B H)) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
exact H25.
--------------- assert (* Cut *) (euclidean__axioms.Col H L H) as H18.
---------------- right.
left.
exact H14.
---------------- assert (* Cut *) (euclidean__defs.Meet M B H L) as H19.
----------------- exists H.
split.
------------------ exact H6.
------------------ split.
------------------- exact H7.
------------------- split.
-------------------- exact H17.
-------------------- exact H18.
----------------- apply (@H3 H19).
------------- assert (* Cut *) (euclidean__axioms.nCol M L H) as H16.
-------------- assert (* Cut *) ((euclidean__axioms.nCol H M L) /\ ((euclidean__axioms.nCol H L M) /\ ((euclidean__axioms.nCol L M H) /\ ((euclidean__axioms.nCol M L H) /\ (euclidean__axioms.nCol L H M))))) as H16.
--------------- apply (@lemma__NCorder.lemma__NCorder (M) (H) (L) H5).
--------------- assert (* AndElim *) ((euclidean__axioms.nCol H M L) /\ ((euclidean__axioms.nCol H L M) /\ ((euclidean__axioms.nCol L M H) /\ ((euclidean__axioms.nCol M L H) /\ (euclidean__axioms.nCol L H M))))) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.nCol H L M) /\ ((euclidean__axioms.nCol L M H) /\ ((euclidean__axioms.nCol M L H) /\ (euclidean__axioms.nCol L H M)))) as H19.
----------------- exact H18.
----------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.nCol L M H) /\ ((euclidean__axioms.nCol M L H) /\ (euclidean__axioms.nCol L H M))) as H21.
------------------ exact H20.
------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.nCol M L H) /\ (euclidean__axioms.nCol L H M)) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
exact H8.
-------------- assert (* Cut *) (euclidean__axioms.Col M L M) as H17.
--------------- right.
left.
exact H11.
--------------- assert (* Cut *) (euclidean__axioms.nCol M K H) as H18.
---------------- apply (@euclidean__tactics.nCol__notCol (M) (K) (H)).
-----------------apply (@euclidean__tactics.nCol__not__Col (M) (K) (H)).
------------------apply (@lemma__NChelper.lemma__NChelper (M) (L) (H) (M) (K) (H16) (H17) (H9) H15).


---------------- assert (* Cut *) (euclidean__axioms.nCol H M K) as H19.
----------------- assert (* Cut *) ((euclidean__axioms.nCol K M H) /\ ((euclidean__axioms.nCol K H M) /\ ((euclidean__axioms.nCol H M K) /\ ((euclidean__axioms.nCol M H K) /\ (euclidean__axioms.nCol H K M))))) as H19.
------------------ apply (@lemma__NCorder.lemma__NCorder (M) (K) (H) H18).
------------------ assert (* AndElim *) ((euclidean__axioms.nCol K M H) /\ ((euclidean__axioms.nCol K H M) /\ ((euclidean__axioms.nCol H M K) /\ ((euclidean__axioms.nCol M H K) /\ (euclidean__axioms.nCol H K M))))) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.nCol K H M) /\ ((euclidean__axioms.nCol H M K) /\ ((euclidean__axioms.nCol M H K) /\ (euclidean__axioms.nCol H K M)))) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.nCol H M K) /\ ((euclidean__axioms.nCol M H K) /\ (euclidean__axioms.nCol H K M))) as H24.
--------------------- exact H23.
--------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.nCol M H K) /\ (euclidean__axioms.nCol H K M)) as H26.
---------------------- exact H25.
---------------------- destruct H26 as [H26 H27].
exact H24.
----------------- assert (* Cut *) ((L = M) \/ ((L = K) \/ ((M = K) \/ ((euclidean__axioms.BetS M L K) \/ ((euclidean__axioms.BetS L M K) \/ (euclidean__axioms.BetS L K M)))))) as H20.
------------------ exact H2.
------------------ assert (* Cut *) (euclidean__axioms.BetS L M K) as H21.
------------------- assert (* Cut *) ((L = M) \/ ((L = K) \/ ((M = K) \/ ((euclidean__axioms.BetS M L K) \/ ((euclidean__axioms.BetS L M K) \/ (euclidean__axioms.BetS L K M)))))) as H21.
-------------------- exact H20.
-------------------- assert (* Cut *) ((L = M) \/ ((L = K) \/ ((M = K) \/ ((euclidean__axioms.BetS M L K) \/ ((euclidean__axioms.BetS L M K) \/ (euclidean__axioms.BetS L K M)))))) as __TmpHyp.
--------------------- exact H21.
--------------------- assert (L = M \/ (L = K) \/ ((M = K) \/ ((euclidean__axioms.BetS M L K) \/ ((euclidean__axioms.BetS L M K) \/ (euclidean__axioms.BetS L K M))))) as H22.
---------------------- exact __TmpHyp.
---------------------- destruct H22 as [H22|H22].
----------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS L M K))) as H23.
------------------------ intro H23.
assert (* Cut *) (euclidean__axioms.Col M B M) as H24.
------------------------- right.
left.
exact H11.
------------------------- assert (* Cut *) (euclidean__axioms.Col H L L) as H25.
-------------------------- right.
right.
left.
exact H12.
-------------------------- assert (* Cut *) (euclidean__axioms.Col H L M) as H26.
--------------------------- apply (@eq__ind__r euclidean__axioms.Point M (fun L0: euclidean__axioms.Point => (euclidean__defs.Par M B H L0) -> ((euclidean__axioms.Col L0 M K) -> ((~(euclidean__defs.Meet M B H L0)) -> ((euclidean__axioms.nCol M H L0) -> ((euclidean__axioms.neq H L0) -> ((euclidean__axioms.nCol M L0 H) -> ((euclidean__axioms.Col M L0 K) -> ((L0 = L0) -> ((euclidean__axioms.nCol M L0 H) -> ((euclidean__axioms.Col M L0 M) -> ((~(euclidean__axioms.BetS L0 M K)) -> ((euclidean__axioms.Col H L0 L0) -> (euclidean__axioms.Col H L0 M)))))))))))))) with (x := L).
----------------------------intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
exact H37.

---------------------------- exact H22.
---------------------------- exact H1.
---------------------------- exact H2.
---------------------------- exact H3.
---------------------------- exact H5.
---------------------------- exact H7.
---------------------------- exact H8.
---------------------------- exact H9.
---------------------------- exact H12.
---------------------------- exact H16.
---------------------------- exact H17.
---------------------------- exact H23.
---------------------------- exact H25.
--------------------------- assert (* Cut *) (euclidean__defs.Meet M B H L) as H27.
---------------------------- exists M.
split.
----------------------------- exact H6.
----------------------------- split.
------------------------------ exact H7.
------------------------------ split.
------------------------------- exact H24.
------------------------------- exact H26.
---------------------------- apply (@H3 H27).
------------------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS L M K)).
-------------------------intro H24.
assert (* AndElim *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))))))) as H25.
-------------------------- exact H4.
-------------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))))))) as H27.
--------------------------- exact H5.
--------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))))) as H29.
---------------------------- exact H8.
---------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))))) as H31.
----------------------------- exact H16.
----------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq M K) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))))))) as H33.
------------------------------ exact H18.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq H M) /\ ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))))))) as H35.
------------------------------- exact H19.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H)))))) as H37.
-------------------------------- exact H26.
-------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L)))))) as H39.
--------------------------------- exact H28.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))))) as H41.
---------------------------------- exact H30.
---------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))))) as H43.
----------------------------------- exact H32.
----------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H)))))) as H45.
------------------------------------ exact H34.
------------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K)))))) as H47.
------------------------------------- exact H36.
------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))))) as H49.
-------------------------------------- exact H38.
-------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))))) as H51.
--------------------------------------- exact H40.
--------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))) as H53.
---------------------------------------- exact H42.
---------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))) as H55.
----------------------------------------- exact H44.
----------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))))) as H57.
------------------------------------------ exact H46.
------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))))) as H59.
------------------------------------------- exact H48.
------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H)))) as H61.
-------------------------------------------- exact H50.
-------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L)))) as H63.
--------------------------------------------- exact H52.
--------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))) as H65.
---------------------------------------------- exact H54.
---------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))) as H67.
----------------------------------------------- exact H56.
----------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H)))) as H69.
------------------------------------------------ exact H58.
------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K)))) as H71.
------------------------------------------------- exact H60.
------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))) as H73.
-------------------------------------------------- exact H62.
-------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))) as H75.
--------------------------------------------------- exact H64.
--------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))) as H77.
---------------------------------------------------- exact H66.
---------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))) as H79.
----------------------------------------------------- exact H68.
----------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))) as H81.
------------------------------------------------------ exact H70.
------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))) as H83.
------------------------------------------------------- exact H72.
------------------------------------------------------- destruct H83 as [H83 H84].
assert (* Cut *) (False) as H85.
-------------------------------------------------------- apply (@H23 H24).
-------------------------------------------------------- assert False.
---------------------------------------------------------exact H85.
--------------------------------------------------------- contradiction.

----------------------- assert (L = K \/ (M = K) \/ ((euclidean__axioms.BetS M L K) \/ ((euclidean__axioms.BetS L M K) \/ (euclidean__axioms.BetS L K M)))) as H23.
------------------------ exact H22.
------------------------ destruct H23 as [H23|H23].
------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS L M K))) as H24.
-------------------------- intro H24.
assert (* Cut *) (euclidean__axioms.Col H B L) as H25.
--------------------------- apply (@eq__ind__r euclidean__axioms.Point K (fun L0: euclidean__axioms.Point => (euclidean__defs.Par M B H L0) -> ((euclidean__axioms.Col L0 M K) -> ((~(euclidean__defs.Meet M B H L0)) -> ((euclidean__axioms.nCol M H L0) -> ((euclidean__axioms.neq H L0) -> ((euclidean__axioms.nCol M L0 H) -> ((euclidean__axioms.Col M L0 K) -> ((L0 = L0) -> ((euclidean__axioms.nCol M L0 H) -> ((euclidean__axioms.Col M L0 M) -> ((~(euclidean__axioms.BetS L0 M K)) -> (euclidean__axioms.Col H B L0))))))))))))) with (x := L).
----------------------------intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
exact H10.

---------------------------- exact H23.
---------------------------- exact H1.
---------------------------- exact H2.
---------------------------- exact H3.
---------------------------- exact H5.
---------------------------- exact H7.
---------------------------- exact H8.
---------------------------- exact H9.
---------------------------- exact H12.
---------------------------- exact H16.
---------------------------- exact H17.
---------------------------- exact H24.
--------------------------- assert (* Cut *) (euclidean__axioms.Col H L B) as H26.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col B H L) /\ ((euclidean__axioms.Col B L H) /\ ((euclidean__axioms.Col L H B) /\ ((euclidean__axioms.Col H L B) /\ (euclidean__axioms.Col L B H))))) as H26.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H) (B) (L) H25).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col B H L) /\ ((euclidean__axioms.Col B L H) /\ ((euclidean__axioms.Col L H B) /\ ((euclidean__axioms.Col H L B) /\ (euclidean__axioms.Col L B H))))) as H27.
------------------------------ exact H26.
------------------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col B L H) /\ ((euclidean__axioms.Col L H B) /\ ((euclidean__axioms.Col H L B) /\ (euclidean__axioms.Col L B H)))) as H29.
------------------------------- exact H28.
------------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col L H B) /\ ((euclidean__axioms.Col H L B) /\ (euclidean__axioms.Col L B H))) as H31.
-------------------------------- exact H30.
-------------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col H L B) /\ (euclidean__axioms.Col L B H)) as H33.
--------------------------------- exact H32.
--------------------------------- destruct H33 as [H33 H34].
exact H33.
---------------------------- assert (* Cut *) (euclidean__axioms.Col M B B) as H27.
----------------------------- right.
right.
left.
exact H13.
----------------------------- assert (* Cut *) (euclidean__defs.Meet M B H L) as H28.
------------------------------ exists B.
split.
------------------------------- exact H6.
------------------------------- split.
-------------------------------- exact H7.
-------------------------------- split.
--------------------------------- exact H27.
--------------------------------- exact H26.
------------------------------ apply (@H3 H28).
-------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS L M K)).
---------------------------intro H25.
assert (* AndElim *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))))))) as H26.
---------------------------- exact H4.
---------------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))))))) as H28.
----------------------------- exact H5.
----------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))))) as H30.
------------------------------ exact H8.
------------------------------ destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))))) as H32.
------------------------------- exact H16.
------------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq M K) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))))))) as H34.
-------------------------------- exact H18.
-------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq H M) /\ ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))))))) as H36.
--------------------------------- exact H19.
--------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H)))))) as H38.
---------------------------------- exact H27.
---------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L)))))) as H40.
----------------------------------- exact H29.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))))) as H42.
------------------------------------ exact H31.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))))) as H44.
------------------------------------- exact H33.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H)))))) as H46.
-------------------------------------- exact H35.
-------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K)))))) as H48.
--------------------------------------- exact H37.
--------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))))) as H50.
---------------------------------------- exact H39.
---------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))))) as H52.
----------------------------------------- exact H41.
----------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))) as H54.
------------------------------------------ exact H43.
------------------------------------------ destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))) as H56.
------------------------------------------- exact H45.
------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))))) as H58.
-------------------------------------------- exact H47.
-------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))))) as H60.
--------------------------------------------- exact H49.
--------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H)))) as H62.
---------------------------------------------- exact H51.
---------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L)))) as H64.
----------------------------------------------- exact H53.
----------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))) as H66.
------------------------------------------------ exact H55.
------------------------------------------------ destruct H66 as [H66 H67].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))) as H68.
------------------------------------------------- exact H57.
------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H)))) as H70.
-------------------------------------------------- exact H59.
-------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K)))) as H72.
--------------------------------------------------- exact H61.
--------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))) as H74.
---------------------------------------------------- exact H63.
---------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))) as H76.
----------------------------------------------------- exact H65.
----------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))) as H78.
------------------------------------------------------ exact H67.
------------------------------------------------------ destruct H78 as [H78 H79].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))) as H80.
------------------------------------------------------- exact H69.
------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))) as H82.
-------------------------------------------------------- exact H71.
-------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))) as H84.
--------------------------------------------------------- exact H73.
--------------------------------------------------------- destruct H84 as [H84 H85].
assert (* Cut *) (False) as H86.
---------------------------------------------------------- apply (@H24 H25).
---------------------------------------------------------- assert False.
-----------------------------------------------------------exact H86.
----------------------------------------------------------- contradiction.

------------------------- assert (M = K \/ (euclidean__axioms.BetS M L K) \/ ((euclidean__axioms.BetS L M K) \/ (euclidean__axioms.BetS L K M))) as H24.
-------------------------- exact H23.
-------------------------- destruct H24 as [H24|H24].
--------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS L M K))) as H25.
---------------------------- intro H25.
apply (@H15 H24).
---------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS L M K)).
-----------------------------intro H26.
assert (* AndElim *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))))))) as H27.
------------------------------ exact H4.
------------------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))))))) as H29.
------------------------------- exact H5.
------------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))))) as H31.
-------------------------------- exact H8.
-------------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))))) as H33.
--------------------------------- exact H16.
--------------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq M K) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))))))) as H35.
---------------------------------- exact H18.
---------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq H M) /\ ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))))))) as H37.
----------------------------------- exact H19.
----------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H)))))) as H39.
------------------------------------ exact H28.
------------------------------------ destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L)))))) as H41.
------------------------------------- exact H30.
------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))))) as H43.
-------------------------------------- exact H32.
-------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))))) as H45.
--------------------------------------- exact H34.
--------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H)))))) as H47.
---------------------------------------- exact H36.
---------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K)))))) as H49.
----------------------------------------- exact H38.
----------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))))) as H51.
------------------------------------------ exact H40.
------------------------------------------ destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))))) as H53.
------------------------------------------- exact H42.
------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))) as H55.
-------------------------------------------- exact H44.
-------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))) as H57.
--------------------------------------------- exact H46.
--------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))))) as H59.
---------------------------------------------- exact H48.
---------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))))) as H61.
----------------------------------------------- exact H50.
----------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H)))) as H63.
------------------------------------------------ exact H52.
------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L)))) as H65.
------------------------------------------------- exact H54.
------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))) as H67.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))) as H69.
--------------------------------------------------- exact H58.
--------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H)))) as H71.
---------------------------------------------------- exact H60.
---------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K)))) as H73.
----------------------------------------------------- exact H62.
----------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))) as H75.
------------------------------------------------------ exact H64.
------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))) as H77.
------------------------------------------------------- exact H66.
------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))) as H79.
-------------------------------------------------------- exact H68.
-------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))) as H81.
--------------------------------------------------------- exact H70.
--------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))) as H83.
---------------------------------------------------------- exact H72.
---------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))) as H85.
----------------------------------------------------------- exact H74.
----------------------------------------------------------- destruct H85 as [H85 H86].
assert (* Cut *) (False) as H87.
------------------------------------------------------------ apply (@H15 H24).
------------------------------------------------------------ assert (* Cut *) (False) as H88.
------------------------------------------------------------- apply (@H25 H26).
------------------------------------------------------------- assert False.
--------------------------------------------------------------exact H88.
-------------------------------------------------------------- contradiction.

--------------------------- assert (euclidean__axioms.BetS M L K \/ (euclidean__axioms.BetS L M K) \/ (euclidean__axioms.BetS L K M)) as H25.
---------------------------- exact H24.
---------------------------- destruct H25 as [H25|H25].
----------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS L M K))) as H26.
------------------------------ intro H26.
assert (* Cut *) (euclidean__axioms.nCol H K M) as H27.
------------------------------- assert (* Cut *) ((euclidean__axioms.nCol M H K) /\ ((euclidean__axioms.nCol M K H) /\ ((euclidean__axioms.nCol K H M) /\ ((euclidean__axioms.nCol H K M) /\ (euclidean__axioms.nCol K M H))))) as H27.
-------------------------------- apply (@lemma__NCorder.lemma__NCorder (H) (M) (K) H19).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol M H K) /\ ((euclidean__axioms.nCol M K H) /\ ((euclidean__axioms.nCol K H M) /\ ((euclidean__axioms.nCol H K M) /\ (euclidean__axioms.nCol K M H))))) as H28.
--------------------------------- exact H27.
--------------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.nCol M K H) /\ ((euclidean__axioms.nCol K H M) /\ ((euclidean__axioms.nCol H K M) /\ (euclidean__axioms.nCol K M H)))) as H30.
---------------------------------- exact H29.
---------------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.nCol K H M) /\ ((euclidean__axioms.nCol H K M) /\ (euclidean__axioms.nCol K M H))) as H32.
----------------------------------- exact H31.
----------------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.nCol H K M) /\ (euclidean__axioms.nCol K M H)) as H34.
------------------------------------ exact H33.
------------------------------------ destruct H34 as [H34 H35].
exact H34.
------------------------------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS H E L) /\ (euclidean__axioms.BetS M E B)) as H28.
-------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (H) (M) (K) (B) (L) (H0) (H25) H27).
-------------------------------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS H E L) /\ (euclidean__axioms.BetS M E B))) as H29.
--------------------------------- exact H28.
--------------------------------- destruct H29 as [E H29].
assert (* AndElim *) ((euclidean__axioms.BetS H E L) /\ (euclidean__axioms.BetS M E B)) as H30.
---------------------------------- exact H29.
---------------------------------- destruct H30 as [H30 H31].
assert (* Cut *) (euclidean__axioms.Col H E L) as H32.
----------------------------------- right.
right.
right.
right.
left.
exact H30.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col M E B) as H33.
------------------------------------ right.
right.
right.
right.
left.
exact H31.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col H L E) as H34.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E H L) /\ ((euclidean__axioms.Col E L H) /\ ((euclidean__axioms.Col L H E) /\ ((euclidean__axioms.Col H L E) /\ (euclidean__axioms.Col L E H))))) as H34.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H) (E) (L) H32).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E H L) /\ ((euclidean__axioms.Col E L H) /\ ((euclidean__axioms.Col L H E) /\ ((euclidean__axioms.Col H L E) /\ (euclidean__axioms.Col L E H))))) as H35.
--------------------------------------- exact H34.
--------------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col E L H) /\ ((euclidean__axioms.Col L H E) /\ ((euclidean__axioms.Col H L E) /\ (euclidean__axioms.Col L E H)))) as H37.
---------------------------------------- exact H36.
---------------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col L H E) /\ ((euclidean__axioms.Col H L E) /\ (euclidean__axioms.Col L E H))) as H39.
----------------------------------------- exact H38.
----------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col H L E) /\ (euclidean__axioms.Col L E H)) as H41.
------------------------------------------ exact H40.
------------------------------------------ destruct H41 as [H41 H42].
exact H41.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col M B E) as H35.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E M B) /\ ((euclidean__axioms.Col E B M) /\ ((euclidean__axioms.Col B M E) /\ ((euclidean__axioms.Col M B E) /\ (euclidean__axioms.Col B E M))))) as H35.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (M) (E) (B) H33).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E M B) /\ ((euclidean__axioms.Col E B M) /\ ((euclidean__axioms.Col B M E) /\ ((euclidean__axioms.Col M B E) /\ (euclidean__axioms.Col B E M))))) as H36.
---------------------------------------- exact H35.
---------------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col E B M) /\ ((euclidean__axioms.Col B M E) /\ ((euclidean__axioms.Col M B E) /\ (euclidean__axioms.Col B E M)))) as H38.
----------------------------------------- exact H37.
----------------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col B M E) /\ ((euclidean__axioms.Col M B E) /\ (euclidean__axioms.Col B E M))) as H40.
------------------------------------------ exact H39.
------------------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col M B E) /\ (euclidean__axioms.Col B E M)) as H42.
------------------------------------------- exact H41.
------------------------------------------- destruct H42 as [H42 H43].
exact H42.
-------------------------------------- assert (* Cut *) (euclidean__defs.Meet M B H L) as H36.
--------------------------------------- exists E.
split.
---------------------------------------- exact H6.
---------------------------------------- split.
----------------------------------------- exact H7.
----------------------------------------- split.
------------------------------------------ exact H35.
------------------------------------------ exact H34.
--------------------------------------- apply (@H3 H36).
------------------------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS L M K)).
-------------------------------intro H27.
assert (* AndElim *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))))))) as H28.
-------------------------------- exact H4.
-------------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))))))) as H30.
--------------------------------- exact H5.
--------------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))))) as H32.
---------------------------------- exact H8.
---------------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))))) as H34.
----------------------------------- exact H16.
----------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq M K) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))))))) as H36.
------------------------------------ exact H18.
------------------------------------ destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq H M) /\ ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))))))) as H38.
------------------------------------- exact H19.
------------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H)))))) as H40.
-------------------------------------- exact H29.
-------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L)))))) as H42.
--------------------------------------- exact H31.
--------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))))) as H44.
---------------------------------------- exact H33.
---------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))))) as H46.
----------------------------------------- exact H35.
----------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H)))))) as H48.
------------------------------------------ exact H37.
------------------------------------------ destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K)))))) as H50.
------------------------------------------- exact H39.
------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))))) as H52.
-------------------------------------------- exact H41.
-------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))))) as H54.
--------------------------------------------- exact H43.
--------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))) as H56.
---------------------------------------------- exact H45.
---------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))) as H58.
----------------------------------------------- exact H47.
----------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))))) as H60.
------------------------------------------------ exact H49.
------------------------------------------------ destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))))) as H62.
------------------------------------------------- exact H51.
------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H)))) as H64.
-------------------------------------------------- exact H53.
-------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L)))) as H66.
--------------------------------------------------- exact H55.
--------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))) as H68.
---------------------------------------------------- exact H57.
---------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))) as H70.
----------------------------------------------------- exact H59.
----------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H)))) as H72.
------------------------------------------------------ exact H61.
------------------------------------------------------ destruct H72 as [H72 H73].
assert (* AndElim *) ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K)))) as H74.
------------------------------------------------------- exact H63.
------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))) as H76.
-------------------------------------------------------- exact H65.
-------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))) as H78.
--------------------------------------------------------- exact H67.
--------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))) as H80.
---------------------------------------------------------- exact H69.
---------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))) as H82.
----------------------------------------------------------- exact H71.
----------------------------------------------------------- destruct H82 as [H82 H83].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))) as H84.
------------------------------------------------------------ exact H73.
------------------------------------------------------------ destruct H84 as [H84 H85].
assert (* AndElim *) ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))) as H86.
------------------------------------------------------------- exact H75.
------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* Cut *) (False) as H88.
-------------------------------------------------------------- apply (@H26 H27).
-------------------------------------------------------------- assert False.
---------------------------------------------------------------exact H88.
--------------------------------------------------------------- contradiction.

----------------------------- assert (euclidean__axioms.BetS L M K \/ euclidean__axioms.BetS L K M) as H26.
------------------------------ exact H25.
------------------------------ destruct H26 as [H26|H26].
------------------------------- exact H26.
------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS L M K))) as H27.
-------------------------------- intro H27.
assert (* Cut *) (euclidean__axioms.BetS M K L) as H28.
--------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (L) (K) (M) H26).
--------------------------------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS H E L) /\ (euclidean__axioms.BetS M B E)) as H29.
---------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (H) (M) (K) (B) (L) (H0) (H28) H16).
---------------------------------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS H E L) /\ (euclidean__axioms.BetS M B E))) as H30.
----------------------------------- exact H29.
----------------------------------- destruct H30 as [E H30].
assert (* AndElim *) ((euclidean__axioms.BetS H E L) /\ (euclidean__axioms.BetS M B E)) as H31.
------------------------------------ exact H30.
------------------------------------ destruct H31 as [H31 H32].
assert (* Cut *) (euclidean__axioms.Col H E L) as H33.
------------------------------------- right.
right.
right.
right.
left.
exact H31.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col M B E) as H34.
-------------------------------------- right.
right.
right.
right.
left.
exact H32.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col H L E) as H35.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E H L) /\ ((euclidean__axioms.Col E L H) /\ ((euclidean__axioms.Col L H E) /\ ((euclidean__axioms.Col H L E) /\ (euclidean__axioms.Col L E H))))) as H35.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H) (E) (L) H33).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E H L) /\ ((euclidean__axioms.Col E L H) /\ ((euclidean__axioms.Col L H E) /\ ((euclidean__axioms.Col H L E) /\ (euclidean__axioms.Col L E H))))) as H36.
----------------------------------------- exact H35.
----------------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col E L H) /\ ((euclidean__axioms.Col L H E) /\ ((euclidean__axioms.Col H L E) /\ (euclidean__axioms.Col L E H)))) as H38.
------------------------------------------ exact H37.
------------------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col L H E) /\ ((euclidean__axioms.Col H L E) /\ (euclidean__axioms.Col L E H))) as H40.
------------------------------------------- exact H39.
------------------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col H L E) /\ (euclidean__axioms.Col L E H)) as H42.
-------------------------------------------- exact H41.
-------------------------------------------- destruct H42 as [H42 H43].
exact H42.
--------------------------------------- assert (* Cut *) (euclidean__defs.Meet M B H L) as H36.
---------------------------------------- exists E.
split.
----------------------------------------- exact H6.
----------------------------------------- split.
------------------------------------------ exact H7.
------------------------------------------ split.
------------------------------------------- exact H34.
------------------------------------------- exact H35.
---------------------------------------- apply (@H3 H36).
-------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS L M K)).
---------------------------------intro H28.
assert (* AndElim *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))))))) as H29.
---------------------------------- exact H4.
---------------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))))))) as H31.
----------------------------------- exact H5.
----------------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))))) as H33.
------------------------------------ exact H8.
------------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))))) as H35.
------------------------------------- exact H16.
------------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq M K) /\ ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))))))) as H37.
-------------------------------------- exact H18.
-------------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.neq H M) /\ ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))))))) as H39.
--------------------------------------- exact H19.
--------------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H)))))) as H41.
---------------------------------------- exact H30.
---------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L)))))) as H43.
----------------------------------------- exact H32.
----------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))))) as H45.
------------------------------------------ exact H34.
------------------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))))) as H47.
------------------------------------------- exact H36.
------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H)))))) as H49.
-------------------------------------------- exact H38.
-------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K)))))) as H51.
--------------------------------------------- exact H40.
--------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq B H) /\ ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))))) as H53.
---------------------------------------------- exact H42.
---------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq H L) /\ ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))))) as H55.
----------------------------------------------- exact H44.
----------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))) as H57.
------------------------------------------------ exact H46.
------------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.neq L H) /\ ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))))) as H59.
------------------------------------------------- exact H48.
------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.neq K H) /\ ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))))) as H61.
-------------------------------------------------- exact H50.
-------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.neq M K) /\ ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))))) as H63.
--------------------------------------------------- exact H52.
--------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((~(euclidean__axioms.BetS M B H)) /\ ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H)))) as H65.
---------------------------------------------------- exact H54.
---------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L)))) as H67.
----------------------------------------------------- exact H56.
----------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))) as H69.
------------------------------------------------------ exact H58.
------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H)))) as H71.
------------------------------------------------------- exact H60.
------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((~(euclidean__axioms.BetS M K H)) /\ ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H)))) as H73.
-------------------------------------------------------- exact H62.
-------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((~(euclidean__axioms.BetS H M K)) /\ ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K)))) as H75.
--------------------------------------------------------- exact H64.
--------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H B)) /\ (~(euclidean__axioms.BetS B M H))) as H77.
---------------------------------------------------------- exact H66.
---------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((~(euclidean__axioms.BetS M L H)) /\ (~(euclidean__axioms.BetS H M L))) as H79.
----------------------------------------------------------- exact H68.
----------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))) as H81.
------------------------------------------------------------ exact H70.
------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H L)) /\ (~(euclidean__axioms.BetS L M H))) as H83.
------------------------------------------------------------- exact H72.
------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((~(euclidean__axioms.BetS M H K)) /\ (~(euclidean__axioms.BetS K M H))) as H85.
-------------------------------------------------------------- exact H74.
-------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((~(euclidean__axioms.BetS H K M)) /\ (~(euclidean__axioms.BetS M H K))) as H87.
--------------------------------------------------------------- exact H76.
--------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* Cut *) (False) as H89.
---------------------------------------------------------------- apply (@H27 H28).
---------------------------------------------------------------- assert False.
-----------------------------------------------------------------exact H89.
----------------------------------------------------------------- contradiction.

------------------- exact H21.
Qed.
