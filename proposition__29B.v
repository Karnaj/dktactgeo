Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Require Export proposition__29.
Definition proposition__29B : forall (A: euclidean__axioms.Point) (D: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point), (euclidean__defs.Par A G H D) -> ((euclidean__axioms.TS A G H D) -> (euclidean__defs.CongA A G H G H D)).
Proof.
intro A.
intro D.
intro G.
intro H.
intro H0.
intro H1.
assert (* Cut *) (exists (a: euclidean__axioms.Point) (d: euclidean__axioms.Point) (g: euclidean__axioms.Point) (h: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G a) /\ ((euclidean__axioms.Col A G g) /\ ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g))))))))))) as H2.
- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H D u) /\ ((euclidean__axioms.Col H D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H2.
-- exact H0.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H D u) /\ ((euclidean__axioms.Col H D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp.
--- exact H2.
--- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H D u) /\ ((euclidean__axioms.Col H D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H3.
---- exact __TmpHyp.
---- destruct H3 as [x H3].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq x V) /\ ((euclidean__axioms.Col H D u) /\ ((euclidean__axioms.Col H D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H4.
----- exact H3.
----- destruct H4 as [x0 H4].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point) (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H D u) /\ ((euclidean__axioms.Col H D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS u X x0)))))))))))) as H5.
------ exact H4.
------ destruct H5 as [x1 H5].
assert (exists v: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H D x1) /\ ((euclidean__axioms.Col H D v) /\ ((euclidean__axioms.neq x1 v) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x X v) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H6.
------- exact H5.
------- destruct H6 as [x2 H6].
assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H D x1) /\ ((euclidean__axioms.Col H D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x X x2) /\ (euclidean__axioms.BetS x1 X x0)))))))))))) as H7.
-------- exact H6.
-------- destruct H7 as [x3 H7].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H D x1) /\ ((euclidean__axioms.Col H D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H D x1) /\ ((euclidean__axioms.Col H D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col A G x) /\ ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H D x1) /\ ((euclidean__axioms.Col H D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col A G x0) /\ ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H D x1) /\ ((euclidean__axioms.Col H D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))))) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq x x0) /\ ((euclidean__axioms.Col H D x1) /\ ((euclidean__axioms.Col H D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))))) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col H D x1) /\ ((euclidean__axioms.Col H D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))))) as H18.
-------------- exact H17.
-------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col H D x2) /\ ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))))) as H20.
--------------- exact H19.
--------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq x1 x2) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)))) as H22.
---------------- exact H21.
---------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0))) as H24.
----------------- exact H23.
----------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS x x3 x2) /\ (euclidean__axioms.BetS x1 x3 x0)) as H26.
------------------ exact H25.
------------------ destruct H26 as [H26 H27].
exists x.
exists x2.
exists x0.
exists x1.
exists x3.
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
- assert (exists a: euclidean__axioms.Point, (exists (d: euclidean__axioms.Point) (g: euclidean__axioms.Point) (h: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G a) /\ ((euclidean__axioms.Col A G g) /\ ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g)))))))))))) as H3.
-- exact H2.
-- destruct H3 as [a H3].
assert (exists d: euclidean__axioms.Point, (exists (g: euclidean__axioms.Point) (h: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G a) /\ ((euclidean__axioms.Col A G g) /\ ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g)))))))))))) as H4.
--- exact H3.
--- destruct H4 as [d H4].
assert (exists g: euclidean__axioms.Point, (exists (h: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G a) /\ ((euclidean__axioms.Col A G g) /\ ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g)))))))))))) as H5.
---- exact H4.
---- destruct H5 as [g H5].
assert (exists h: euclidean__axioms.Point, (exists (m: euclidean__axioms.Point), (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G a) /\ ((euclidean__axioms.Col A G g) /\ ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g)))))))))))) as H6.
----- exact H5.
----- destruct H6 as [h H6].
assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G a) /\ ((euclidean__axioms.Col A G g) /\ ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g)))))))))))) as H7.
------ exact H6.
------ destruct H7 as [m H7].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G a) /\ ((euclidean__axioms.Col A G g) /\ ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g))))))))))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G a) /\ ((euclidean__axioms.Col A G g) /\ ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g)))))))))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col A G a) /\ ((euclidean__axioms.Col A G g) /\ ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g))))))))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col A G g) /\ ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g)))))))) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g))))))) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g)))))) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g))))) as H20.
------------- exact H19.
------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g)))) as H22.
-------------- exact H21.
-------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g))) as H24.
--------------- exact H23.
--------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g)) as H26.
---------------- exact H25.
---------------- destruct H26 as [H26 H27].
assert (* Cut *) (euclidean__axioms.neq D H) as H28.
----------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (H) (D) H10).
----------------- assert (* Cut *) (~(H = G)) as H29.
------------------ intro H29.
assert (* Cut *) (H = H) as H30.
------------------- apply (@logic.eq__refl (Point) H).
------------------- assert (* Cut *) (euclidean__axioms.Col H D H) as H31.
-------------------- right.
left.
exact H30.
-------------------- assert (* Cut *) (G = G) as H32.
--------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun H32: euclidean__axioms.Point => (euclidean__defs.Par A G H32 D) -> ((euclidean__axioms.TS A G H32 D) -> ((euclidean__axioms.neq H32 D) -> ((euclidean__axioms.Col H32 D h) -> ((euclidean__axioms.Col H32 D d) -> ((~(euclidean__defs.Meet A G H32 D)) -> ((euclidean__axioms.neq D H32) -> ((H32 = H32) -> ((euclidean__axioms.Col H32 D H32) -> (G = G))))))))))) with (x := H).
----------------------intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
assert (* Cut *) (G = G) as H41.
----------------------- exact H39.
----------------------- exact H41.

---------------------- exact H29.
---------------------- exact H0.
---------------------- exact H1.
---------------------- exact H10.
---------------------- exact H18.
---------------------- exact H20.
---------------------- exact H24.
---------------------- exact H28.
---------------------- exact H30.
---------------------- exact H31.
--------------------- assert (* Cut *) (euclidean__axioms.Col A G G) as H33.
---------------------- right.
right.
left.
exact H32.
---------------------- assert (* Cut *) (euclidean__axioms.Col A G H) as H34.
----------------------- apply (@eq__ind euclidean__axioms.Point H (fun G0: euclidean__axioms.Point => (euclidean__defs.Par A G0 H D) -> ((euclidean__axioms.TS A G0 H D) -> ((euclidean__axioms.neq A G0) -> ((euclidean__axioms.Col A G0 a) -> ((euclidean__axioms.Col A G0 g) -> ((~(euclidean__defs.Meet A G0 H D)) -> ((G0 = G0) -> ((euclidean__axioms.Col A G0 G0) -> (euclidean__axioms.Col A G0 H)))))))))) with (y := G).
------------------------intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
assert (* Cut *) (H = H) as H42.
------------------------- exact H40.
------------------------- exact H41.

------------------------ exact H29.
------------------------ exact H0.
------------------------ exact H1.
------------------------ exact H8.
------------------------ exact H12.
------------------------ exact H14.
------------------------ exact H24.
------------------------ exact H32.
------------------------ exact H33.
----------------------- assert (* Cut *) (euclidean__defs.Meet A G H D) as H35.
------------------------ exists H.
split.
------------------------- exact H8.
------------------------- split.
-------------------------- exact H10.
-------------------------- split.
--------------------------- exact H34.
--------------------------- exact H31.
------------------------ apply (@H24 H35).
------------------ assert (* Cut *) (exists (B: euclidean__axioms.Point), (euclidean__axioms.BetS A G B) /\ (euclidean__axioms.Cong G B A G)) as H30.
------------------- apply (@lemma__extension.lemma__extension (A) (G) (A) (G) (H8) H8).
------------------- assert (exists B: euclidean__axioms.Point, ((euclidean__axioms.BetS A G B) /\ (euclidean__axioms.Cong G B A G))) as H31.
-------------------- exact H30.
-------------------- destruct H31 as [B H31].
assert (* AndElim *) ((euclidean__axioms.BetS A G B) /\ (euclidean__axioms.Cong G B A G)) as H32.
--------------------- exact H31.
--------------------- destruct H32 as [H32 H33].
assert (* Cut *) (exists (C: euclidean__axioms.Point), (euclidean__axioms.BetS D H C) /\ (euclidean__axioms.Cong H C D H)) as H34.
---------------------- apply (@lemma__extension.lemma__extension (D) (H) (D) (H) (H28) H28).
---------------------- assert (exists C: euclidean__axioms.Point, ((euclidean__axioms.BetS D H C) /\ (euclidean__axioms.Cong H C D H))) as H35.
----------------------- exact H34.
----------------------- destruct H35 as [C H35].
assert (* AndElim *) ((euclidean__axioms.BetS D H C) /\ (euclidean__axioms.Cong H C D H)) as H36.
------------------------ exact H35.
------------------------ destruct H36 as [H36 H37].
assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS H G E) /\ (euclidean__axioms.Cong G E H G)) as H38.
------------------------- apply (@lemma__extension.lemma__extension (H) (G) (H) (G) (H29) H29).
------------------------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS H G E) /\ (euclidean__axioms.Cong G E H G))) as H39.
-------------------------- exact H38.
-------------------------- destruct H39 as [E H39].
assert (* AndElim *) ((euclidean__axioms.BetS H G E) /\ (euclidean__axioms.Cong G E H G)) as H40.
--------------------------- exact H39.
--------------------------- destruct H40 as [H40 H41].
assert (* Cut *) (euclidean__axioms.neq A B) as H42.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H42.
----------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (G) (B) H32).
----------------------------- assert (* AndElim *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H43.
------------------------------ exact H42.
------------------------------ destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B)) as H45.
------------------------------- exact H44.
------------------------------- destruct H45 as [H45 H46].
exact H46.
---------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H43.
----------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H42).
----------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H44.
------------------------------ assert (* Cut *) ((euclidean__axioms.neq H C) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D C))) as H44.
------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (H) (C) H36).
------------------------------- assert (* AndElim *) ((euclidean__axioms.neq H C) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D C))) as H45.
-------------------------------- exact H44.
-------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D C)) as H47.
--------------------------------- exact H46.
--------------------------------- destruct H47 as [H47 H48].
exact H48.
------------------------------ assert (* Cut *) (euclidean__axioms.neq C D) as H45.
------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (C) H44).
------------------------------- assert (* Cut *) (euclidean__axioms.Col A G B) as H46.
-------------------------------- right.
right.
right.
right.
left.
exact H32.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col G A B) as H47.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H47.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (B) H46).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H48.
----------------------------------- exact H47.
----------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A)))) as H50.
------------------------------------ exact H49.
------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))) as H52.
------------------------------------- exact H51.
------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A)) as H54.
-------------------------------------- exact H53.
-------------------------------------- destruct H54 as [H54 H55].
exact H48.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col G A a) as H48.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col G A a) /\ ((euclidean__axioms.Col G a A) /\ ((euclidean__axioms.Col a A G) /\ ((euclidean__axioms.Col A a G) /\ (euclidean__axioms.Col a G A))))) as H48.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (a) H12).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G A a) /\ ((euclidean__axioms.Col G a A) /\ ((euclidean__axioms.Col a A G) /\ ((euclidean__axioms.Col A a G) /\ (euclidean__axioms.Col a G A))))) as H49.
------------------------------------ exact H48.
------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col G a A) /\ ((euclidean__axioms.Col a A G) /\ ((euclidean__axioms.Col A a G) /\ (euclidean__axioms.Col a G A)))) as H51.
------------------------------------- exact H50.
------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col a A G) /\ ((euclidean__axioms.Col A a G) /\ (euclidean__axioms.Col a G A))) as H53.
-------------------------------------- exact H52.
-------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col A a G) /\ (euclidean__axioms.Col a G A)) as H55.
--------------------------------------- exact H54.
--------------------------------------- destruct H55 as [H55 H56].
exact H49.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq G A) as H49.
----------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (G) H8).
----------------------------------- assert (* Cut *) (euclidean__axioms.Col A B a) as H50.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col (A) (B) (a)).
-------------------------------------intro H50.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (a) (H50)).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (A) (B) (a) (H47) (H48) H49).


------------------------------------ assert (* Cut *) (euclidean__axioms.Col G A g) as H51.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G A g) /\ ((euclidean__axioms.Col G g A) /\ ((euclidean__axioms.Col g A G) /\ ((euclidean__axioms.Col A g G) /\ (euclidean__axioms.Col g G A))))) as H51.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (G) (g) H14).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col G A g) /\ ((euclidean__axioms.Col G g A) /\ ((euclidean__axioms.Col g A G) /\ ((euclidean__axioms.Col A g G) /\ (euclidean__axioms.Col g G A))))) as H52.
--------------------------------------- exact H51.
--------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col G g A) /\ ((euclidean__axioms.Col g A G) /\ ((euclidean__axioms.Col A g G) /\ (euclidean__axioms.Col g G A)))) as H54.
---------------------------------------- exact H53.
---------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col g A G) /\ ((euclidean__axioms.Col A g G) /\ (euclidean__axioms.Col g G A))) as H56.
----------------------------------------- exact H55.
----------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col A g G) /\ (euclidean__axioms.Col g G A)) as H58.
------------------------------------------ exact H57.
------------------------------------------ destruct H58 as [H58 H59].
exact H52.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B g) as H52.
-------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (B) (g)).
---------------------------------------intro H52.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (g) (H52)).
----------------------------------------apply (@lemma__collinear4.lemma__collinear4 (G) (A) (B) (g) (H47) (H51) H49).


-------------------------------------- assert (* Cut *) (euclidean__axioms.Col D H C) as H53.
--------------------------------------- right.
right.
right.
right.
left.
exact H36.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col H D C) as H54.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))))) as H54.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (H) (C) H53).
----------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))))) as H55.
------------------------------------------ exact H54.
------------------------------------------ destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D)))) as H57.
------------------------------------------- exact H56.
------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))) as H59.
-------------------------------------------- exact H58.
-------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D)) as H61.
--------------------------------------------- exact H60.
--------------------------------------------- destruct H61 as [H61 H62].
exact H55.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C h) as H55.
----------------------------------------- apply (@euclidean__tactics.not__nCol__Col (D) (C) (h)).
------------------------------------------intro H55.
apply (@euclidean__tactics.Col__nCol__False (D) (C) (h) (H55)).
-------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (H) (D) (C) (h) (H54) (H18) H10).


----------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D h) as H56.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C D h) /\ ((euclidean__axioms.Col C h D) /\ ((euclidean__axioms.Col h D C) /\ ((euclidean__axioms.Col D h C) /\ (euclidean__axioms.Col h C D))))) as H56.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (C) (h) H55).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C D h) /\ ((euclidean__axioms.Col C h D) /\ ((euclidean__axioms.Col h D C) /\ ((euclidean__axioms.Col D h C) /\ (euclidean__axioms.Col h C D))))) as H57.
-------------------------------------------- exact H56.
-------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col C h D) /\ ((euclidean__axioms.Col h D C) /\ ((euclidean__axioms.Col D h C) /\ (euclidean__axioms.Col h C D)))) as H59.
--------------------------------------------- exact H58.
--------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col h D C) /\ ((euclidean__axioms.Col D h C) /\ (euclidean__axioms.Col h C D))) as H61.
---------------------------------------------- exact H60.
---------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col D h C) /\ (euclidean__axioms.Col h C D)) as H63.
----------------------------------------------- exact H62.
----------------------------------------------- destruct H63 as [H63 H64].
exact H57.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D d C) as H57.
------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (D) (d) (C)).
--------------------------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False (D) (d) (C) (H57)).
---------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (H) (D) (d) (C) (H20) (H54) H10).


------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D d) as H58.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col d D C) /\ ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.Col D C d) /\ (euclidean__axioms.Col C d D))))) as H58.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (d) (C) H57).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col d D C) /\ ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.Col D C d) /\ (euclidean__axioms.Col C d D))))) as H59.
---------------------------------------------- exact H58.
---------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.Col D C d) /\ (euclidean__axioms.Col C d D)))) as H61.
----------------------------------------------- exact H60.
----------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.Col D C d) /\ (euclidean__axioms.Col C d D))) as H63.
------------------------------------------------ exact H62.
------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col D C d) /\ (euclidean__axioms.Col C d D)) as H65.
------------------------------------------------- exact H64.
------------------------------------------------- destruct H65 as [H65 H66].
exact H63.
-------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H59.
--------------------------------------------- intro H59.
assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.Col C D M)))) as H60.
---------------------------------------------- exact H59.
---------------------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.Col C D M))))) as H61.
----------------------------------------------- exact H60.
----------------------------------------------- destruct H61 as [M H61].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.Col C D M)))) as H62.
------------------------------------------------ exact H61.
------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.Col C D M))) as H64.
------------------------------------------------- exact H63.
------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.Col C D M)) as H66.
-------------------------------------------------- exact H65.
-------------------------------------------------- destruct H66 as [H66 H67].
assert (* Cut *) (euclidean__axioms.Col B A G) as H68.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G))))) as H68.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (G) (A) (B) H47).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G))))) as H69.
----------------------------------------------------- exact H68.
----------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G)))) as H71.
------------------------------------------------------ exact H70.
------------------------------------------------------ destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G))) as H73.
------------------------------------------------------- exact H72.
------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G)) as H75.
-------------------------------------------------------- exact H74.
-------------------------------------------------------- destruct H75 as [H75 H76].
exact H76.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A M) as H69.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A M) /\ ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A M B) /\ (euclidean__axioms.Col M B A))))) as H69.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (M) H66).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A M) /\ ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A M B) /\ (euclidean__axioms.Col M B A))))) as H70.
------------------------------------------------------ exact H69.
------------------------------------------------------ destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A M B) /\ (euclidean__axioms.Col M B A)))) as H72.
------------------------------------------------------- exact H71.
------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A M B) /\ (euclidean__axioms.Col M B A))) as H74.
-------------------------------------------------------- exact H73.
-------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col A M B) /\ (euclidean__axioms.Col M B A)) as H76.
--------------------------------------------------------- exact H75.
--------------------------------------------------------- destruct H76 as [H76 H77].
exact H70.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A G M) as H70.
----------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (G) (M)).
------------------------------------------------------intro H70.
apply (@euclidean__tactics.Col__nCol__False (A) (G) (M) (H70)).
-------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (G) (M) (H68) (H69) H43).


----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D H) as H71.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col D H C) /\ ((euclidean__axioms.Col D C H) /\ ((euclidean__axioms.Col C H D) /\ ((euclidean__axioms.Col H C D) /\ (euclidean__axioms.Col C D H))))) as H71.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (H) (D) (C) H54).
------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col D H C) /\ ((euclidean__axioms.Col D C H) /\ ((euclidean__axioms.Col C H D) /\ ((euclidean__axioms.Col H C D) /\ (euclidean__axioms.Col C D H))))) as H72.
-------------------------------------------------------- exact H71.
-------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col D C H) /\ ((euclidean__axioms.Col C H D) /\ ((euclidean__axioms.Col H C D) /\ (euclidean__axioms.Col C D H)))) as H74.
--------------------------------------------------------- exact H73.
--------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col C H D) /\ ((euclidean__axioms.Col H C D) /\ (euclidean__axioms.Col C D H))) as H76.
---------------------------------------------------------- exact H75.
---------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col H C D) /\ (euclidean__axioms.Col C D H)) as H78.
----------------------------------------------------------- exact H77.
----------------------------------------------------------- destruct H78 as [H78 H79].
exact H79.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D H M) as H72.
------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (D) (H) (M)).
--------------------------------------------------------intro H72.
apply (@euclidean__tactics.Col__nCol__False (D) (H) (M) (H72)).
---------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (D) (H) (M) (H71) (H67) H64).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H D M) as H73.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H D M) /\ ((euclidean__axioms.Col H M D) /\ ((euclidean__axioms.Col M D H) /\ ((euclidean__axioms.Col D M H) /\ (euclidean__axioms.Col M H D))))) as H73.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (D) (H) (M) H72).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col H D M) /\ ((euclidean__axioms.Col H M D) /\ ((euclidean__axioms.Col M D H) /\ ((euclidean__axioms.Col D M H) /\ (euclidean__axioms.Col M H D))))) as H74.
---------------------------------------------------------- exact H73.
---------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col H M D) /\ ((euclidean__axioms.Col M D H) /\ ((euclidean__axioms.Col D M H) /\ (euclidean__axioms.Col M H D)))) as H76.
----------------------------------------------------------- exact H75.
----------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col M D H) /\ ((euclidean__axioms.Col D M H) /\ (euclidean__axioms.Col M H D))) as H78.
------------------------------------------------------------ exact H77.
------------------------------------------------------------ destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col D M H) /\ (euclidean__axioms.Col M H D)) as H80.
------------------------------------------------------------- exact H79.
------------------------------------------------------------- destruct H80 as [H80 H81].
exact H74.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A G H D) as H74.
--------------------------------------------------------- exists M.
split.
---------------------------------------------------------- exact H8.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H10.
----------------------------------------------------------- split.
------------------------------------------------------------ exact H70.
------------------------------------------------------------ exact H73.
--------------------------------------------------------- apply (@H24 H74).
--------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H60.
---------------------------------------------- exists a.
exists g.
exists h.
exists d.
exists m.
split.
----------------------------------------------- exact H42.
----------------------------------------------- split.
------------------------------------------------ exact H45.
------------------------------------------------ split.
------------------------------------------------- exact H50.
------------------------------------------------- split.
-------------------------------------------------- exact H52.
-------------------------------------------------- split.
--------------------------------------------------- exact H16.
--------------------------------------------------- split.
---------------------------------------------------- exact H56.
---------------------------------------------------- split.
----------------------------------------------------- exact H58.
----------------------------------------------------- split.
------------------------------------------------------ exact H22.
------------------------------------------------------ split.
------------------------------------------------------- exact H59.
------------------------------------------------------- split.
-------------------------------------------------------- exact H26.
-------------------------------------------------------- exact H27.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C H D) as H61.
----------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (H) (C) H36).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E G H) as H62.
------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (H) (G) (E) H40).
------------------------------------------------ assert (* Cut *) ((euclidean__defs.CongA A G H G H D) /\ ((euclidean__defs.CongA E G B G H D) /\ (euclidean__defs.RT B G H G H D))) as H63.
------------------------------------------------- apply (@proposition__29.proposition__29 (A) (B) (C) (D) (E) (G) (H) (H60) (H32) (H61) (H62) H1).
------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA A G H G H D)).
--------------------------------------------------intro H64.
assert (* AndElim *) ((euclidean__defs.CongA A G H G H D) /\ ((euclidean__defs.CongA E G B G H D) /\ (euclidean__defs.RT B G H G H D))) as H65.
--------------------------------------------------- exact H63.
--------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__defs.CongA E G B G H D) /\ (euclidean__defs.RT B G H G H D)) as H67.
---------------------------------------------------- exact H66.
---------------------------------------------------- destruct H67 as [H67 H68].
assert (* Cut *) (False) as H69.
----------------------------------------------------- apply (@H64 H65).
----------------------------------------------------- assert False.
------------------------------------------------------exact H69.
------------------------------------------------------ contradiction.

Qed.
