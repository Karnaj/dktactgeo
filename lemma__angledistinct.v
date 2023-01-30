Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__equalanglessymmetric.
Require Export logic.
Definition lemma__angledistinct : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__defs.CongA A B C a b c) -> ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq b c) /\ (euclidean__axioms.neq a c)))))).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H0.
- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H0.
-- exact H.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as __TmpHyp.
--- exact H0.
--- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H1.
---- exact __TmpHyp.
---- destruct H1 as [x H1].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A x) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B x b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong x V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H2.
----- exact H1.
----- destruct H2 as [x0 H2].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out B A x) /\ ((euclidean__defs.Out B C x0) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B x b u) /\ ((euclidean__axioms.Cong B x0 b v) /\ ((euclidean__axioms.Cong x x0 u v) /\ (euclidean__axioms.nCol A B C))))))))) as H3.
------ exact H2.
------ destruct H3 as [x1 H3].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out B A x) /\ ((euclidean__defs.Out B C x0) /\ ((euclidean__defs.Out b a x1) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B x b x1) /\ ((euclidean__axioms.Cong B x0 b v) /\ ((euclidean__axioms.Cong x x0 x1 v) /\ (euclidean__axioms.nCol A B C))))))))) as H4.
------- exact H3.
------- destruct H4 as [x2 H4].
assert (* AndElim *) ((euclidean__defs.Out B A x) /\ ((euclidean__defs.Out B C x0) /\ ((euclidean__defs.Out b a x1) /\ ((euclidean__defs.Out b c x2) /\ ((euclidean__axioms.Cong B x b x1) /\ ((euclidean__axioms.Cong B x0 b x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol A B C)))))))) as H5.
-------- exact H4.
-------- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Out B C x0) /\ ((euclidean__defs.Out b a x1) /\ ((euclidean__defs.Out b c x2) /\ ((euclidean__axioms.Cong B x b x1) /\ ((euclidean__axioms.Cong B x0 b x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol A B C))))))) as H7.
--------- exact H6.
--------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Out b a x1) /\ ((euclidean__defs.Out b c x2) /\ ((euclidean__axioms.Cong B x b x1) /\ ((euclidean__axioms.Cong B x0 b x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol A B C)))))) as H9.
---------- exact H8.
---------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Out b c x2) /\ ((euclidean__axioms.Cong B x b x1) /\ ((euclidean__axioms.Cong B x0 b x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol A B C))))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Cong B x b x1) /\ ((euclidean__axioms.Cong B x0 b x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol A B C)))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Cong B x0 b x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol A B C))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol A B C)) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
exact H18.
- assert (* Cut *) (~(A = B)) as H1.
-- intro H1.
assert (* Cut *) (euclidean__axioms.Col A B C) as H2.
--- left.
exact H1.
--- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H0) H2).
-- assert (* Cut *) (~(B = C)) as H2.
--- intro H2.
assert (* Cut *) (euclidean__axioms.Col A B C) as H3.
---- right.
right.
left.
exact H2.
---- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H0) H3).
--- assert (* Cut *) (~(A = C)) as H3.
---- intro H3.
assert (* Cut *) (euclidean__axioms.Col A B C) as H4.
----- right.
left.
exact H3.
----- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H0) H4).
---- assert (* Cut *) (euclidean__defs.CongA a b c A B C) as H4.
----- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (a) (b) (c) H).
----- assert (* Cut *) (euclidean__axioms.nCol a b c) as H5.
------ assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out b a U) /\ ((euclidean__defs.Out b c V) /\ ((euclidean__defs.Out B A u) /\ ((euclidean__defs.Out B C v) /\ ((euclidean__axioms.Cong b U B u) /\ ((euclidean__axioms.Cong b V B v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol a b c)))))))) as H5.
------- exact H4.
------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out b a U) /\ ((euclidean__defs.Out b c V) /\ ((euclidean__defs.Out B A u) /\ ((euclidean__defs.Out B C v) /\ ((euclidean__axioms.Cong b U B u) /\ ((euclidean__axioms.Cong b V B v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol a b c)))))))) as __TmpHyp.
-------- exact H5.
-------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out b a U) /\ ((euclidean__defs.Out b c V) /\ ((euclidean__defs.Out B A u) /\ ((euclidean__defs.Out B C v) /\ ((euclidean__axioms.Cong b U B u) /\ ((euclidean__axioms.Cong b V B v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol a b c))))))))) as H6.
--------- exact __TmpHyp.
--------- destruct H6 as [x H6].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out b a x) /\ ((euclidean__defs.Out b c V) /\ ((euclidean__defs.Out B A u) /\ ((euclidean__defs.Out B C v) /\ ((euclidean__axioms.Cong b x B u) /\ ((euclidean__axioms.Cong b V B v) /\ ((euclidean__axioms.Cong x V u v) /\ (euclidean__axioms.nCol a b c))))))))) as H7.
---------- exact H6.
---------- destruct H7 as [x0 H7].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out b a x) /\ ((euclidean__defs.Out b c x0) /\ ((euclidean__defs.Out B A u) /\ ((euclidean__defs.Out B C v) /\ ((euclidean__axioms.Cong b x B u) /\ ((euclidean__axioms.Cong b x0 B v) /\ ((euclidean__axioms.Cong x x0 u v) /\ (euclidean__axioms.nCol a b c))))))))) as H8.
----------- exact H7.
----------- destruct H8 as [x1 H8].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out b a x) /\ ((euclidean__defs.Out b c x0) /\ ((euclidean__defs.Out B A x1) /\ ((euclidean__defs.Out B C v) /\ ((euclidean__axioms.Cong b x B x1) /\ ((euclidean__axioms.Cong b x0 B v) /\ ((euclidean__axioms.Cong x x0 x1 v) /\ (euclidean__axioms.nCol a b c))))))))) as H9.
------------ exact H8.
------------ destruct H9 as [x2 H9].
assert (* AndElim *) ((euclidean__defs.Out b a x) /\ ((euclidean__defs.Out b c x0) /\ ((euclidean__defs.Out B A x1) /\ ((euclidean__defs.Out B C x2) /\ ((euclidean__axioms.Cong b x B x1) /\ ((euclidean__axioms.Cong b x0 B x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol a b c)))))))) as H10.
------------- exact H9.
------------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.Out b c x0) /\ ((euclidean__defs.Out B A x1) /\ ((euclidean__defs.Out B C x2) /\ ((euclidean__axioms.Cong b x B x1) /\ ((euclidean__axioms.Cong b x0 B x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol a b c))))))) as H12.
-------------- exact H11.
-------------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.Out B A x1) /\ ((euclidean__defs.Out B C x2) /\ ((euclidean__axioms.Cong b x B x1) /\ ((euclidean__axioms.Cong b x0 B x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol a b c)))))) as H14.
--------------- exact H13.
--------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__defs.Out B C x2) /\ ((euclidean__axioms.Cong b x B x1) /\ ((euclidean__axioms.Cong b x0 B x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol a b c))))) as H16.
---------------- exact H15.
---------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong b x B x1) /\ ((euclidean__axioms.Cong b x0 B x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol a b c)))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Cong b x0 B x2) /\ ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol a b c))) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Cong x x0 x1 x2) /\ (euclidean__axioms.nCol a b c)) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H24.
-------------------- exact H.
-------------------- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as __TmpHyp0.
--------------------- exact H24.
--------------------- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H25.
---------------------- exact __TmpHyp0.
---------------------- destruct H25 as [x3 H25].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A x3) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B x3 b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong x3 V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H26.
----------------------- exact H25.
----------------------- destruct H26 as [x4 H26].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out B A x3) /\ ((euclidean__defs.Out B C x4) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B x3 b u) /\ ((euclidean__axioms.Cong B x4 b v) /\ ((euclidean__axioms.Cong x3 x4 u v) /\ (euclidean__axioms.nCol A B C))))))))) as H27.
------------------------ exact H26.
------------------------ destruct H27 as [x5 H27].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out B A x3) /\ ((euclidean__defs.Out B C x4) /\ ((euclidean__defs.Out b a x5) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B x3 b x5) /\ ((euclidean__axioms.Cong B x4 b v) /\ ((euclidean__axioms.Cong x3 x4 x5 v) /\ (euclidean__axioms.nCol A B C))))))))) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [x6 H28].
assert (* AndElim *) ((euclidean__defs.Out B A x3) /\ ((euclidean__defs.Out B C x4) /\ ((euclidean__defs.Out b a x5) /\ ((euclidean__defs.Out b c x6) /\ ((euclidean__axioms.Cong B x3 b x5) /\ ((euclidean__axioms.Cong B x4 b x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A B C)))))))) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__defs.Out B C x4) /\ ((euclidean__defs.Out b a x5) /\ ((euclidean__defs.Out b c x6) /\ ((euclidean__axioms.Cong B x3 b x5) /\ ((euclidean__axioms.Cong B x4 b x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A B C))))))) as H31.
--------------------------- exact H30.
--------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__defs.Out b a x5) /\ ((euclidean__defs.Out b c x6) /\ ((euclidean__axioms.Cong B x3 b x5) /\ ((euclidean__axioms.Cong B x4 b x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A B C)))))) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__defs.Out b c x6) /\ ((euclidean__axioms.Cong B x3 b x5) /\ ((euclidean__axioms.Cong B x4 b x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A B C))))) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Cong B x3 b x5) /\ ((euclidean__axioms.Cong B x4 b x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A B C)))) as H37.
------------------------------ exact H36.
------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Cong B x4 b x6) /\ ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A B C))) as H39.
------------------------------- exact H38.
------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Cong x3 x4 x5 x6) /\ (euclidean__axioms.nCol A B C)) as H41.
-------------------------------- exact H40.
-------------------------------- destruct H41 as [H41 H42].
exact H23.
------ assert (* Cut *) (~(a = b)) as H6.
------- intro H6.
assert (* Cut *) (euclidean__axioms.Col a b c) as H7.
-------- left.
exact H6.
-------- apply (@euclidean__tactics.Col__nCol__False (a) (b) (c) (H5) H7).
------- assert (* Cut *) (~(b = c)) as H7.
-------- intro H7.
assert (* Cut *) (euclidean__axioms.Col a b c) as H8.
--------- right.
right.
left.
exact H7.
--------- apply (@euclidean__tactics.Col__nCol__False (a) (b) (c) (H5) H8).
-------- assert (* Cut *) (~(a = c)) as H8.
--------- intro H8.
assert (* Cut *) (euclidean__axioms.Col a b c) as H9.
---------- right.
left.
exact H8.
---------- apply (@euclidean__tactics.Col__nCol__False (a) (b) (c) (H5) H9).
--------- split.
---------- exact H1.
---------- split.
----------- exact H2.
----------- split.
------------ exact H3.
------------ split.
------------- exact H6.
------------- split.
-------------- exact H7.
-------------- exact H8.
Qed.
