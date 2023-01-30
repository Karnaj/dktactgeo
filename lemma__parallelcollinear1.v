Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__parallelcollinear1 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point), (euclidean__defs.TP A B c d) -> ((euclidean__axioms.BetS C c d) -> (euclidean__defs.TP A B C d)).
Proof.
intro A.
intro B.
intro C.
intro c.
intro d.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.Col C c d) as H1.
- right.
right.
right.
right.
left.
exact H0.
- assert (* Cut *) (euclidean__axioms.neq C c) as H2.
-- assert (* Cut *) ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq C d))) as H2.
--- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (c) (d) H0).
--- assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq C d))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq C d)) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
exact H5.
-- assert (* Cut *) (euclidean__axioms.neq c d) as H3.
--- assert (* Cut *) ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq C d))) as H3.
---- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (c) (d) H0).
---- assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq C d))) as H4.
----- exact H3.
----- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq C d)) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
exact H4.
--- assert (* Cut *) (euclidean__axioms.neq C d) as H4.
---- assert (* Cut *) ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq C d))) as H4.
----- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (c) (d) H0).
----- assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq C d))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq C d)) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
exact H8.
---- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)))) as H5.
----- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)))) as H5.
------ exact H.
------ assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)))) as __TmpHyp.
------- exact H5.
------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)))) as H6.
-------- exact __TmpHyp.
-------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
split.
----------- exact H6.
----------- split.
------------ exact H8.
------------ split.
------------- exact H10.
------------- exact H11.
----- assert (* Cut *) (exists (p: euclidean__axioms.Point) (q: euclidean__axioms.Point) (r: euclidean__axioms.Point), (euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.BetS c p q) /\ ((euclidean__axioms.BetS d r q) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d)))))) as H6.
------ assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS c U X) /\ ((euclidean__axioms.BetS d V X) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))))) as H6.
------- exact H5.
------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS c U X) /\ ((euclidean__axioms.BetS d V X) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))))) as __TmpHyp.
-------- exact H6.
-------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS c U X) /\ ((euclidean__axioms.BetS d V X) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))))) as H7.
--------- exact __TmpHyp.
--------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS c U X) /\ ((euclidean__axioms.BetS d V X) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d)))))))) as H9.
---------- exact H8.
---------- destruct H9 as [H9 H10].
assert (* AndElim *) ((~(euclidean__defs.Meet A B c d)) /\ (exists (X: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS c U X) /\ ((euclidean__axioms.BetS d V X) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (exists X: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS c U X) /\ ((euclidean__axioms.BetS d V X) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))) as H13.
------------ exact H12.
------------ destruct H13 as [x H13].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS c U x) /\ ((euclidean__axioms.BetS d V x) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))) as H14.
------------- exact H13.
------------- destruct H14 as [x0 H14].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS c x0 x) /\ ((euclidean__axioms.BetS d V x) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))) as H15.
-------------- exact H14.
-------------- destruct H15 as [x1 H15].
assert (* AndElim *) ((euclidean__axioms.Col A B x0) /\ ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.BetS c x0 x) /\ ((euclidean__axioms.BetS d x1 x) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d)))))) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col A B x1) /\ ((euclidean__axioms.BetS c x0 x) /\ ((euclidean__axioms.BetS d x1 x) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.BetS c x0 x) /\ ((euclidean__axioms.BetS d x1 x) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d)))) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.BetS d x1 x) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d)) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
exists x0.
exists x.
exists x1.
split.
-------------------- exact H16.
-------------------- split.
--------------------- exact H18.
--------------------- split.
---------------------- exact H20.
---------------------- split.
----------------------- exact H22.
----------------------- split.
------------------------ exact H24.
------------------------ exact H25.
------ assert (exists p: euclidean__axioms.Point, (exists (q: euclidean__axioms.Point) (r: euclidean__axioms.Point), (euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.BetS c p q) /\ ((euclidean__axioms.BetS d r q) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))) as H7.
------- exact H6.
------- destruct H7 as [p H7].
assert (exists q: euclidean__axioms.Point, (exists (r: euclidean__axioms.Point), (euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.BetS c p q) /\ ((euclidean__axioms.BetS d r q) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))) as H8.
-------- exact H7.
-------- destruct H8 as [q H8].
assert (exists r: euclidean__axioms.Point, ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.BetS c p q) /\ ((euclidean__axioms.BetS d r q) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))))) as H9.
--------- exact H8.
--------- destruct H9 as [r H9].
assert (* AndElim *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.BetS c p q) /\ ((euclidean__axioms.BetS d r q) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d)))))) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.BetS c p q) /\ ((euclidean__axioms.BetS d r q) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))))) as H12.
----------- exact H11.
----------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.BetS c p q) /\ ((euclidean__axioms.BetS d r q) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d)))) as H14.
------------ exact H13.
------------ destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.BetS d r q) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d))) as H16.
------------- exact H15.
------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol A B d)) as H18.
-------------- exact H17.
-------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)))) as H20.
--------------- exact H5.
--------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B))) as H22.
---------------- exact H21.
---------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((~(euclidean__defs.Meet A B c d)) /\ (euclidean__defs.OS c d A B)) as H24.
----------------- exact H23.
----------------- destruct H24 as [H24 H25].
assert (* Cut *) (euclidean__axioms.BetS q r d) as H26.
------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (d) (r) (q) H16).
------------------ assert (* Cut *) (euclidean__axioms.Col C c d) as H27.
------------------- exact H1.
------------------- assert (* Cut *) (euclidean__axioms.Col c d C) as H28.
-------------------- assert (* Cut *) ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))))) as H28.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (c) (d) H27).
--------------------- assert (* AndElim *) ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))))) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C)))) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))) as H33.
------------------------ exact H32.
------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C)) as H35.
------------------------- exact H34.
------------------------- destruct H35 as [H35 H36].
exact H31.
-------------------- assert (* Cut *) (euclidean__axioms.BetS d c C) as H29.
--------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (c) (d) H0).
--------------------- assert (* Cut *) (euclidean__axioms.BetS q p c) as H30.
---------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (c) (p) (q) H14).
---------------------- assert (* Cut *) (~(p = r)) as H31.
----------------------- intro H31.
assert (* Cut *) (euclidean__axioms.Col q r d) as H32.
------------------------ right.
right.
right.
right.
left.
exact H26.
------------------------ assert (* Cut *) (euclidean__axioms.Col q p c) as H33.
------------------------- right.
right.
right.
right.
left.
exact H30.
------------------------- assert (* Cut *) (euclidean__axioms.Col q p d) as H34.
-------------------------- apply (@eq__ind__r euclidean__axioms.Point r (fun p0: euclidean__axioms.Point => (euclidean__axioms.Col A B p0) -> ((euclidean__axioms.BetS c p0 q) -> ((euclidean__axioms.BetS q p0 c) -> ((euclidean__axioms.Col q p0 c) -> (euclidean__axioms.Col q p0 d)))))) with (x := p).
---------------------------intro H34.
intro H35.
intro H36.
intro H37.
exact H32.

--------------------------- exact H31.
--------------------------- exact H10.
--------------------------- exact H14.
--------------------------- exact H30.
--------------------------- exact H33.
-------------------------- assert (* Cut *) (euclidean__axioms.neq q p) as H35.
--------------------------- assert (* Cut *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c))) as H35.
---------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (q) (p) (c) H30).
---------------------------- assert (* AndElim *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c))) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c)) as H38.
------------------------------ exact H37.
------------------------------ destruct H38 as [H38 H39].
exact H38.
--------------------------- assert (* Cut *) (euclidean__axioms.Col p c d) as H36.
---------------------------- apply (@euclidean__tactics.not__nCol__Col (p) (c) (d)).
-----------------------------intro H36.
apply (@euclidean__tactics.Col__nCol__False (p) (c) (d) (H36)).
------------------------------apply (@lemma__collinear4.lemma__collinear4 (q) (p) (c) (d) (H33) (H34) H35).


---------------------------- assert (* Cut *) (euclidean__axioms.Col c d p) as H37.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col c p d) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p d c) /\ (euclidean__axioms.Col d c p))))) as H37.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (p) (c) (d) H36).
------------------------------ assert (* AndElim *) ((euclidean__axioms.Col c p d) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p d c) /\ (euclidean__axioms.Col d c p))))) as H38.
------------------------------- exact H37.
------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p d c) /\ (euclidean__axioms.Col d c p)))) as H40.
-------------------------------- exact H39.
-------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p d c) /\ (euclidean__axioms.Col d c p))) as H42.
--------------------------------- exact H41.
--------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col p d c) /\ (euclidean__axioms.Col d c p)) as H44.
---------------------------------- exact H43.
---------------------------------- destruct H44 as [H44 H45].
exact H40.
----------------------------- assert (* Cut *) (euclidean__defs.Meet A B c d) as H38.
------------------------------ exists p.
split.
------------------------------- exact H20.
------------------------------- split.
-------------------------------- exact H22.
-------------------------------- split.
--------------------------------- exact H10.
--------------------------------- exact H37.
------------------------------ apply (@H24 H38).
----------------------- assert (* Cut *) (euclidean__axioms.Col q p c) as H32.
------------------------ right.
right.
right.
right.
left.
exact H30.
------------------------ assert (* Cut *) (~(euclidean__axioms.Col q d C)) as H33.
------------------------- intro H33.
assert (* Cut *) (euclidean__axioms.Col d c C) as H34.
-------------------------- right.
right.
right.
right.
left.
exact H29.
-------------------------- assert (* Cut *) (euclidean__axioms.Col C d c) as H35.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col C d c) /\ ((euclidean__axioms.Col d C c) /\ (euclidean__axioms.Col C c d))))) as H35.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder (d) (c) (C) H34).
---------------------------- assert (* AndElim *) ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col C d c) /\ ((euclidean__axioms.Col d C c) /\ (euclidean__axioms.Col C c d))))) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col C d c) /\ ((euclidean__axioms.Col d C c) /\ (euclidean__axioms.Col C c d)))) as H38.
------------------------------ exact H37.
------------------------------ destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col C d c) /\ ((euclidean__axioms.Col d C c) /\ (euclidean__axioms.Col C c d))) as H40.
------------------------------- exact H39.
------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col d C c) /\ (euclidean__axioms.Col C c d)) as H42.
-------------------------------- exact H41.
-------------------------------- destruct H42 as [H42 H43].
exact H40.
--------------------------- assert (* Cut *) (euclidean__axioms.Col C d q) as H36.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col d q C) /\ ((euclidean__axioms.Col d C q) /\ ((euclidean__axioms.Col C q d) /\ ((euclidean__axioms.Col q C d) /\ (euclidean__axioms.Col C d q))))) as H36.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder (q) (d) (C) H33).
----------------------------- assert (* AndElim *) ((euclidean__axioms.Col d q C) /\ ((euclidean__axioms.Col d C q) /\ ((euclidean__axioms.Col C q d) /\ ((euclidean__axioms.Col q C d) /\ (euclidean__axioms.Col C d q))))) as H37.
------------------------------ exact H36.
------------------------------ destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col d C q) /\ ((euclidean__axioms.Col C q d) /\ ((euclidean__axioms.Col q C d) /\ (euclidean__axioms.Col C d q)))) as H39.
------------------------------- exact H38.
------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col C q d) /\ ((euclidean__axioms.Col q C d) /\ (euclidean__axioms.Col C d q))) as H41.
-------------------------------- exact H40.
-------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col q C d) /\ (euclidean__axioms.Col C d q)) as H43.
--------------------------------- exact H42.
--------------------------------- destruct H43 as [H43 H44].
exact H44.
---------------------------- assert (* Cut *) (euclidean__axioms.neq C d) as H37.
----------------------------- assert (* Cut *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c))) as H37.
------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (q) (p) (c) H30).
------------------------------ assert (* AndElim *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c))) as H38.
------------------------------- exact H37.
------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c)) as H40.
-------------------------------- exact H39.
-------------------------------- destruct H40 as [H40 H41].
exact H4.
----------------------------- assert (* Cut *) (euclidean__axioms.Col d c q) as H38.
------------------------------ apply (@euclidean__tactics.not__nCol__Col (d) (c) (q)).
-------------------------------intro H38.
apply (@euclidean__tactics.Col__nCol__False (d) (c) (q) (H38)).
--------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (d) (c) (q) (H35) (H36) H37).


------------------------------ assert (* Cut *) (euclidean__axioms.Col c q d) as H39.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.Col c q d) /\ ((euclidean__axioms.Col q d c) /\ ((euclidean__axioms.Col d q c) /\ (euclidean__axioms.Col q c d))))) as H39.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (d) (c) (q) H38).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.Col c q d) /\ ((euclidean__axioms.Col q d c) /\ ((euclidean__axioms.Col d q c) /\ (euclidean__axioms.Col q c d))))) as H40.
--------------------------------- exact H39.
--------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col c q d) /\ ((euclidean__axioms.Col q d c) /\ ((euclidean__axioms.Col d q c) /\ (euclidean__axioms.Col q c d)))) as H42.
---------------------------------- exact H41.
---------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col q d c) /\ ((euclidean__axioms.Col d q c) /\ (euclidean__axioms.Col q c d))) as H44.
----------------------------------- exact H43.
----------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col d q c) /\ (euclidean__axioms.Col q c d)) as H46.
------------------------------------ exact H45.
------------------------------------ destruct H46 as [H46 H47].
exact H42.
------------------------------- assert (* Cut *) (euclidean__axioms.Col c q p) as H40.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col p q c) /\ ((euclidean__axioms.Col p c q) /\ ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q))))) as H40.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (q) (p) (c) H32).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p q c) /\ ((euclidean__axioms.Col p c q) /\ ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q))))) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col p c q) /\ ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q)))) as H43.
----------------------------------- exact H42.
----------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q))) as H45.
------------------------------------ exact H44.
------------------------------------ destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q)) as H47.
------------------------------------- exact H46.
------------------------------------- destruct H47 as [H47 H48].
exact H45.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq q c) as H41.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c))) as H41.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (q) (p) (c) H30).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c))) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c)) as H44.
------------------------------------ exact H43.
------------------------------------ destruct H44 as [H44 H45].
exact H45.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq c q) as H42.
---------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (q) (c) H41).
---------------------------------- assert (* Cut *) (euclidean__axioms.Col q d p) as H43.
----------------------------------- apply (@euclidean__tactics.not__nCol__Col (q) (d) (p)).
------------------------------------intro H43.
apply (@euclidean__tactics.Col__nCol__False (q) (d) (p) (H43)).
-------------------------------------apply (@lemma__collinear4.lemma__collinear4 (c) (q) (d) (p) (H39) (H40) H42).


----------------------------------- assert (* Cut *) (euclidean__axioms.Col q r d) as H44.
------------------------------------ right.
right.
right.
right.
left.
exact H26.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col q d r) as H45.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col r q d) /\ ((euclidean__axioms.Col r d q) /\ ((euclidean__axioms.Col d q r) /\ ((euclidean__axioms.Col q d r) /\ (euclidean__axioms.Col d r q))))) as H45.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (q) (r) (d) H44).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col r q d) /\ ((euclidean__axioms.Col r d q) /\ ((euclidean__axioms.Col d q r) /\ ((euclidean__axioms.Col q d r) /\ (euclidean__axioms.Col d r q))))) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col r d q) /\ ((euclidean__axioms.Col d q r) /\ ((euclidean__axioms.Col q d r) /\ (euclidean__axioms.Col d r q)))) as H48.
---------------------------------------- exact H47.
---------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col d q r) /\ ((euclidean__axioms.Col q d r) /\ (euclidean__axioms.Col d r q))) as H50.
----------------------------------------- exact H49.
----------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col q d r) /\ (euclidean__axioms.Col d r q)) as H52.
------------------------------------------ exact H51.
------------------------------------------ destruct H52 as [H52 H53].
exact H52.
------------------------------------- assert (* Cut *) (euclidean__axioms.neq q d) as H46.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.neq r d) /\ ((euclidean__axioms.neq q r) /\ (euclidean__axioms.neq q d))) as H46.
--------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (q) (r) (d) H26).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq r d) /\ ((euclidean__axioms.neq q r) /\ (euclidean__axioms.neq q d))) as H47.
---------------------------------------- exact H46.
---------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq q r) /\ (euclidean__axioms.neq q d)) as H49.
----------------------------------------- exact H48.
----------------------------------------- destruct H49 as [H49 H50].
exact H50.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col d p r) as H47.
--------------------------------------- apply (@euclidean__tactics.not__nCol__Col (d) (p) (r)).
----------------------------------------intro H47.
apply (@euclidean__tactics.Col__nCol__False (d) (p) (r) (H47)).
-----------------------------------------apply (@lemma__collinear4.lemma__collinear4 (q) (d) (p) (r) (H43) (H45) H46).


--------------------------------------- assert (* Cut *) (euclidean__axioms.Col B p r) as H48.
---------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (p) (r)).
-----------------------------------------intro H48.
apply (@euclidean__tactics.Col__nCol__False (B) (p) (r) (H48)).
------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (p) (r) (H10) (H12) H20).


---------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A p) as H49.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A p) /\ ((euclidean__axioms.Col B p A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A))))) as H49.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (p) H10).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col B A p) /\ ((euclidean__axioms.Col B p A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A))))) as H50.
------------------------------------------- exact H49.
------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col B p A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A)))) as H52.
-------------------------------------------- exact H51.
-------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A))) as H54.
--------------------------------------------- exact H53.
--------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A)) as H56.
---------------------------------------------- exact H55.
---------------------------------------------- destruct H56 as [H56 H57].
exact H50.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col B p A) as H50.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A p B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B))))) as H50.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (p) H49).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A p B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B))))) as H51.
-------------------------------------------- exact H50.
-------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col A p B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B)))) as H53.
--------------------------------------------- exact H52.
--------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B))) as H55.
---------------------------------------------- exact H54.
---------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B)) as H57.
----------------------------------------------- exact H56.
----------------------------------------------- destruct H57 as [H57 H58].
exact H57.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B A r) as H51.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A r) /\ ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A))))) as H51.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (r) H12).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A r) /\ ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A))))) as H52.
--------------------------------------------- exact H51.
--------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A)))) as H54.
---------------------------------------------- exact H53.
---------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A))) as H56.
----------------------------------------------- exact H55.
----------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A)) as H58.
------------------------------------------------ exact H57.
------------------------------------------------ destruct H58 as [H58 H59].
exact H52.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H52.
-------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H20).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A p r) as H53.
--------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (p) (r)).
----------------------------------------------intro H53.
apply (@euclidean__tactics.Col__nCol__False (A) (p) (r) (H53)).
-----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (p) (r) (H49) (H51) H52).


--------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq B p)) as H54.
---------------------------------------------- intro H54.
assert (* Cut *) (euclidean__axioms.Col p r A) as H55.
----------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (p) (r) (A)).
------------------------------------------------intro H55.
apply (@euclidean__tactics.Col__nCol__False (p) (r) (A) (H55)).
-------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (p) (r) (A) (H48) (H50) H54).


----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p r d) as H56.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col p d r) /\ ((euclidean__axioms.Col p r d) /\ ((euclidean__axioms.Col r d p) /\ ((euclidean__axioms.Col d r p) /\ (euclidean__axioms.Col r p d))))) as H56.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (d) (p) (r) H47).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p d r) /\ ((euclidean__axioms.Col p r d) /\ ((euclidean__axioms.Col r d p) /\ ((euclidean__axioms.Col d r p) /\ (euclidean__axioms.Col r p d))))) as H57.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col p r d) /\ ((euclidean__axioms.Col r d p) /\ ((euclidean__axioms.Col d r p) /\ (euclidean__axioms.Col r p d)))) as H59.
--------------------------------------------------- exact H58.
--------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col r d p) /\ ((euclidean__axioms.Col d r p) /\ (euclidean__axioms.Col r p d))) as H61.
---------------------------------------------------- exact H60.
---------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col d r p) /\ (euclidean__axioms.Col r p d)) as H63.
----------------------------------------------------- exact H62.
----------------------------------------------------- destruct H63 as [H63 H64].
exact H59.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col r A d) as H57.
------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (r) (A) (d)).
--------------------------------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False (r) (A) (d) (H57)).
---------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (p) (r) (A) (d) (H55) (H56) H31).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r A B) as H58.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))))) as H58.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (r) H51).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))))) as H59.
---------------------------------------------------- exact H58.
---------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B)))) as H61.
----------------------------------------------------- exact H60.
----------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))) as H63.
------------------------------------------------------ exact H62.
------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B)) as H65.
------------------------------------------------------- exact H64.
------------------------------------------------------- destruct H65 as [H65 H66].
exact H66.
-------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq r A)) as H59.
--------------------------------------------------- intro H59.
assert (* Cut *) (euclidean__axioms.Col A d B) as H60.
---------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (d) (B)).
-----------------------------------------------------intro H60.
apply (@euclidean__tactics.Col__nCol__False (A) (d) (B) (H60)).
------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (r) (A) (d) (B) (H57) (H58) H59).


---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B d) as H61.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col d A B) /\ ((euclidean__axioms.Col d B A) /\ ((euclidean__axioms.Col B A d) /\ ((euclidean__axioms.Col A B d) /\ (euclidean__axioms.Col B d A))))) as H61.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (d) (B) H60).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col d A B) /\ ((euclidean__axioms.Col d B A) /\ ((euclidean__axioms.Col B A d) /\ ((euclidean__axioms.Col A B d) /\ (euclidean__axioms.Col B d A))))) as H62.
------------------------------------------------------- exact H61.
------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col d B A) /\ ((euclidean__axioms.Col B A d) /\ ((euclidean__axioms.Col A B d) /\ (euclidean__axioms.Col B d A)))) as H64.
-------------------------------------------------------- exact H63.
-------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col B A d) /\ ((euclidean__axioms.Col A B d) /\ (euclidean__axioms.Col B d A))) as H66.
--------------------------------------------------------- exact H65.
--------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col A B d) /\ (euclidean__axioms.Col B d A)) as H68.
---------------------------------------------------------- exact H67.
---------------------------------------------------------- destruct H68 as [H68 H69].
exact H68.
----------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (d) (H19) H61).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p A d) as H60.
---------------------------------------------------- apply (@eq__ind euclidean__axioms.Point r (fun X: euclidean__axioms.Point => euclidean__axioms.Col p X d)) with (y := A).
----------------------------------------------------- exact H56.
-----------------------------------------------------apply (@euclidean__tactics.NNPP (r = A) H59).

---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p A B) as H61.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B))))) as H61.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (p) (A) H50).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B))))) as H62.
------------------------------------------------------- exact H61.
------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B)))) as H64.
-------------------------------------------------------- exact H63.
-------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B))) as H66.
--------------------------------------------------------- exact H65.
--------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B)) as H68.
---------------------------------------------------------- exact H67.
---------------------------------------------------------- destruct H68 as [H68 H69].
exact H64.
----------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq p A)) as H62.
------------------------------------------------------ intro H62.
assert (* Cut *) (euclidean__axioms.Col A d B) as H63.
------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (d) (B)).
--------------------------------------------------------intro H63.
apply (@euclidean__tactics.Col__nCol__False (A) (d) (B) (H63)).
---------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (p) (A) (d) (B) (H60) (H61) H62).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B d) as H64.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col d A B) /\ ((euclidean__axioms.Col d B A) /\ ((euclidean__axioms.Col B A d) /\ ((euclidean__axioms.Col A B d) /\ (euclidean__axioms.Col B d A))))) as H64.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (d) (B) H63).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col d A B) /\ ((euclidean__axioms.Col d B A) /\ ((euclidean__axioms.Col B A d) /\ ((euclidean__axioms.Col A B d) /\ (euclidean__axioms.Col B d A))))) as H65.
---------------------------------------------------------- exact H64.
---------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col d B A) /\ ((euclidean__axioms.Col B A d) /\ ((euclidean__axioms.Col A B d) /\ (euclidean__axioms.Col B d A)))) as H67.
----------------------------------------------------------- exact H66.
----------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col B A d) /\ ((euclidean__axioms.Col A B d) /\ (euclidean__axioms.Col B d A))) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col A B d) /\ (euclidean__axioms.Col B d A)) as H71.
------------------------------------------------------------- exact H70.
------------------------------------------------------------- destruct H71 as [H71 H72].
exact H71.
-------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (d) (H19) H64).
------------------------------------------------------ assert (* Cut *) (A = p) as H63.
------------------------------------------------------- assert (* Cut *) (p = A) as H63.
-------------------------------------------------------- apply (@euclidean__tactics.NNPP (p = A) H62).
-------------------------------------------------------- assert (* Cut *) (r = A) as H64.
--------------------------------------------------------- apply (@euclidean__tactics.NNPP (r = A) H59).
--------------------------------------------------------- apply (@logic.eq__sym (Point) (p) (A) H63).
------------------------------------------------------- assert (* Cut *) (r = p) as H64.
-------------------------------------------------------- assert (* Cut *) (p = A) as H64.
--------------------------------------------------------- apply (@euclidean__tactics.NNPP (p = A) H62).
--------------------------------------------------------- assert (* Cut *) (r = A) as H65.
---------------------------------------------------------- apply (@euclidean__tactics.NNPP (r = A) H59).
---------------------------------------------------------- apply (@logic.eq__trans (Point) (r) (A) (p) (H65) H63).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q p d) as H65.
--------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point p (fun r0: euclidean__axioms.Point => (euclidean__axioms.Col A B r0) -> ((euclidean__axioms.BetS d r0 q) -> ((euclidean__axioms.BetS q r0 d) -> ((~(p = r0)) -> ((euclidean__axioms.Col q r0 d) -> ((euclidean__axioms.Col q d r0) -> ((euclidean__axioms.Col d p r0) -> ((euclidean__axioms.Col B p r0) -> ((euclidean__axioms.Col B A r0) -> ((euclidean__axioms.Col A p r0) -> ((euclidean__axioms.Col p r0 A) -> ((euclidean__axioms.Col p r0 d) -> ((euclidean__axioms.Col r0 A d) -> ((euclidean__axioms.Col r0 A B) -> ((~(euclidean__axioms.neq r0 A)) -> (euclidean__axioms.Col q p d))))))))))))))))) with (x := r).
----------------------------------------------------------intro H65.
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
apply (@eq__ind__r euclidean__axioms.Point p (fun A0: euclidean__axioms.Point => (euclidean__defs.TP A0 B c d) -> ((euclidean__axioms.neq A0 B) -> ((~(euclidean__defs.Meet A0 B c d)) -> ((euclidean__defs.OS c d A0 B) -> ((euclidean__axioms.Col A0 B p) -> ((euclidean__axioms.Col A0 B p) -> ((euclidean__axioms.nCol A0 B c) -> ((euclidean__axioms.nCol A0 B d) -> ((euclidean__axioms.Col B A0 p) -> ((euclidean__axioms.Col B p A0) -> ((euclidean__axioms.Col B A0 p) -> ((euclidean__axioms.neq B A0) -> ((euclidean__axioms.Col A0 p p) -> ((~(euclidean__axioms.neq p A0)) -> ((euclidean__axioms.Col p A0 B) -> ((euclidean__axioms.Col p A0 d) -> ((euclidean__axioms.Col p p A0) -> ((euclidean__axioms.Col p A0 d) -> ((euclidean__axioms.Col p A0 B) -> ((~(euclidean__axioms.neq p A0)) -> (euclidean__axioms.Col q p d)))))))))))))))))))))) with (x := A).
-----------------------------------------------------------intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
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
exact H69.

----------------------------------------------------------- exact H63.
----------------------------------------------------------- exact H.
----------------------------------------------------------- exact H20.
----------------------------------------------------------- exact H24.
----------------------------------------------------------- exact H25.
----------------------------------------------------------- exact H10.
----------------------------------------------------------- exact H65.
----------------------------------------------------------- exact H18.
----------------------------------------------------------- exact H19.
----------------------------------------------------------- exact H49.
----------------------------------------------------------- exact H50.
----------------------------------------------------------- exact H73.
----------------------------------------------------------- exact H52.
----------------------------------------------------------- exact H74.
----------------------------------------------------------- exact H79.
----------------------------------------------------------- exact H78.
----------------------------------------------------------- exact H77.
----------------------------------------------------------- exact H75.
----------------------------------------------------------- exact H60.
----------------------------------------------------------- exact H61.
----------------------------------------------------------- exact H62.

---------------------------------------------------------- exact H64.
---------------------------------------------------------- exact H12.
---------------------------------------------------------- exact H16.
---------------------------------------------------------- exact H26.
---------------------------------------------------------- exact H31.
---------------------------------------------------------- exact H44.
---------------------------------------------------------- exact H45.
---------------------------------------------------------- exact H47.
---------------------------------------------------------- exact H48.
---------------------------------------------------------- exact H51.
---------------------------------------------------------- exact H53.
---------------------------------------------------------- exact H55.
---------------------------------------------------------- exact H56.
---------------------------------------------------------- exact H57.
---------------------------------------------------------- exact H58.
---------------------------------------------------------- exact H59.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq q p) as H66.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c))) as H66.
----------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (q) (p) (c) H30).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq p c) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c))) as H67.
------------------------------------------------------------ exact H66.
------------------------------------------------------------ destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q c)) as H69.
------------------------------------------------------------- exact H68.
------------------------------------------------------------- destruct H69 as [H69 H70].
exact H69.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p c d) as H67.
----------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (p) (c) (d)).
------------------------------------------------------------intro H67.
apply (@euclidean__tactics.Col__nCol__False (p) (c) (d) (H67)).
-------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (q) (p) (c) (d) (H32) (H65) H66).


----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c d p) as H68.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col c p d) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p d c) /\ (euclidean__axioms.Col d c p))))) as H68.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (p) (c) (d) H67).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col c p d) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p d c) /\ (euclidean__axioms.Col d c p))))) as H69.
-------------------------------------------------------------- exact H68.
-------------------------------------------------------------- destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p d c) /\ (euclidean__axioms.Col d c p)))) as H71.
--------------------------------------------------------------- exact H70.
--------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col d p c) /\ ((euclidean__axioms.Col p d c) /\ (euclidean__axioms.Col d c p))) as H73.
---------------------------------------------------------------- exact H72.
---------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col p d c) /\ (euclidean__axioms.Col d c p)) as H75.
----------------------------------------------------------------- exact H74.
----------------------------------------------------------------- destruct H75 as [H75 H76].
exact H71.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet A B c d) as H69.
------------------------------------------------------------- exists p.
split.
-------------------------------------------------------------- exact H20.
-------------------------------------------------------------- split.
--------------------------------------------------------------- exact H22.
--------------------------------------------------------------- split.
---------------------------------------------------------------- exact H10.
---------------------------------------------------------------- exact H68.
------------------------------------------------------------- apply (@H24 H69).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A p) as H55.
----------------------------------------------- assert (* Cut *) (B = p) as H55.
------------------------------------------------ apply (@euclidean__tactics.NNPP (B = p) H54).
------------------------------------------------ intro H56.
assert (* Cut *) (A = B) as Heq.
------------------------------------------------- apply (@logic.eq__trans (Point) (A) (p) (B) (H56)).
--------------------------------------------------apply (@logic.eq__sym (Point) (B) (p) H55).

------------------------------------------------- assert False.
--------------------------------------------------apply (@H20 Heq).
-------------------------------------------------- contradiction.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A p B) as H56.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B))))) as H56.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (p) (A) H50).
------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B))))) as H57.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B)))) as H59.
--------------------------------------------------- exact H58.
--------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B))) as H61.
---------------------------------------------------- exact H60.
---------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B)) as H63.
----------------------------------------------------- exact H62.
----------------------------------------------------- destruct H63 as [H63 H64].
exact H64.
------------------------------------------------ assert (* Cut *) (~(r = A)) as H57.
------------------------------------------------- intro H57.
assert (* Cut *) (euclidean__axioms.Col d p A) as H58.
-------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun r0: euclidean__axioms.Point => (euclidean__axioms.Col A B r0) -> ((euclidean__axioms.BetS d r0 q) -> ((euclidean__axioms.BetS q r0 d) -> ((~(p = r0)) -> ((euclidean__axioms.Col q r0 d) -> ((euclidean__axioms.Col q d r0) -> ((euclidean__axioms.Col d p r0) -> ((euclidean__axioms.Col B p r0) -> ((euclidean__axioms.Col B A r0) -> ((euclidean__axioms.Col A p r0) -> (euclidean__axioms.Col d p A)))))))))))) with (x := r).
---------------------------------------------------intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
exact H64.

--------------------------------------------------- exact H57.
--------------------------------------------------- exact H12.
--------------------------------------------------- exact H16.
--------------------------------------------------- exact H26.
--------------------------------------------------- exact H31.
--------------------------------------------------- exact H44.
--------------------------------------------------- exact H45.
--------------------------------------------------- exact H47.
--------------------------------------------------- exact H48.
--------------------------------------------------- exact H51.
--------------------------------------------------- exact H53.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col d B A) as H59.
--------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point p (fun X: euclidean__axioms.Point => euclidean__axioms.Col d X A)) with (x := B).
---------------------------------------------------- exact H58.
----------------------------------------------------apply (@euclidean__tactics.NNPP (B = p) H54).

--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B d) as H60.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B d A) /\ ((euclidean__axioms.Col B A d) /\ ((euclidean__axioms.Col A d B) /\ ((euclidean__axioms.Col d A B) /\ (euclidean__axioms.Col A B d))))) as H60.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (d) (B) (A) H59).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B d A) /\ ((euclidean__axioms.Col B A d) /\ ((euclidean__axioms.Col A d B) /\ ((euclidean__axioms.Col d A B) /\ (euclidean__axioms.Col A B d))))) as H61.
------------------------------------------------------ exact H60.
------------------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col B A d) /\ ((euclidean__axioms.Col A d B) /\ ((euclidean__axioms.Col d A B) /\ (euclidean__axioms.Col A B d)))) as H63.
------------------------------------------------------- exact H62.
------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col A d B) /\ ((euclidean__axioms.Col d A B) /\ (euclidean__axioms.Col A B d))) as H65.
-------------------------------------------------------- exact H64.
-------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col d A B) /\ (euclidean__axioms.Col A B d)) as H67.
--------------------------------------------------------- exact H66.
--------------------------------------------------------- destruct H67 as [H67 H68].
exact H68.
---------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (d) (H19) H60).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r A B) as H58.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))))) as H58.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (r) H51).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))))) as H59.
---------------------------------------------------- exact H58.
---------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B)))) as H61.
----------------------------------------------------- exact H60.
----------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))) as H63.
------------------------------------------------------ exact H62.
------------------------------------------------------ destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B)) as H65.
------------------------------------------------------- exact H64.
------------------------------------------------------- destruct H65 as [H65 H66].
exact H66.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col d B r) as H59.
--------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point p (fun X: euclidean__axioms.Point => euclidean__axioms.Col d X r)) with (x := B).
---------------------------------------------------- exact H47.
----------------------------------------------------apply (@euclidean__tactics.NNPP (B = p) H54).

--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r B d) as H60.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B d r) /\ ((euclidean__axioms.Col B r d) /\ ((euclidean__axioms.Col r d B) /\ ((euclidean__axioms.Col d r B) /\ (euclidean__axioms.Col r B d))))) as H60.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (d) (B) (r) H59).
----------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B d r) /\ ((euclidean__axioms.Col B r d) /\ ((euclidean__axioms.Col r d B) /\ ((euclidean__axioms.Col d r B) /\ (euclidean__axioms.Col r B d))))) as H61.
------------------------------------------------------ exact H60.
------------------------------------------------------ destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col B r d) /\ ((euclidean__axioms.Col r d B) /\ ((euclidean__axioms.Col d r B) /\ (euclidean__axioms.Col r B d)))) as H63.
------------------------------------------------------- exact H62.
------------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col r d B) /\ ((euclidean__axioms.Col d r B) /\ (euclidean__axioms.Col r B d))) as H65.
-------------------------------------------------------- exact H64.
-------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col d r B) /\ (euclidean__axioms.Col r B d)) as H67.
--------------------------------------------------------- exact H66.
--------------------------------------------------------- destruct H67 as [H67 H68].
exact H68.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r B A) as H61.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r B A) /\ (euclidean__axioms.Col B A r))))) as H61.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (r) (A) (B) H58).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r B A) /\ (euclidean__axioms.Col B A r))))) as H62.
------------------------------------------------------- exact H61.
------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r B A) /\ (euclidean__axioms.Col B A r)))) as H64.
-------------------------------------------------------- exact H63.
-------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r B A) /\ (euclidean__axioms.Col B A r))) as H66.
--------------------------------------------------------- exact H65.
--------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col r B A) /\ (euclidean__axioms.Col B A r)) as H68.
---------------------------------------------------------- exact H67.
---------------------------------------------------------- destruct H68 as [H68 H69].
exact H68.
----------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq r B)) as H62.
------------------------------------------------------ intro H62.
assert (* Cut *) (euclidean__axioms.Col B d A) as H63.
------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (d) (A)).
--------------------------------------------------------intro H63.
apply (@euclidean__tactics.Col__nCol__False (B) (d) (A) (H63)).
---------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (r) (B) (d) (A) (H60) (H61) H62).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B d) as H64.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col d B A) /\ ((euclidean__axioms.Col d A B) /\ ((euclidean__axioms.Col A B d) /\ ((euclidean__axioms.Col B A d) /\ (euclidean__axioms.Col A d B))))) as H64.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (d) (A) H63).
--------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col d B A) /\ ((euclidean__axioms.Col d A B) /\ ((euclidean__axioms.Col A B d) /\ ((euclidean__axioms.Col B A d) /\ (euclidean__axioms.Col A d B))))) as H65.
---------------------------------------------------------- exact H64.
---------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col d A B) /\ ((euclidean__axioms.Col A B d) /\ ((euclidean__axioms.Col B A d) /\ (euclidean__axioms.Col A d B)))) as H67.
----------------------------------------------------------- exact H66.
----------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col A B d) /\ ((euclidean__axioms.Col B A d) /\ (euclidean__axioms.Col A d B))) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col B A d) /\ (euclidean__axioms.Col A d B)) as H71.
------------------------------------------------------------- exact H70.
------------------------------------------------------------- destruct H71 as [H71 H72].
exact H69.
-------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (d) (H19) H64).
------------------------------------------------------ assert (* Cut *) (B = r) as H63.
------------------------------------------------------- assert (* Cut *) (r = B) as H63.
-------------------------------------------------------- apply (@euclidean__tactics.NNPP (r = B) H62).
-------------------------------------------------------- assert (* Cut *) (B = p) as H64.
--------------------------------------------------------- apply (@euclidean__tactics.NNPP (B = p) H54).
--------------------------------------------------------- apply (@logic.eq__sym (Point) (r) (B) H63).
------------------------------------------------------- assert (* Cut *) (p = B) as H64.
-------------------------------------------------------- assert (* Cut *) (r = B) as H64.
--------------------------------------------------------- apply (@euclidean__tactics.NNPP (r = B) H62).
--------------------------------------------------------- assert (* Cut *) (B = p) as H65.
---------------------------------------------------------- apply (@euclidean__tactics.NNPP (B = p) H54).
---------------------------------------------------------- apply (@logic.eq__sym (Point) (B) (p) H65).
-------------------------------------------------------- assert (* Cut *) (p = r) as H65.
--------------------------------------------------------- assert (* Cut *) (r = B) as H65.
---------------------------------------------------------- apply (@euclidean__tactics.NNPP (r = B) H62).
---------------------------------------------------------- assert (* Cut *) (B = p) as H66.
----------------------------------------------------------- apply (@euclidean__tactics.NNPP (B = p) H54).
----------------------------------------------------------- apply (@logic.eq__trans (Point) (p) (B) (r) (H64) H63).
--------------------------------------------------------- apply (@H31 H65).
------------------------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS q E c) /\ (euclidean__axioms.BetS C E r)) as H34.
-------------------------- apply (@euclidean__axioms.postulate__Pasch__inner (q) (C) (d) (r) (c) (H26) (H0)).
---------------------------apply (@euclidean__tactics.nCol__notCol (q) (d) (C) H33).

-------------------------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS q E c) /\ (euclidean__axioms.BetS C E r))) as H35.
--------------------------- exact H34.
--------------------------- destruct H35 as [E H35].
assert (* AndElim *) ((euclidean__axioms.BetS q E c) /\ (euclidean__axioms.BetS C E r)) as H36.
---------------------------- exact H35.
---------------------------- destruct H36 as [H36 H37].
assert (* Cut *) (euclidean__axioms.BetS r E C) as H38.
----------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (E) (r) H37).
----------------------------- assert (* Cut *) (euclidean__axioms.Col q E c) as H39.
------------------------------ right.
right.
right.
right.
left.
exact H36.
------------------------------ assert (* Cut *) (euclidean__axioms.Col q c p) as H40.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col p q c) /\ ((euclidean__axioms.Col p c q) /\ ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q))))) as H40.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (q) (p) (c) H32).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p q c) /\ ((euclidean__axioms.Col p c q) /\ ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q))))) as H41.
--------------------------------- exact H40.
--------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col p c q) /\ ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q)))) as H43.
---------------------------------- exact H42.
---------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q))) as H45.
----------------------------------- exact H44.
----------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q)) as H47.
------------------------------------ exact H46.
------------------------------------ destruct H47 as [H47 H48].
exact H47.
------------------------------- assert (* Cut *) (euclidean__axioms.Col q c E) as H41.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col E q c) /\ ((euclidean__axioms.Col E c q) /\ ((euclidean__axioms.Col c q E) /\ ((euclidean__axioms.Col q c E) /\ (euclidean__axioms.Col c E q))))) as H41.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (q) (E) (c) H39).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Col E q c) /\ ((euclidean__axioms.Col E c q) /\ ((euclidean__axioms.Col c q E) /\ ((euclidean__axioms.Col q c E) /\ (euclidean__axioms.Col c E q))))) as H42.
---------------------------------- exact H41.
---------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col E c q) /\ ((euclidean__axioms.Col c q E) /\ ((euclidean__axioms.Col q c E) /\ (euclidean__axioms.Col c E q)))) as H44.
----------------------------------- exact H43.
----------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col c q E) /\ ((euclidean__axioms.Col q c E) /\ (euclidean__axioms.Col c E q))) as H46.
------------------------------------ exact H45.
------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col q c E) /\ (euclidean__axioms.Col c E q)) as H48.
------------------------------------- exact H47.
------------------------------------- destruct H48 as [H48 H49].
exact H48.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq q c) as H42.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq E c) /\ ((euclidean__axioms.neq q E) /\ (euclidean__axioms.neq q c))) as H42.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (q) (E) (c) H36).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.neq E c) /\ ((euclidean__axioms.neq q E) /\ (euclidean__axioms.neq q c))) as H43.
----------------------------------- exact H42.
----------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq q E) /\ (euclidean__axioms.neq q c)) as H45.
------------------------------------ exact H44.
------------------------------------ destruct H45 as [H45 H46].
exact H46.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col c p E) as H43.
---------------------------------- apply (@euclidean__tactics.not__nCol__Col (c) (p) (E)).
-----------------------------------intro H43.
apply (@euclidean__tactics.Col__nCol__False (c) (p) (E) (H43)).
------------------------------------apply (@lemma__collinear4.lemma__collinear4 (q) (c) (p) (E) (H40) (H41) H42).


---------------------------------- assert (* Cut *) (euclidean__axioms.Col c E p) as H44.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col p c E) /\ ((euclidean__axioms.Col p E c) /\ ((euclidean__axioms.Col E c p) /\ ((euclidean__axioms.Col c E p) /\ (euclidean__axioms.Col E p c))))) as H44.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (c) (p) (E) H43).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col p c E) /\ ((euclidean__axioms.Col p E c) /\ ((euclidean__axioms.Col E c p) /\ ((euclidean__axioms.Col c E p) /\ (euclidean__axioms.Col E p c))))) as H45.
------------------------------------- exact H44.
------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col p E c) /\ ((euclidean__axioms.Col E c p) /\ ((euclidean__axioms.Col c E p) /\ (euclidean__axioms.Col E p c)))) as H47.
-------------------------------------- exact H46.
-------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col E c p) /\ ((euclidean__axioms.Col c E p) /\ (euclidean__axioms.Col E p c))) as H49.
--------------------------------------- exact H48.
--------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col c E p) /\ (euclidean__axioms.Col E p c)) as H51.
---------------------------------------- exact H50.
---------------------------------------- destruct H51 as [H51 H52].
exact H51.
----------------------------------- assert (* Cut *) (euclidean__axioms.neq r p) as H45.
------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (p) (r) H31).
------------------------------------ assert (* Cut *) (exists (J: euclidean__axioms.Point), (euclidean__axioms.BetS r p J) /\ (euclidean__axioms.Cong p J r p)) as H46.
------------------------------------- apply (@lemma__extension.lemma__extension (r) (p) (r) (p) (H45) H45).
------------------------------------- assert (exists J: euclidean__axioms.Point, ((euclidean__axioms.BetS r p J) /\ (euclidean__axioms.Cong p J r p))) as H47.
-------------------------------------- exact H46.
-------------------------------------- destruct H47 as [J H47].
assert (* AndElim *) ((euclidean__axioms.BetS r p J) /\ (euclidean__axioms.Cong p J r p)) as H48.
--------------------------------------- exact H47.
--------------------------------------- destruct H48 as [H48 H49].
assert (* Cut *) (euclidean__axioms.BetS J p r) as H50.
---------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (r) (p) (J) H48).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col J p r) as H51.
----------------------------------------- right.
right.
right.
right.
left.
exact H50.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq J r) as H52.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq p r) /\ ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r))) as H52.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (J) (p) (r) H50).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq p r) /\ ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r))) as H53.
-------------------------------------------- exact H52.
-------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r)) as H55.
--------------------------------------------- exact H54.
--------------------------------------------- destruct H55 as [H55 H56].
exact H56.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq p r) as H53.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq p r) /\ ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r))) as H53.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (J) (p) (r) H50).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq p r) /\ ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r))) as H54.
--------------------------------------------- exact H53.
--------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r)) as H56.
---------------------------------------------- exact H55.
---------------------------------------------- destruct H56 as [H56 H57].
exact H54.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq J p) as H54.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq p r) /\ ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r))) as H54.
--------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (J) (p) (r) H50).
--------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq p r) /\ ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r))) as H55.
---------------------------------------------- exact H54.
---------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r)) as H57.
----------------------------------------------- exact H56.
----------------------------------------------- destruct H57 as [H57 H58].
exact H57.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B p r) as H55.
--------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (p) (r)).
----------------------------------------------intro H55.
apply (@euclidean__tactics.Col__nCol__False (B) (p) (r) (H55)).
-----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (p) (r) (H10) (H12) H20).


--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A p) as H56.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A p) /\ ((euclidean__axioms.Col B p A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A))))) as H56.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (p) H10).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A p) /\ ((euclidean__axioms.Col B p A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A))))) as H57.
------------------------------------------------ exact H56.
------------------------------------------------ destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col B p A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A)))) as H59.
------------------------------------------------- exact H58.
------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A))) as H61.
-------------------------------------------------- exact H60.
-------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A)) as H63.
--------------------------------------------------- exact H62.
--------------------------------------------------- destruct H63 as [H63 H64].
exact H57.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A r) as H57.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A r) /\ ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A))))) as H57.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (r) H12).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col B A r) /\ ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A))))) as H58.
------------------------------------------------- exact H57.
------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A)))) as H60.
-------------------------------------------------- exact H59.
-------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A))) as H62.
--------------------------------------------------- exact H61.
--------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A)) as H64.
---------------------------------------------------- exact H63.
---------------------------------------------------- destruct H64 as [H64 H65].
exact H58.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H58.
------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (B) H20).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A p r) as H59.
------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (p) (r)).
--------------------------------------------------intro H59.
apply (@euclidean__tactics.Col__nCol__False (A) (p) (r) (H59)).
---------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (p) (r) (H56) (H57) H58).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p r A) as H60.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p A r) /\ ((euclidean__axioms.Col p r A) /\ ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col A r p) /\ (euclidean__axioms.Col r p A))))) as H60.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (p) (r) H59).
--------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p A r) /\ ((euclidean__axioms.Col p r A) /\ ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col A r p) /\ (euclidean__axioms.Col r p A))))) as H61.
---------------------------------------------------- exact H60.
---------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((euclidean__axioms.Col p r A) /\ ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col A r p) /\ (euclidean__axioms.Col r p A)))) as H63.
----------------------------------------------------- exact H62.
----------------------------------------------------- destruct H63 as [H63 H64].
assert (* AndElim *) ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col A r p) /\ (euclidean__axioms.Col r p A))) as H65.
------------------------------------------------------ exact H64.
------------------------------------------------------ destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.Col A r p) /\ (euclidean__axioms.Col r p A)) as H67.
------------------------------------------------------- exact H66.
------------------------------------------------------- destruct H67 as [H67 H68].
exact H63.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p r B) as H61.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p B r) /\ ((euclidean__axioms.Col p r B) /\ ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col B r p) /\ (euclidean__axioms.Col r p B))))) as H61.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (p) (r) H55).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p B r) /\ ((euclidean__axioms.Col p r B) /\ ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col B r p) /\ (euclidean__axioms.Col r p B))))) as H62.
----------------------------------------------------- exact H61.
----------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col p r B) /\ ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col B r p) /\ (euclidean__axioms.Col r p B)))) as H64.
------------------------------------------------------ exact H63.
------------------------------------------------------ destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col B r p) /\ (euclidean__axioms.Col r p B))) as H66.
------------------------------------------------------- exact H65.
------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col B r p) /\ (euclidean__axioms.Col r p B)) as H68.
-------------------------------------------------------- exact H67.
-------------------------------------------------------- destruct H68 as [H68 H69].
exact H64.
--------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet C d J r)) as H62.
---------------------------------------------------- intro H62.
assert (* Cut *) (exists (K: euclidean__axioms.Point), (euclidean__axioms.neq C d) /\ ((euclidean__axioms.neq J r) /\ ((euclidean__axioms.Col C d K) /\ (euclidean__axioms.Col J r K)))) as H63.
----------------------------------------------------- exact H62.
----------------------------------------------------- assert (exists K: euclidean__axioms.Point, ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.neq J r) /\ ((euclidean__axioms.Col C d K) /\ (euclidean__axioms.Col J r K))))) as H64.
------------------------------------------------------ exact H63.
------------------------------------------------------ destruct H64 as [K H64].
assert (* AndElim *) ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.neq J r) /\ ((euclidean__axioms.Col C d K) /\ (euclidean__axioms.Col J r K)))) as H65.
------------------------------------------------------- exact H64.
------------------------------------------------------- destruct H65 as [H65 H66].
assert (* AndElim *) ((euclidean__axioms.neq J r) /\ ((euclidean__axioms.Col C d K) /\ (euclidean__axioms.Col J r K))) as H67.
-------------------------------------------------------- exact H66.
-------------------------------------------------------- destruct H67 as [H67 H68].
assert (* AndElim *) ((euclidean__axioms.Col C d K) /\ (euclidean__axioms.Col J r K)) as H69.
--------------------------------------------------------- exact H68.
--------------------------------------------------------- destruct H69 as [H69 H70].
assert (* Cut *) (euclidean__axioms.Col C c d) as H71.
---------------------------------------------------------- exact H27.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C d c) as H72.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))))) as H72.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (C) (c) (d) H71).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))))) as H73.
------------------------------------------------------------- exact H72.
------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C)))) as H75.
-------------------------------------------------------------- exact H74.
-------------------------------------------------------------- destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))) as H77.
--------------------------------------------------------------- exact H76.
--------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C)) as H79.
---------------------------------------------------------------- exact H78.
---------------------------------------------------------------- destruct H79 as [H79 H80].
exact H79.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq c d) as H73.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq p r) /\ ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r))) as H73.
------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (J) (p) (r) H50).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq p r) /\ ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r))) as H74.
-------------------------------------------------------------- exact H73.
-------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.neq J p) /\ (euclidean__axioms.neq J r)) as H76.
--------------------------------------------------------------- exact H75.
--------------------------------------------------------------- destruct H76 as [H76 H77].
exact H22.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq d c) as H74.
------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (c) (d) H73).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col d c K) as H75.
-------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (d) (c) (K)).
---------------------------------------------------------------intro H75.
apply (@euclidean__tactics.Col__nCol__False (d) (c) (K) (H75)).
----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (d) (c) (K) (H72) (H69) H65).


-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c d K) as H76.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col c d K) /\ ((euclidean__axioms.Col c K d) /\ ((euclidean__axioms.Col K d c) /\ ((euclidean__axioms.Col d K c) /\ (euclidean__axioms.Col K c d))))) as H76.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (d) (c) (K) H75).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col c d K) /\ ((euclidean__axioms.Col c K d) /\ ((euclidean__axioms.Col K d c) /\ ((euclidean__axioms.Col d K c) /\ (euclidean__axioms.Col K c d))))) as H77.
----------------------------------------------------------------- exact H76.
----------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.Col c K d) /\ ((euclidean__axioms.Col K d c) /\ ((euclidean__axioms.Col d K c) /\ (euclidean__axioms.Col K c d)))) as H79.
------------------------------------------------------------------ exact H78.
------------------------------------------------------------------ destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col K d c) /\ ((euclidean__axioms.Col d K c) /\ (euclidean__axioms.Col K c d))) as H81.
------------------------------------------------------------------- exact H80.
------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col d K c) /\ (euclidean__axioms.Col K c d)) as H83.
-------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------- destruct H83 as [H83 H84].
exact H77.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r p J) as H77.
---------------------------------------------------------------- right.
right.
right.
right.
left.
exact H48.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r J p) as H78.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p r J) /\ ((euclidean__axioms.Col p J r) /\ ((euclidean__axioms.Col J r p) /\ ((euclidean__axioms.Col r J p) /\ (euclidean__axioms.Col J p r))))) as H78.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (r) (p) (J) H77).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col p r J) /\ ((euclidean__axioms.Col p J r) /\ ((euclidean__axioms.Col J r p) /\ ((euclidean__axioms.Col r J p) /\ (euclidean__axioms.Col J p r))))) as H79.
------------------------------------------------------------------- exact H78.
------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.Col p J r) /\ ((euclidean__axioms.Col J r p) /\ ((euclidean__axioms.Col r J p) /\ (euclidean__axioms.Col J p r)))) as H81.
-------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col J r p) /\ ((euclidean__axioms.Col r J p) /\ (euclidean__axioms.Col J p r))) as H83.
--------------------------------------------------------------------- exact H82.
--------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col r J p) /\ (euclidean__axioms.Col J p r)) as H85.
---------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------- destruct H85 as [H85 H86].
exact H85.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq r J) as H79.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq p J) /\ ((euclidean__axioms.neq r p) /\ (euclidean__axioms.neq r J))) as H79.
------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (r) (p) (J) H48).
------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq p J) /\ ((euclidean__axioms.neq r p) /\ (euclidean__axioms.neq r J))) as H80.
-------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------- destruct H80 as [H80 H81].
assert (* AndElim *) ((euclidean__axioms.neq r p) /\ (euclidean__axioms.neq r J)) as H82.
--------------------------------------------------------------------- exact H81.
--------------------------------------------------------------------- destruct H82 as [H82 H83].
exact H83.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col r J K) as H80.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col r J K) /\ ((euclidean__axioms.Col r K J) /\ ((euclidean__axioms.Col K J r) /\ ((euclidean__axioms.Col J K r) /\ (euclidean__axioms.Col K r J))))) as H80.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (J) (r) (K) H70).
-------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col r J K) /\ ((euclidean__axioms.Col r K J) /\ ((euclidean__axioms.Col K J r) /\ ((euclidean__axioms.Col J K r) /\ (euclidean__axioms.Col K r J))))) as H81.
--------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------- destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.Col r K J) /\ ((euclidean__axioms.Col K J r) /\ ((euclidean__axioms.Col J K r) /\ (euclidean__axioms.Col K r J)))) as H83.
---------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col K J r) /\ ((euclidean__axioms.Col J K r) /\ (euclidean__axioms.Col K r J))) as H85.
----------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col J K r) /\ (euclidean__axioms.Col K r J)) as H87.
------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------ destruct H87 as [H87 H88].
exact H81.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col J p K) as H81.
-------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (J) (p) (K)).
---------------------------------------------------------------------intro H81.
apply (@euclidean__tactics.Col__nCol__False (J) (p) (K) (H81)).
----------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (r) (J) (p) (K) (H78) (H80) H79).


-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col J p r) as H82.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p J K) /\ ((euclidean__axioms.Col p K J) /\ ((euclidean__axioms.Col K J p) /\ ((euclidean__axioms.Col J K p) /\ (euclidean__axioms.Col K p J))))) as H82.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (J) (p) (K) H81).
---------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p J K) /\ ((euclidean__axioms.Col p K J) /\ ((euclidean__axioms.Col K J p) /\ ((euclidean__axioms.Col J K p) /\ (euclidean__axioms.Col K p J))))) as H83.
----------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col p K J) /\ ((euclidean__axioms.Col K J p) /\ ((euclidean__axioms.Col J K p) /\ (euclidean__axioms.Col K p J)))) as H85.
------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------ destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col K J p) /\ ((euclidean__axioms.Col J K p) /\ (euclidean__axioms.Col K p J))) as H87.
------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col J K p) /\ (euclidean__axioms.Col K p J)) as H89.
-------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------- destruct H89 as [H89 H90].
exact H51.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq p J) as H83.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq p J) /\ ((euclidean__axioms.neq r p) /\ (euclidean__axioms.neq r J))) as H83.
----------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (r) (p) (J) H48).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq p J) /\ ((euclidean__axioms.neq r p) /\ (euclidean__axioms.neq r J))) as H84.
------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------ destruct H84 as [H84 H85].
assert (* AndElim *) ((euclidean__axioms.neq r p) /\ (euclidean__axioms.neq r J)) as H86.
------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------- destruct H86 as [H86 H87].
exact H84.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq J p) as H84.
----------------------------------------------------------------------- exact H54.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p K r) as H85.
------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col (p) (K) (r)).
-------------------------------------------------------------------------intro H85.
apply (@euclidean__tactics.Col__nCol__False (p) (K) (r) (H85)).
--------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (J) (p) (K) (r) (H81) (H82) H84).


------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col p r K) as H86.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K p r) /\ ((euclidean__axioms.Col K r p) /\ ((euclidean__axioms.Col r p K) /\ ((euclidean__axioms.Col p r K) /\ (euclidean__axioms.Col r K p))))) as H86.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (p) (K) (r) H85).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col K p r) /\ ((euclidean__axioms.Col K r p) /\ ((euclidean__axioms.Col r p K) /\ ((euclidean__axioms.Col p r K) /\ (euclidean__axioms.Col r K p))))) as H87.
--------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col K r p) /\ ((euclidean__axioms.Col r p K) /\ ((euclidean__axioms.Col p r K) /\ (euclidean__axioms.Col r K p)))) as H89.
---------------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Col r p K) /\ ((euclidean__axioms.Col p r K) /\ (euclidean__axioms.Col r K p))) as H91.
----------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col p r K) /\ (euclidean__axioms.Col r K p)) as H93.
------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------ destruct H93 as [H93 H94].
exact H93.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B K) as H87.
-------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (B) (K)).
---------------------------------------------------------------------------intro H87.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (K) (H87)).
----------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (p) (r) (A) (B) (K) (H53) (H60) (H61) H86).


-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A B c d) as H88.
--------------------------------------------------------------------------- exists K.
split.
---------------------------------------------------------------------------- exact H20.
---------------------------------------------------------------------------- split.
----------------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------------- split.
------------------------------------------------------------------------------ exact H87.
------------------------------------------------------------------------------ exact H76.
--------------------------------------------------------------------------- apply (@H24 H88).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS c E p) as H63.
----------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween (C) (d) (J) (r) (c) (p) (E) (H27) (H51) (H4) (H52) (H2) (H53) (H62) (H37) H43).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS p E c) as H64.
------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (c) (E) (p) H63).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS q p E) as H65.
------------------------------------------------------- apply (@euclidean__axioms.axiom__innertransitivity (q) (p) (E) (c) (H30) H64).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol p r c) as H66.
-------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (p) (r) (c)).
---------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (p) (r) (c)).
----------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (A) (B) (c) (p) (r) (H18) (H10) (H12) H53).


-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol p c r) as H67.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol r p c) /\ ((euclidean__axioms.nCol r c p) /\ ((euclidean__axioms.nCol c p r) /\ ((euclidean__axioms.nCol p c r) /\ (euclidean__axioms.nCol c r p))))) as H67.
---------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (p) (r) (c) H66).
---------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol r p c) /\ ((euclidean__axioms.nCol r c p) /\ ((euclidean__axioms.nCol c p r) /\ ((euclidean__axioms.nCol p c r) /\ (euclidean__axioms.nCol c r p))))) as H68.
----------------------------------------------------------- exact H67.
----------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.nCol r c p) /\ ((euclidean__axioms.nCol c p r) /\ ((euclidean__axioms.nCol p c r) /\ (euclidean__axioms.nCol c r p)))) as H70.
------------------------------------------------------------ exact H69.
------------------------------------------------------------ destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.nCol c p r) /\ ((euclidean__axioms.nCol p c r) /\ (euclidean__axioms.nCol c r p))) as H72.
------------------------------------------------------------- exact H71.
------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.nCol p c r) /\ (euclidean__axioms.nCol c r p)) as H74.
-------------------------------------------------------------- exact H73.
-------------------------------------------------------------- destruct H74 as [H74 H75].
exact H74.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q p c) as H68.
---------------------------------------------------------- exact H32.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p c q) as H69.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p q c) /\ ((euclidean__axioms.Col p c q) /\ ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q))))) as H69.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (q) (p) (c) H68).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col p q c) /\ ((euclidean__axioms.Col p c q) /\ ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q))))) as H70.
------------------------------------------------------------- exact H69.
------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col p c q) /\ ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q)))) as H72.
-------------------------------------------------------------- exact H71.
-------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col c q p) /\ ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q))) as H74.
--------------------------------------------------------------- exact H73.
--------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col q c p) /\ (euclidean__axioms.Col c p q)) as H76.
---------------------------------------------------------------- exact H75.
---------------------------------------------------------------- destruct H76 as [H76 H77].
exact H72.
----------------------------------------------------------- assert (* Cut *) (c = c) as H70.
------------------------------------------------------------ apply (@logic.eq__refl (Point) c).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col p c c) as H71.
------------------------------------------------------------- right.
right.
left.
exact H70.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq q c) as H72.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq p E) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q E))) as H72.
--------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (q) (p) (E) H65).
--------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq p E) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q E))) as H73.
---------------------------------------------------------------- exact H72.
---------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q E)) as H75.
----------------------------------------------------------------- exact H74.
----------------------------------------------------------------- destruct H75 as [H75 H76].
exact H42.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol q c r) as H73.
--------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (q) (c) (r)).
----------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (q) (c) (r)).
-----------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (p) (c) (r) (q) (c) (H67) (H69) (H71) H72).


--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol q r c) as H74.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol c q r) /\ ((euclidean__axioms.nCol c r q) /\ ((euclidean__axioms.nCol r q c) /\ ((euclidean__axioms.nCol q r c) /\ (euclidean__axioms.nCol r c q))))) as H74.
----------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (q) (c) (r) H73).
----------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol c q r) /\ ((euclidean__axioms.nCol c r q) /\ ((euclidean__axioms.nCol r q c) /\ ((euclidean__axioms.nCol q r c) /\ (euclidean__axioms.nCol r c q))))) as H75.
------------------------------------------------------------------ exact H74.
------------------------------------------------------------------ destruct H75 as [H75 H76].
assert (* AndElim *) ((euclidean__axioms.nCol c r q) /\ ((euclidean__axioms.nCol r q c) /\ ((euclidean__axioms.nCol q r c) /\ (euclidean__axioms.nCol r c q)))) as H77.
------------------------------------------------------------------- exact H76.
------------------------------------------------------------------- destruct H77 as [H77 H78].
assert (* AndElim *) ((euclidean__axioms.nCol r q c) /\ ((euclidean__axioms.nCol q r c) /\ (euclidean__axioms.nCol r c q))) as H79.
-------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.nCol q r c) /\ (euclidean__axioms.nCol r c q)) as H81.
--------------------------------------------------------------------- exact H80.
--------------------------------------------------------------------- destruct H81 as [H81 H82].
exact H81.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq q d) as H75.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq r d) /\ ((euclidean__axioms.neq q r) /\ (euclidean__axioms.neq q d))) as H75.
------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (q) (r) (d) H26).
------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq r d) /\ ((euclidean__axioms.neq q r) /\ (euclidean__axioms.neq q d))) as H76.
------------------------------------------------------------------- exact H75.
------------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.neq q r) /\ (euclidean__axioms.neq q d)) as H78.
-------------------------------------------------------------------- exact H77.
-------------------------------------------------------------------- destruct H78 as [H78 H79].
exact H79.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q r d) as H76.
------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H26.
------------------------------------------------------------------ assert (* Cut *) (q = q) as H77.
------------------------------------------------------------------- apply (@logic.eq__refl (Point) q).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q r q) as H78.
-------------------------------------------------------------------- right.
left.
exact H77.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol q d c) as H79.
--------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (q) (d) (c)).
----------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (q) (d) (c)).
-----------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (q) (r) (c) (q) (d) (H74) (H78) (H76) H75).


--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol d c q) as H80.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol d q c) /\ ((euclidean__axioms.nCol d c q) /\ ((euclidean__axioms.nCol c q d) /\ ((euclidean__axioms.nCol q c d) /\ (euclidean__axioms.nCol c d q))))) as H80.
----------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (q) (d) (c) H79).
----------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol d q c) /\ ((euclidean__axioms.nCol d c q) /\ ((euclidean__axioms.nCol c q d) /\ ((euclidean__axioms.nCol q c d) /\ (euclidean__axioms.nCol c d q))))) as H81.
------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------ destruct H81 as [H81 H82].
assert (* AndElim *) ((euclidean__axioms.nCol d c q) /\ ((euclidean__axioms.nCol c q d) /\ ((euclidean__axioms.nCol q c d) /\ (euclidean__axioms.nCol c d q)))) as H83.
------------------------------------------------------------------------- exact H82.
------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.nCol c q d) /\ ((euclidean__axioms.nCol q c d) /\ (euclidean__axioms.nCol c d q))) as H85.
-------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.nCol q c d) /\ (euclidean__axioms.nCol c d q)) as H87.
--------------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------------- destruct H87 as [H87 H88].
exact H83.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C c d) as H81.
----------------------------------------------------------------------- exact H27.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col d c C) as H82.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))))) as H82.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (c) (d) H81).
------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))))) as H83.
-------------------------------------------------------------------------- exact H82.
-------------------------------------------------------------------------- destruct H83 as [H83 H84].
assert (* AndElim *) ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C)))) as H85.
--------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------- destruct H85 as [H85 H86].
assert (* AndElim *) ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))) as H87.
---------------------------------------------------------------------------- exact H86.
---------------------------------------------------------------------------- destruct H87 as [H87 H88].
assert (* AndElim *) ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C)) as H89.
----------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------- destruct H89 as [H89 H90].
exact H90.
------------------------------------------------------------------------ assert (* Cut *) (d = d) as H83.
------------------------------------------------------------------------- apply (@logic.eq__refl (Point) d).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col d c d) as H84.
-------------------------------------------------------------------------- right.
left.
exact H83.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C d) as H85.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq p E) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q E))) as H85.
---------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (q) (p) (E) H65).
---------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq p E) /\ ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q E))) as H86.
----------------------------------------------------------------------------- exact H85.
----------------------------------------------------------------------------- destruct H86 as [H86 H87].
assert (* AndElim *) ((euclidean__axioms.neq q p) /\ (euclidean__axioms.neq q E)) as H88.
------------------------------------------------------------------------------ exact H87.
------------------------------------------------------------------------------ destruct H88 as [H88 H89].
exact H4.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq d C) as H86.
---------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (d) H85).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol d C q) as H87.
----------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (d) (C) (q)).
------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (d) (C) (q)).
-------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (d) (c) (q) (d) (C) (H80) (H84) (H82) H86).


----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol d q C) as H88.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol C d q) /\ ((euclidean__axioms.nCol C q d) /\ ((euclidean__axioms.nCol q d C) /\ ((euclidean__axioms.nCol d q C) /\ (euclidean__axioms.nCol q C d))))) as H88.
------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (d) (C) (q) H87).
------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C d q) /\ ((euclidean__axioms.nCol C q d) /\ ((euclidean__axioms.nCol q d C) /\ ((euclidean__axioms.nCol d q C) /\ (euclidean__axioms.nCol q C d))))) as H89.
-------------------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.nCol C q d) /\ ((euclidean__axioms.nCol q d C) /\ ((euclidean__axioms.nCol d q C) /\ (euclidean__axioms.nCol q C d)))) as H91.
--------------------------------------------------------------------------------- exact H90.
--------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.nCol q d C) /\ ((euclidean__axioms.nCol d q C) /\ (euclidean__axioms.nCol q C d))) as H93.
---------------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.nCol d q C) /\ (euclidean__axioms.nCol q C d)) as H95.
----------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------- destruct H95 as [H95 H96].
exact H95.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col q r d) as H89.
------------------------------------------------------------------------------- exact H76.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col d q r) as H90.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col r q d) /\ ((euclidean__axioms.Col r d q) /\ ((euclidean__axioms.Col d q r) /\ ((euclidean__axioms.Col q d r) /\ (euclidean__axioms.Col d r q))))) as H90.
--------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (q) (r) (d) H89).
--------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col r q d) /\ ((euclidean__axioms.Col r d q) /\ ((euclidean__axioms.Col d q r) /\ ((euclidean__axioms.Col q d r) /\ (euclidean__axioms.Col d r q))))) as H91.
---------------------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------------------- destruct H91 as [H91 H92].
assert (* AndElim *) ((euclidean__axioms.Col r d q) /\ ((euclidean__axioms.Col d q r) /\ ((euclidean__axioms.Col q d r) /\ (euclidean__axioms.Col d r q)))) as H93.
----------------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------------- destruct H93 as [H93 H94].
assert (* AndElim *) ((euclidean__axioms.Col d q r) /\ ((euclidean__axioms.Col q d r) /\ (euclidean__axioms.Col d r q))) as H95.
------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------ destruct H95 as [H95 H96].
assert (* AndElim *) ((euclidean__axioms.Col q d r) /\ (euclidean__axioms.Col d r q)) as H97.
------------------------------------------------------------------------------------- exact H96.
------------------------------------------------------------------------------------- destruct H97 as [H97 H98].
exact H95.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col d q q) as H91.
--------------------------------------------------------------------------------- right.
right.
left.
exact H77.
--------------------------------------------------------------------------------- assert (* Cut *) (~(r = C)) as H92.
---------------------------------------------------------------------------------- intro H92.
assert (* Cut *) (euclidean__axioms.Col A B C) as H93.
----------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun r0: euclidean__axioms.Point => (euclidean__axioms.Col A B r0) -> ((euclidean__axioms.BetS d r0 q) -> ((euclidean__axioms.BetS q r0 d) -> ((~(p = r0)) -> ((euclidean__axioms.BetS C E r0) -> ((euclidean__axioms.BetS r0 E C) -> ((euclidean__axioms.neq r0 p) -> ((euclidean__axioms.BetS r0 p J) -> ((euclidean__axioms.Cong p J r0 p) -> ((euclidean__axioms.BetS J p r0) -> ((euclidean__axioms.Col J p r0) -> ((euclidean__axioms.neq J r0) -> ((euclidean__axioms.neq p r0) -> ((euclidean__axioms.Col B p r0) -> ((euclidean__axioms.Col B A r0) -> ((euclidean__axioms.Col A p r0) -> ((euclidean__axioms.Col p r0 A) -> ((euclidean__axioms.Col p r0 B) -> ((~(euclidean__defs.Meet C d J r0)) -> ((euclidean__axioms.nCol p r0 c) -> ((euclidean__axioms.nCol p c r0) -> ((euclidean__axioms.nCol q c r0) -> ((euclidean__axioms.nCol q r0 c) -> ((euclidean__axioms.Col q r0 d) -> ((euclidean__axioms.Col q r0 q) -> ((euclidean__axioms.Col q r0 d) -> ((euclidean__axioms.Col d q r0) -> (euclidean__axioms.Col A B C))))))))))))))))))))))))))))) with (x := r).
------------------------------------------------------------------------------------intro H93.
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
exact H93.

------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------ exact H12.
------------------------------------------------------------------------------------ exact H16.
------------------------------------------------------------------------------------ exact H26.
------------------------------------------------------------------------------------ exact H31.
------------------------------------------------------------------------------------ exact H37.
------------------------------------------------------------------------------------ exact H38.
------------------------------------------------------------------------------------ exact H45.
------------------------------------------------------------------------------------ exact H48.
------------------------------------------------------------------------------------ exact H49.
------------------------------------------------------------------------------------ exact H50.
------------------------------------------------------------------------------------ exact H51.
------------------------------------------------------------------------------------ exact H52.
------------------------------------------------------------------------------------ exact H53.
------------------------------------------------------------------------------------ exact H55.
------------------------------------------------------------------------------------ exact H57.
------------------------------------------------------------------------------------ exact H59.
------------------------------------------------------------------------------------ exact H60.
------------------------------------------------------------------------------------ exact H61.
------------------------------------------------------------------------------------ exact H62.
------------------------------------------------------------------------------------ exact H66.
------------------------------------------------------------------------------------ exact H67.
------------------------------------------------------------------------------------ exact H73.
------------------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------------ exact H90.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A B c d) as H94.
------------------------------------------------------------------------------------ exists C.
split.
------------------------------------------------------------------------------------- exact H20.
------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------- exact H22.
-------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------------------------- exact H28.
------------------------------------------------------------------------------------ apply (@H24 H94).
---------------------------------------------------------------------------------- assert (* Cut *) (~(r = q)) as H93.
----------------------------------------------------------------------------------- intro H93.
assert (* Cut *) (euclidean__axioms.Col r q c) as H94.
------------------------------------------------------------------------------------ left.
exact H93.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col q r c) as H95.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col q r c) /\ ((euclidean__axioms.Col q c r) /\ ((euclidean__axioms.Col c r q) /\ ((euclidean__axioms.Col r c q) /\ (euclidean__axioms.Col c q r))))) as H95.
-------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (r) (q) (c) H94).
-------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col q r c) /\ ((euclidean__axioms.Col q c r) /\ ((euclidean__axioms.Col c r q) /\ ((euclidean__axioms.Col r c q) /\ (euclidean__axioms.Col c q r))))) as H96.
--------------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.Col q c r) /\ ((euclidean__axioms.Col c r q) /\ ((euclidean__axioms.Col r c q) /\ (euclidean__axioms.Col c q r)))) as H98.
---------------------------------------------------------------------------------------- exact H97.
---------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.Col c r q) /\ ((euclidean__axioms.Col r c q) /\ (euclidean__axioms.Col c q r))) as H100.
----------------------------------------------------------------------------------------- exact H99.
----------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.Col r c q) /\ (euclidean__axioms.Col c q r)) as H102.
------------------------------------------------------------------------------------------ exact H101.
------------------------------------------------------------------------------------------ destruct H102 as [H102 H103].
exact H96.
------------------------------------------------------------------------------------- apply (@H33).
--------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (q) (d) (C)).
---------------------------------------------------------------------------------------intro H96.
apply (@euclidean__tactics.Col__nCol__False (q) (r) (c) (H74) H95).


----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol r q C) as H94.
------------------------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (r) (q) (C)).
-------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (r) (q) (C)).
--------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (d) (q) (C) (r) (q) (H88) (H90) (H91) H93).


------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol r C q) as H95.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol q r C) /\ ((euclidean__axioms.nCol q C r) /\ ((euclidean__axioms.nCol C r q) /\ ((euclidean__axioms.nCol r C q) /\ (euclidean__axioms.nCol C q r))))) as H95.
-------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (r) (q) (C) H94).
-------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol q r C) /\ ((euclidean__axioms.nCol q C r) /\ ((euclidean__axioms.nCol C r q) /\ ((euclidean__axioms.nCol r C q) /\ (euclidean__axioms.nCol C q r))))) as H96.
--------------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------------- destruct H96 as [H96 H97].
assert (* AndElim *) ((euclidean__axioms.nCol q C r) /\ ((euclidean__axioms.nCol C r q) /\ ((euclidean__axioms.nCol r C q) /\ (euclidean__axioms.nCol C q r)))) as H98.
---------------------------------------------------------------------------------------- exact H97.
---------------------------------------------------------------------------------------- destruct H98 as [H98 H99].
assert (* AndElim *) ((euclidean__axioms.nCol C r q) /\ ((euclidean__axioms.nCol r C q) /\ (euclidean__axioms.nCol C q r))) as H100.
----------------------------------------------------------------------------------------- exact H99.
----------------------------------------------------------------------------------------- destruct H100 as [H100 H101].
assert (* AndElim *) ((euclidean__axioms.nCol r C q) /\ (euclidean__axioms.nCol C q r)) as H102.
------------------------------------------------------------------------------------------ exact H101.
------------------------------------------------------------------------------------------ destruct H102 as [H102 H103].
exact H102.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS r E C) as H96.
-------------------------------------------------------------------------------------- exact H38.
-------------------------------------------------------------------------------------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS q F C) /\ (euclidean__axioms.BetS r p F)) as H97.
--------------------------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer (q) (r) (E) (p) (C) (H65) (H96) H95).
--------------------------------------------------------------------------------------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS q F C) /\ (euclidean__axioms.BetS r p F))) as H98.
---------------------------------------------------------------------------------------- exact H97.
---------------------------------------------------------------------------------------- destruct H98 as [F H98].
assert (* AndElim *) ((euclidean__axioms.BetS q F C) /\ (euclidean__axioms.BetS r p F)) as H99.
----------------------------------------------------------------------------------------- exact H98.
----------------------------------------------------------------------------------------- destruct H99 as [H99 H100].
assert (* Cut *) (euclidean__axioms.BetS C F q) as H101.
------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (q) (F) (C) H99).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col r p F) as H102.
------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H100.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r p A) as H103.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col r p A) /\ ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col A p r) /\ ((euclidean__axioms.Col p A r) /\ (euclidean__axioms.Col A r p))))) as H103.
--------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (p) (r) (A) H60).
--------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col r p A) /\ ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col A p r) /\ ((euclidean__axioms.Col p A r) /\ (euclidean__axioms.Col A r p))))) as H104.
---------------------------------------------------------------------------------------------- exact H103.
---------------------------------------------------------------------------------------------- destruct H104 as [H104 H105].
assert (* AndElim *) ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col A p r) /\ ((euclidean__axioms.Col p A r) /\ (euclidean__axioms.Col A r p)))) as H106.
----------------------------------------------------------------------------------------------- exact H105.
----------------------------------------------------------------------------------------------- destruct H106 as [H106 H107].
assert (* AndElim *) ((euclidean__axioms.Col A p r) /\ ((euclidean__axioms.Col p A r) /\ (euclidean__axioms.Col A r p))) as H108.
------------------------------------------------------------------------------------------------ exact H107.
------------------------------------------------------------------------------------------------ destruct H108 as [H108 H109].
assert (* AndElim *) ((euclidean__axioms.Col p A r) /\ (euclidean__axioms.Col A r p)) as H110.
------------------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------------------- destruct H110 as [H110 H111].
exact H104.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r p B) as H104.
--------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col r p B) /\ ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col B p r) /\ ((euclidean__axioms.Col p B r) /\ (euclidean__axioms.Col B r p))))) as H104.
---------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (p) (r) (B) H61).
---------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col r p B) /\ ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col B p r) /\ ((euclidean__axioms.Col p B r) /\ (euclidean__axioms.Col B r p))))) as H105.
----------------------------------------------------------------------------------------------- exact H104.
----------------------------------------------------------------------------------------------- destruct H105 as [H105 H106].
assert (* AndElim *) ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col B p r) /\ ((euclidean__axioms.Col p B r) /\ (euclidean__axioms.Col B r p)))) as H107.
------------------------------------------------------------------------------------------------ exact H106.
------------------------------------------------------------------------------------------------ destruct H107 as [H107 H108].
assert (* AndElim *) ((euclidean__axioms.Col B p r) /\ ((euclidean__axioms.Col p B r) /\ (euclidean__axioms.Col B r p))) as H109.
------------------------------------------------------------------------------------------------- exact H108.
------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.Col p B r) /\ (euclidean__axioms.Col B r p)) as H111.
-------------------------------------------------------------------------------------------------- exact H110.
-------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
exact H105.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H105.
---------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (B) (F)).
-----------------------------------------------------------------------------------------------intro H105.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (F) (H105)).
------------------------------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 (r) (p) (A) (B) (F) (H45) (H103) (H104) H102).


---------------------------------------------------------------------------------------------- assert (* Cut *) (r = r) as H106.
----------------------------------------------------------------------------------------------- apply (@logic.eq__refl (Point) r).
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col d q r) as H107.
------------------------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq q r) as H108.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq r d) /\ ((euclidean__axioms.neq q r) /\ (euclidean__axioms.neq q d))) as H108.
-------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (q) (r) (d) H26).
-------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq r d) /\ ((euclidean__axioms.neq q r) /\ (euclidean__axioms.neq q d))) as H109.
--------------------------------------------------------------------------------------------------- exact H108.
--------------------------------------------------------------------------------------------------- destruct H109 as [H109 H110].
assert (* AndElim *) ((euclidean__axioms.neq q r) /\ (euclidean__axioms.neq q d)) as H111.
---------------------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
exact H111.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol q r C) as H109.
-------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (q) (r) (C)).
---------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (q) (r) (C)).
----------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (d) (q) (C) (q) (r) (H88) (H91) (H107) H108).


-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol q C r) as H110.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol r q C) /\ ((euclidean__axioms.nCol r C q) /\ ((euclidean__axioms.nCol C q r) /\ ((euclidean__axioms.nCol q C r) /\ (euclidean__axioms.nCol C r q))))) as H110.
---------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (q) (r) (C) H109).
---------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol r q C) /\ ((euclidean__axioms.nCol r C q) /\ ((euclidean__axioms.nCol C q r) /\ ((euclidean__axioms.nCol q C r) /\ (euclidean__axioms.nCol C r q))))) as H111.
----------------------------------------------------------------------------------------------------- exact H110.
----------------------------------------------------------------------------------------------------- destruct H111 as [H111 H112].
assert (* AndElim *) ((euclidean__axioms.nCol r C q) /\ ((euclidean__axioms.nCol C q r) /\ ((euclidean__axioms.nCol q C r) /\ (euclidean__axioms.nCol C r q)))) as H113.
------------------------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------------------------ destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.nCol C q r) /\ ((euclidean__axioms.nCol q C r) /\ (euclidean__axioms.nCol C r q))) as H115.
------------------------------------------------------------------------------------------------------- exact H114.
------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.nCol q C r) /\ (euclidean__axioms.nCol C r q)) as H117.
-------------------------------------------------------------------------------------------------------- exact H116.
-------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
exact H117.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q F C) as H111.
---------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H99.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q C F) as H112.
----------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F q C) /\ ((euclidean__axioms.Col F C q) /\ ((euclidean__axioms.Col C q F) /\ ((euclidean__axioms.Col q C F) /\ (euclidean__axioms.Col C F q))))) as H112.
------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (q) (F) (C) H111).
------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col F q C) /\ ((euclidean__axioms.Col F C q) /\ ((euclidean__axioms.Col C q F) /\ ((euclidean__axioms.Col q C F) /\ (euclidean__axioms.Col C F q))))) as H113.
------------------------------------------------------------------------------------------------------- exact H112.
------------------------------------------------------------------------------------------------------- destruct H113 as [H113 H114].
assert (* AndElim *) ((euclidean__axioms.Col F C q) /\ ((euclidean__axioms.Col C q F) /\ ((euclidean__axioms.Col q C F) /\ (euclidean__axioms.Col C F q)))) as H115.
-------------------------------------------------------------------------------------------------------- exact H114.
-------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Col C q F) /\ ((euclidean__axioms.Col q C F) /\ (euclidean__axioms.Col C F q))) as H117.
--------------------------------------------------------------------------------------------------------- exact H116.
--------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* AndElim *) ((euclidean__axioms.Col q C F) /\ (euclidean__axioms.Col C F q)) as H119.
---------------------------------------------------------------------------------------------------------- exact H118.
---------------------------------------------------------------------------------------------------------- destruct H119 as [H119 H120].
exact H119.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (C = C) as H113.
------------------------------------------------------------------------------------------------------ apply (@logic.eq__refl (Point) C).
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col q C C) as H114.
------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H113.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F C) as H115.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq q F) /\ (euclidean__axioms.neq q C))) as H115.
--------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (q) (F) (C) H99).
--------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq q F) /\ (euclidean__axioms.neq q C))) as H116.
---------------------------------------------------------------------------------------------------------- exact H115.
---------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.neq q F) /\ (euclidean__axioms.neq q C)) as H118.
----------------------------------------------------------------------------------------------------------- exact H117.
----------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
exact H116.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F C r) as H116.
--------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (F) (C) (r)).
----------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (F) (C) (r)).
-----------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (q) (C) (r) (F) (C) (H110) (H112) (H114) H115).


--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F r C) as H117.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C F r) /\ ((euclidean__axioms.nCol C r F) /\ ((euclidean__axioms.nCol r F C) /\ ((euclidean__axioms.nCol F r C) /\ (euclidean__axioms.nCol r C F))))) as H117.
----------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder (F) (C) (r) H116).
----------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.nCol C F r) /\ ((euclidean__axioms.nCol C r F) /\ ((euclidean__axioms.nCol r F C) /\ ((euclidean__axioms.nCol F r C) /\ (euclidean__axioms.nCol r C F))))) as H118.
------------------------------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------------------------------ destruct H118 as [H118 H119].
assert (* AndElim *) ((euclidean__axioms.nCol C r F) /\ ((euclidean__axioms.nCol r F C) /\ ((euclidean__axioms.nCol F r C) /\ (euclidean__axioms.nCol r C F)))) as H120.
------------------------------------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.nCol r F C) /\ ((euclidean__axioms.nCol F r C) /\ (euclidean__axioms.nCol r C F))) as H122.
-------------------------------------------------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.nCol F r C) /\ (euclidean__axioms.nCol r C F)) as H124.
--------------------------------------------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
exact H124.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B r p) as H118.
----------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (r) (p)).
------------------------------------------------------------------------------------------------------------intro H118.
apply (@euclidean__tactics.Col__nCol__False (B) (r) (p) (H118)).
-------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (r) (p) (H12) (H10) H20).


----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B p r) as H119.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col r p B) /\ ((euclidean__axioms.Col p B r) /\ ((euclidean__axioms.Col B p r) /\ (euclidean__axioms.Col p r B))))) as H119.
------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (r) (p) H118).
------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col r p B) /\ ((euclidean__axioms.Col p B r) /\ ((euclidean__axioms.Col B p r) /\ (euclidean__axioms.Col p r B))))) as H120.
-------------------------------------------------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------------------------------------------------- destruct H120 as [H120 H121].
assert (* AndElim *) ((euclidean__axioms.Col r p B) /\ ((euclidean__axioms.Col p B r) /\ ((euclidean__axioms.Col B p r) /\ (euclidean__axioms.Col p r B)))) as H122.
--------------------------------------------------------------------------------------------------------------- exact H121.
--------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col p B r) /\ ((euclidean__axioms.Col B p r) /\ (euclidean__axioms.Col p r B))) as H124.
---------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.Col B p r) /\ (euclidean__axioms.Col p r B)) as H126.
----------------------------------------------------------------------------------------------------------------- exact H125.
----------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
exact H126.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B p A) as H120.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A p B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B))))) as H120.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (p) H56).
-------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A p B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B))))) as H121.
--------------------------------------------------------------------------------------------------------------- exact H120.
--------------------------------------------------------------------------------------------------------------- destruct H121 as [H121 H122].
assert (* AndElim *) ((euclidean__axioms.Col A p B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B)))) as H123.
---------------------------------------------------------------------------------------------------------------- exact H122.
---------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B))) as H125.
----------------------------------------------------------------------------------------------------------------- exact H124.
----------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B)) as H127.
------------------------------------------------------------------------------------------------------------------ exact H126.
------------------------------------------------------------------------------------------------------------------ destruct H127 as [H127 H128].
exact H127.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A r) as H121.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B))))) as H121.
--------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (p) (A) H120).
--------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B))))) as H122.
---------------------------------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------------------------------- destruct H122 as [H122 H123].
assert (* AndElim *) ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B)))) as H124.
----------------------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B))) as H126.
------------------------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------------------------ destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col B A p) /\ (euclidean__axioms.Col A p B)) as H128.
------------------------------------------------------------------------------------------------------------------- exact H127.
------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
exact H57.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A p) as H122.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))))) as H122.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (r) H121).
---------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))))) as H123.
----------------------------------------------------------------------------------------------------------------- exact H122.
----------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B)))) as H125.
------------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------------ destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))) as H127.
------------------------------------------------------------------------------------------------------------------- exact H126.
------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B)) as H129.
-------------------------------------------------------------------------------------------------------------------- exact H128.
-------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
exact H56.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A r p) as H123.
---------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (A) (r) (p)).
-----------------------------------------------------------------------------------------------------------------intro H123.
apply (@euclidean__tactics.Col__nCol__False (A) (r) (p) (H123)).
------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (B) (A) (r) (p) (H121) (H122) H58).


---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p r A) as H124.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col r p A) /\ ((euclidean__axioms.Col p A r) /\ ((euclidean__axioms.Col A p r) /\ (euclidean__axioms.Col p r A))))) as H124.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (r) (p) H123).
------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col r p A) /\ ((euclidean__axioms.Col p A r) /\ ((euclidean__axioms.Col A p r) /\ (euclidean__axioms.Col p r A))))) as H125.
------------------------------------------------------------------------------------------------------------------- exact H124.
------------------------------------------------------------------------------------------------------------------- destruct H125 as [H125 H126].
assert (* AndElim *) ((euclidean__axioms.Col r p A) /\ ((euclidean__axioms.Col p A r) /\ ((euclidean__axioms.Col A p r) /\ (euclidean__axioms.Col p r A)))) as H127.
-------------------------------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.Col p A r) /\ ((euclidean__axioms.Col A p r) /\ (euclidean__axioms.Col p r A))) as H129.
--------------------------------------------------------------------------------------------------------------------- exact H128.
--------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col A p r) /\ (euclidean__axioms.Col p r A)) as H131.
---------------------------------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
exact H132.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p r F) as H125.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col p r F) /\ ((euclidean__axioms.Col p F r) /\ ((euclidean__axioms.Col F r p) /\ ((euclidean__axioms.Col r F p) /\ (euclidean__axioms.Col F p r))))) as H125.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (r) (p) (F) H102).
------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p r F) /\ ((euclidean__axioms.Col p F r) /\ ((euclidean__axioms.Col F r p) /\ ((euclidean__axioms.Col r F p) /\ (euclidean__axioms.Col F p r))))) as H126.
-------------------------------------------------------------------------------------------------------------------- exact H125.
-------------------------------------------------------------------------------------------------------------------- destruct H126 as [H126 H127].
assert (* AndElim *) ((euclidean__axioms.Col p F r) /\ ((euclidean__axioms.Col F r p) /\ ((euclidean__axioms.Col r F p) /\ (euclidean__axioms.Col F p r)))) as H128.
--------------------------------------------------------------------------------------------------------------------- exact H127.
--------------------------------------------------------------------------------------------------------------------- destruct H128 as [H128 H129].
assert (* AndElim *) ((euclidean__axioms.Col F r p) /\ ((euclidean__axioms.Col r F p) /\ (euclidean__axioms.Col F p r))) as H130.
---------------------------------------------------------------------------------------------------------------------- exact H129.
---------------------------------------------------------------------------------------------------------------------- destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Col r F p) /\ (euclidean__axioms.Col F p r)) as H132.
----------------------------------------------------------------------------------------------------------------------- exact H131.
----------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
exact H126.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq p r) as H126.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F q) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C q))) as H126.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (q) H101).
-------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F q) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C q))) as H127.
--------------------------------------------------------------------------------------------------------------------- exact H126.
--------------------------------------------------------------------------------------------------------------------- destruct H127 as [H127 H128].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C q)) as H129.
---------------------------------------------------------------------------------------------------------------------- exact H128.
---------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
exact H53.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r A F) as H127.
-------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (r) (A) (F)).
---------------------------------------------------------------------------------------------------------------------intro H127.
apply (@euclidean__tactics.Col__nCol__False (r) (A) (F) (H127)).
----------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (p) (r) (A) (F) (H124) (H125) H126).


-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F r A) as H128.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A r F) /\ ((euclidean__axioms.Col A F r) /\ ((euclidean__axioms.Col F r A) /\ ((euclidean__axioms.Col r F A) /\ (euclidean__axioms.Col F A r))))) as H128.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (r) (A) (F) H127).
---------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A r F) /\ ((euclidean__axioms.Col A F r) /\ ((euclidean__axioms.Col F r A) /\ ((euclidean__axioms.Col r F A) /\ (euclidean__axioms.Col F A r))))) as H129.
----------------------------------------------------------------------------------------------------------------------- exact H128.
----------------------------------------------------------------------------------------------------------------------- destruct H129 as [H129 H130].
assert (* AndElim *) ((euclidean__axioms.Col A F r) /\ ((euclidean__axioms.Col F r A) /\ ((euclidean__axioms.Col r F A) /\ (euclidean__axioms.Col F A r)))) as H131.
------------------------------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------------------------------ destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col F r A) /\ ((euclidean__axioms.Col r F A) /\ (euclidean__axioms.Col F A r))) as H133.
------------------------------------------------------------------------------------------------------------------------- exact H132.
------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col r F A) /\ (euclidean__axioms.Col F A r)) as H135.
-------------------------------------------------------------------------------------------------------------------------- exact H134.
-------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
exact H133.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A r) as H129.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col r F A) /\ ((euclidean__axioms.Col r A F) /\ ((euclidean__axioms.Col A F r) /\ ((euclidean__axioms.Col F A r) /\ (euclidean__axioms.Col A r F))))) as H129.
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (r) (A) H128).
----------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col r F A) /\ ((euclidean__axioms.Col r A F) /\ ((euclidean__axioms.Col A F r) /\ ((euclidean__axioms.Col F A r) /\ (euclidean__axioms.Col A r F))))) as H130.
------------------------------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------------------------------ destruct H130 as [H130 H131].
assert (* AndElim *) ((euclidean__axioms.Col r A F) /\ ((euclidean__axioms.Col A F r) /\ ((euclidean__axioms.Col F A r) /\ (euclidean__axioms.Col A r F)))) as H132.
------------------------------------------------------------------------------------------------------------------------- exact H131.
------------------------------------------------------------------------------------------------------------------------- destruct H132 as [H132 H133].
assert (* AndElim *) ((euclidean__axioms.Col A F r) /\ ((euclidean__axioms.Col F A r) /\ (euclidean__axioms.Col A r F))) as H134.
-------------------------------------------------------------------------------------------------------------------------- exact H133.
-------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.Col F A r) /\ (euclidean__axioms.Col A r F)) as H136.
--------------------------------------------------------------------------------------------------------------------------- exact H135.
--------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
exact H121.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A p) as H130.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))))) as H130.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (r) H129).
------------------------------------------------------------------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col A B r) /\ ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))))) as H131.
------------------------------------------------------------------------------------------------------------------------- exact H130.
------------------------------------------------------------------------------------------------------------------------- destruct H131 as [H131 H132].
assert (* AndElim *) ((euclidean__axioms.Col A r B) /\ ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B)))) as H133.
-------------------------------------------------------------------------------------------------------------------------- exact H132.
-------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col r B A) /\ ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B))) as H135.
--------------------------------------------------------------------------------------------------------------------------- exact H134.
--------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col B r A) /\ (euclidean__axioms.Col r A B)) as H137.
---------------------------------------------------------------------------------------------------------------------------- exact H136.
---------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
exact H122.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A r p) as H131.
------------------------------------------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A p r) as H132.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col r p A) /\ ((euclidean__axioms.Col p A r) /\ ((euclidean__axioms.Col A p r) /\ (euclidean__axioms.Col p r A))))) as H132.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (r) (p) H131).
-------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col r A p) /\ ((euclidean__axioms.Col r p A) /\ ((euclidean__axioms.Col p A r) /\ ((euclidean__axioms.Col A p r) /\ (euclidean__axioms.Col p r A))))) as H133.
--------------------------------------------------------------------------------------------------------------------------- exact H132.
--------------------------------------------------------------------------------------------------------------------------- destruct H133 as [H133 H134].
assert (* AndElim *) ((euclidean__axioms.Col r p A) /\ ((euclidean__axioms.Col p A r) /\ ((euclidean__axioms.Col A p r) /\ (euclidean__axioms.Col p r A)))) as H135.
---------------------------------------------------------------------------------------------------------------------------- exact H134.
---------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col p A r) /\ ((euclidean__axioms.Col A p r) /\ (euclidean__axioms.Col p r A))) as H137.
----------------------------------------------------------------------------------------------------------------------------- exact H136.
----------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.Col A p r) /\ (euclidean__axioms.Col p r A)) as H139.
------------------------------------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------------------------------------ destruct H139 as [H139 H140].
exact H139.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A p B) as H133.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A p B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B))))) as H133.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (p) H130).
--------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A p B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B))))) as H134.
---------------------------------------------------------------------------------------------------------------------------- exact H133.
---------------------------------------------------------------------------------------------------------------------------- destruct H134 as [H134 H135].
assert (* AndElim *) ((euclidean__axioms.Col A p B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B)))) as H136.
----------------------------------------------------------------------------------------------------------------------------- exact H135.
----------------------------------------------------------------------------------------------------------------------------- destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B))) as H138.
------------------------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------------------------ destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col B p A) /\ (euclidean__axioms.Col p A B)) as H140.
------------------------------------------------------------------------------------------------------------------------------- exact H139.
------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
exact H136.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B r) as H134.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B A p) /\ ((euclidean__axioms.Col A B p) /\ (euclidean__axioms.Col B p A))))) as H134.
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (p) (B) H133).
---------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B A p) /\ ((euclidean__axioms.Col A B p) /\ (euclidean__axioms.Col B p A))))) as H135.
----------------------------------------------------------------------------------------------------------------------------- exact H134.
----------------------------------------------------------------------------------------------------------------------------- destruct H135 as [H135 H136].
assert (* AndElim *) ((euclidean__axioms.Col p B A) /\ ((euclidean__axioms.Col B A p) /\ ((euclidean__axioms.Col A B p) /\ (euclidean__axioms.Col B p A)))) as H137.
------------------------------------------------------------------------------------------------------------------------------ exact H136.
------------------------------------------------------------------------------------------------------------------------------ destruct H137 as [H137 H138].
assert (* AndElim *) ((euclidean__axioms.Col B A p) /\ ((euclidean__axioms.Col A B p) /\ (euclidean__axioms.Col B p A))) as H139.
------------------------------------------------------------------------------------------------------------------------------- exact H138.
------------------------------------------------------------------------------------------------------------------------------- destruct H139 as [H139 H140].
assert (* AndElim *) ((euclidean__axioms.Col A B p) /\ (euclidean__axioms.Col B p A)) as H141.
-------------------------------------------------------------------------------------------------------------------------------- exact H140.
-------------------------------------------------------------------------------------------------------------------------------- destruct H141 as [H141 H142].
exact H12.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B p) as H135.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A r) /\ ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A))))) as H135.
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (r) H134).
----------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A r) /\ ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A))))) as H136.
------------------------------------------------------------------------------------------------------------------------------ exact H135.
------------------------------------------------------------------------------------------------------------------------------ destruct H136 as [H136 H137].
assert (* AndElim *) ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A)))) as H138.
------------------------------------------------------------------------------------------------------------------------------- exact H137.
------------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A))) as H140.
-------------------------------------------------------------------------------------------------------------------------------- exact H139.
-------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A)) as H142.
--------------------------------------------------------------------------------------------------------------------------------- exact H141.
--------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
exact H10.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B r p) as H136.
----------------------------------------------------------------------------------------------------------------------------- exact H118.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p r B) as H137.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col r p B) /\ ((euclidean__axioms.Col p B r) /\ ((euclidean__axioms.Col B p r) /\ (euclidean__axioms.Col p r B))))) as H137.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (r) (p) H136).
------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col r B p) /\ ((euclidean__axioms.Col r p B) /\ ((euclidean__axioms.Col p B r) /\ ((euclidean__axioms.Col B p r) /\ (euclidean__axioms.Col p r B))))) as H138.
-------------------------------------------------------------------------------------------------------------------------------- exact H137.
-------------------------------------------------------------------------------------------------------------------------------- destruct H138 as [H138 H139].
assert (* AndElim *) ((euclidean__axioms.Col r p B) /\ ((euclidean__axioms.Col p B r) /\ ((euclidean__axioms.Col B p r) /\ (euclidean__axioms.Col p r B)))) as H140.
--------------------------------------------------------------------------------------------------------------------------------- exact H139.
--------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Col p B r) /\ ((euclidean__axioms.Col B p r) /\ (euclidean__axioms.Col p r B))) as H142.
---------------------------------------------------------------------------------------------------------------------------------- exact H141.
---------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.Col B p r) /\ (euclidean__axioms.Col p r B)) as H144.
----------------------------------------------------------------------------------------------------------------------------------- exact H143.
----------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H144 H145].
exact H145.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col r B F) as H138.
------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (r) (B) (F)).
--------------------------------------------------------------------------------------------------------------------------------intro H138.
apply (@euclidean__tactics.Col__nCol__False (r) (B) (F) (H138)).
---------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (p) (r) (B) (F) (H137) (H125) H126).


------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F r B) as H139.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B r F) /\ ((euclidean__axioms.Col B F r) /\ ((euclidean__axioms.Col F r B) /\ ((euclidean__axioms.Col r F B) /\ (euclidean__axioms.Col F B r))))) as H139.
--------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (r) (B) (F) H138).
--------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B r F) /\ ((euclidean__axioms.Col B F r) /\ ((euclidean__axioms.Col F r B) /\ ((euclidean__axioms.Col r F B) /\ (euclidean__axioms.Col F B r))))) as H140.
---------------------------------------------------------------------------------------------------------------------------------- exact H139.
---------------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H140 H141].
assert (* AndElim *) ((euclidean__axioms.Col B F r) /\ ((euclidean__axioms.Col F r B) /\ ((euclidean__axioms.Col r F B) /\ (euclidean__axioms.Col F B r)))) as H142.
----------------------------------------------------------------------------------------------------------------------------------- exact H141.
----------------------------------------------------------------------------------------------------------------------------------- destruct H142 as [H142 H143].
assert (* AndElim *) ((euclidean__axioms.Col F r B) /\ ((euclidean__axioms.Col r F B) /\ (euclidean__axioms.Col F B r))) as H144.
------------------------------------------------------------------------------------------------------------------------------------ exact H143.
------------------------------------------------------------------------------------------------------------------------------------ destruct H144 as [H144 H145].
assert (* AndElim *) ((euclidean__axioms.Col r F B) /\ (euclidean__axioms.Col F B r)) as H146.
------------------------------------------------------------------------------------------------------------------------------------- exact H145.
------------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
exact H144.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H140.
--------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (A) (B) (C)).
----------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (A) (B) (C)).
-----------------------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper (F) (r) (C) (A) (B) (H117) (H128) (H139) H20).


--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C A B q) as H141.
---------------------------------------------------------------------------------------------------------------------------------- exists F.
split.
----------------------------------------------------------------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------------------------------------------------------ exact H140.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS C d A B) as H142.
----------------------------------------------------------------------------------------------------------------------------------- exists q.
exists F.
exists r.
split.
------------------------------------------------------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------- exact H134.
------------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------------- exact H101.
-------------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------------- exact H16.
--------------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------------------------------------------- exact H19.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C d)) as H143.
------------------------------------------------------------------------------------------------------------------------------------ intro H143.
assert (* Cut *) (exists (K: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.Col A B K) /\ (euclidean__axioms.Col C d K)))) as H144.
------------------------------------------------------------------------------------------------------------------------------------- exact H143.
------------------------------------------------------------------------------------------------------------------------------------- assert (exists K: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.Col A B K) /\ (euclidean__axioms.Col C d K))))) as H145.
-------------------------------------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [K H145].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.Col A B K) /\ (euclidean__axioms.Col C d K)))) as H146.
--------------------------------------------------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H146 as [H146 H147].
assert (* AndElim *) ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.Col A B K) /\ (euclidean__axioms.Col C d K))) as H148.
---------------------------------------------------------------------------------------------------------------------------------------- exact H147.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H148 as [H148 H149].
assert (* AndElim *) ((euclidean__axioms.Col A B K) /\ (euclidean__axioms.Col C d K)) as H150.
----------------------------------------------------------------------------------------------------------------------------------------- exact H149.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H150 as [H150 H151].
assert (* Cut *) (euclidean__axioms.Col C c d) as H152.
------------------------------------------------------------------------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C d c) as H153.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))))) as H153.
-------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (c) (d) H152).
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))))) as H154.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H153.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H154 as [H154 H155].
assert (* AndElim *) ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C)))) as H156.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H155.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H156 H157].
assert (* AndElim *) ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))) as H158.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H157.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H158 H159].
assert (* AndElim *) ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C)) as H160.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H159.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H160 as [H160 H161].
exact H160.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C d) as H154.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F q) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C q))) as H154.
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (q) H101).
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F q) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C q))) as H155.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H154.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H155 H156].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C q)) as H157.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H156.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H157 as [H157 H158].
exact H148.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col d c K) as H155.
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (d) (c) (K)).
----------------------------------------------------------------------------------------------------------------------------------------------intro H155.
apply (@euclidean__tactics.Col__nCol__False (d) (c) (K) (H155)).
-----------------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (C) (d) (c) (K) (H153) (H151) H154).


--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c d K) as H156.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col c d K) /\ ((euclidean__axioms.Col c K d) /\ ((euclidean__axioms.Col K d c) /\ ((euclidean__axioms.Col d K c) /\ (euclidean__axioms.Col K c d))))) as H156.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (d) (c) (K) H155).
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col c d K) /\ ((euclidean__axioms.Col c K d) /\ ((euclidean__axioms.Col K d c) /\ ((euclidean__axioms.Col d K c) /\ (euclidean__axioms.Col K c d))))) as H157.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H156.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H157 as [H157 H158].
assert (* AndElim *) ((euclidean__axioms.Col c K d) /\ ((euclidean__axioms.Col K d c) /\ ((euclidean__axioms.Col d K c) /\ (euclidean__axioms.Col K c d)))) as H159.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H158.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H159 H160].
assert (* AndElim *) ((euclidean__axioms.Col K d c) /\ ((euclidean__axioms.Col d K c) /\ (euclidean__axioms.Col K c d))) as H161.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H160.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H161 H162].
assert (* AndElim *) ((euclidean__axioms.Col d K c) /\ (euclidean__axioms.Col K c d)) as H163.
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H162.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H163 H164].
exact H157.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A B c d) as H157.
----------------------------------------------------------------------------------------------------------------------------------------------- exists K.
split.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H146.
------------------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------------------- exact H22.
------------------------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H150.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H156.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@H24 H157).
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C d) as H144.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F q) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C q))) as H144.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (F) (q) H101).
-------------------------------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F q) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C q))) as H145.
--------------------------------------------------------------------------------------------------------------------------------------- exact H144.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H145 as [H145 H146].
assert (* AndElim *) ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C q)) as H147.
---------------------------------------------------------------------------------------------------------------------------------------- exact H146.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H147 as [H147 H148].
exact H85.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP A B C d) as H145.
-------------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------------- exact H20.
--------------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------------------- exact H143.
----------------------------------------------------------------------------------------------------------------------------------------- exact H142.
-------------------------------------------------------------------------------------------------------------------------------------- exact H145.
Qed.
