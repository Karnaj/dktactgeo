Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__supplements.
Require Export logic.
Definition lemma__supplements2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (J: euclidean__axioms.Point) (K: euclidean__axioms.Point) (L: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__defs.RT A B C P Q R) -> ((euclidean__defs.CongA A B C J K L) -> ((euclidean__defs.RT J K L D E F) -> ((euclidean__defs.CongA P Q R D E F) /\ (euclidean__defs.CongA D E F P Q R)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro J.
intro K.
intro L.
intro P.
intro Q.
intro R.
intro H.
intro H0.
intro H1.
assert (* Cut *) (exists (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA P Q R d b e))) as H2.
- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA J K L X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as H2.
-- exact H1.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA J K L X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as __TmpHyp.
--- exact H2.
--- assert (exists X: euclidean__axioms.Point, (exists (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA J K L X Y U) /\ (euclidean__defs.CongA D E F V Y Z)))) as H3.
---- exact __TmpHyp.
---- destruct H3 as [x H3].
assert (exists Y: euclidean__axioms.Point, (exists (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x Y U V Z) /\ ((euclidean__defs.CongA J K L x Y U) /\ (euclidean__defs.CongA D E F V Y Z)))) as H4.
----- exact H3.
----- destruct H4 as [x0 H4].
assert (exists Z: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V Z) /\ ((euclidean__defs.CongA J K L x x0 U) /\ (euclidean__defs.CongA D E F V x0 Z)))) as H5.
------ exact H4.
------ destruct H5 as [x1 H5].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V x1) /\ ((euclidean__defs.CongA J K L x x0 U) /\ (euclidean__defs.CongA D E F V x0 x1)))) as H6.
------- exact H5.
------- destruct H6 as [x2 H6].
assert (exists V: euclidean__axioms.Point, ((euclidean__defs.Supp x x0 x2 V x1) /\ ((euclidean__defs.CongA J K L x x0 x2) /\ (euclidean__defs.CongA D E F V x0 x1)))) as H7.
-------- exact H6.
-------- destruct H7 as [x3 H7].
assert (* AndElim *) ((euclidean__defs.Supp x x0 x2 x3 x1) /\ ((euclidean__defs.CongA J K L x x0 x2) /\ (euclidean__defs.CongA D E F x3 x0 x1))) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.CongA J K L x x0 x2) /\ (euclidean__defs.CongA D E F x3 x0 x1)) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA P Q R V Y Z))) as H12.
----------- exact H.
----------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA P Q R V Y Z))) as __TmpHyp0.
------------ exact H12.
------------ assert (exists X: euclidean__axioms.Point, (exists (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA P Q R V Y Z)))) as H13.
------------- exact __TmpHyp0.
------------- destruct H13 as [x4 H13].
assert (exists Y: euclidean__axioms.Point, (exists (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x4 Y U V Z) /\ ((euclidean__defs.CongA A B C x4 Y U) /\ (euclidean__defs.CongA P Q R V Y Z)))) as H14.
-------------- exact H13.
-------------- destruct H14 as [x5 H14].
assert (exists Z: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x4 x5 U V Z) /\ ((euclidean__defs.CongA A B C x4 x5 U) /\ (euclidean__defs.CongA P Q R V x5 Z)))) as H15.
--------------- exact H14.
--------------- destruct H15 as [x6 H15].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__defs.Supp x4 x5 U V x6) /\ ((euclidean__defs.CongA A B C x4 x5 U) /\ (euclidean__defs.CongA P Q R V x5 x6)))) as H16.
---------------- exact H15.
---------------- destruct H16 as [x7 H16].
assert (exists V: euclidean__axioms.Point, ((euclidean__defs.Supp x4 x5 x7 V x6) /\ ((euclidean__defs.CongA A B C x4 x5 x7) /\ (euclidean__defs.CongA P Q R V x5 x6)))) as H17.
----------------- exact H16.
----------------- destruct H17 as [x8 H17].
assert (* AndElim *) ((euclidean__defs.Supp x4 x5 x7 x8 x6) /\ ((euclidean__defs.CongA A B C x4 x5 x7) /\ (euclidean__defs.CongA P Q R x8 x5 x6))) as H18.
------------------ exact H17.
------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__defs.CongA A B C x4 x5 x7) /\ (euclidean__defs.CongA P Q R x8 x5 x6)) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
exists x4.
exists x5.
exists x7.
exists x8.
exists x6.
split.
-------------------- exact H18.
-------------------- split.
--------------------- exact H20.
--------------------- exact H21.
- assert (exists a: euclidean__axioms.Point, (exists (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA P Q R d b e)))) as H3.
-- exact H2.
-- destruct H3 as [a H3].
assert (exists b: euclidean__axioms.Point, (exists (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA P Q R d b e)))) as H4.
--- exact H3.
--- destruct H4 as [b H4].
assert (exists c: euclidean__axioms.Point, (exists (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA P Q R d b e)))) as H5.
---- exact H4.
---- destruct H5 as [c H5].
assert (exists d: euclidean__axioms.Point, (exists (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA P Q R d b e)))) as H6.
----- exact H5.
----- destruct H6 as [d H6].
assert (exists e: euclidean__axioms.Point, ((euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA P Q R d b e)))) as H7.
------ exact H6.
------ destruct H7 as [e H7].
assert (* AndElim *) ((euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA P Q R d b e))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA P Q R d b e)) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* Cut *) (exists (j: euclidean__axioms.Point) (k: euclidean__axioms.Point) (l: euclidean__axioms.Point) (m: euclidean__axioms.Point) (n: euclidean__axioms.Point), (euclidean__defs.Supp j k l m n) /\ ((euclidean__defs.CongA J K L j k l) /\ (euclidean__defs.CongA D E F m k n))) as H12.
--------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA J K L X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as H12.
---------- exact H1.
---------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA J K L X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as __TmpHyp.
----------- exact H12.
----------- assert (exists X: euclidean__axioms.Point, (exists (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA J K L X Y U) /\ (euclidean__defs.CongA D E F V Y Z)))) as H13.
------------ exact __TmpHyp.
------------ destruct H13 as [x H13].
assert (exists Y: euclidean__axioms.Point, (exists (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x Y U V Z) /\ ((euclidean__defs.CongA J K L x Y U) /\ (euclidean__defs.CongA D E F V Y Z)))) as H14.
------------- exact H13.
------------- destruct H14 as [x0 H14].
assert (exists Z: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V Z) /\ ((euclidean__defs.CongA J K L x x0 U) /\ (euclidean__defs.CongA D E F V x0 Z)))) as H15.
-------------- exact H14.
-------------- destruct H15 as [x1 H15].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V x1) /\ ((euclidean__defs.CongA J K L x x0 U) /\ (euclidean__defs.CongA D E F V x0 x1)))) as H16.
--------------- exact H15.
--------------- destruct H16 as [x2 H16].
assert (exists V: euclidean__axioms.Point, ((euclidean__defs.Supp x x0 x2 V x1) /\ ((euclidean__defs.CongA J K L x x0 x2) /\ (euclidean__defs.CongA D E F V x0 x1)))) as H17.
---------------- exact H16.
---------------- destruct H17 as [x3 H17].
assert (* AndElim *) ((euclidean__defs.Supp x x0 x2 x3 x1) /\ ((euclidean__defs.CongA J K L x x0 x2) /\ (euclidean__defs.CongA D E F x3 x0 x1))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__defs.CongA J K L x x0 x2) /\ (euclidean__defs.CongA D E F x3 x0 x1)) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA P Q R V Y Z))) as H22.
------------------- exact H.
------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA P Q R V Y Z))) as __TmpHyp0.
-------------------- exact H22.
-------------------- assert (exists X: euclidean__axioms.Point, (exists (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA P Q R V Y Z)))) as H23.
--------------------- exact __TmpHyp0.
--------------------- destruct H23 as [x4 H23].
assert (exists Y: euclidean__axioms.Point, (exists (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x4 Y U V Z) /\ ((euclidean__defs.CongA A B C x4 Y U) /\ (euclidean__defs.CongA P Q R V Y Z)))) as H24.
---------------------- exact H23.
---------------------- destruct H24 as [x5 H24].
assert (exists Z: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x4 x5 U V Z) /\ ((euclidean__defs.CongA A B C x4 x5 U) /\ (euclidean__defs.CongA P Q R V x5 Z)))) as H25.
----------------------- exact H24.
----------------------- destruct H25 as [x6 H25].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__defs.Supp x4 x5 U V x6) /\ ((euclidean__defs.CongA A B C x4 x5 U) /\ (euclidean__defs.CongA P Q R V x5 x6)))) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [x7 H26].
assert (exists V: euclidean__axioms.Point, ((euclidean__defs.Supp x4 x5 x7 V x6) /\ ((euclidean__defs.CongA A B C x4 x5 x7) /\ (euclidean__defs.CongA P Q R V x5 x6)))) as H27.
------------------------- exact H26.
------------------------- destruct H27 as [x8 H27].
assert (* AndElim *) ((euclidean__defs.Supp x4 x5 x7 x8 x6) /\ ((euclidean__defs.CongA A B C x4 x5 x7) /\ (euclidean__defs.CongA P Q R x8 x5 x6))) as H28.
-------------------------- exact H27.
-------------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__defs.CongA A B C x4 x5 x7) /\ (euclidean__defs.CongA P Q R x8 x5 x6)) as H30.
--------------------------- exact H29.
--------------------------- destruct H30 as [H30 H31].
exists x.
exists x0.
exists x2.
exists x3.
exists x1.
split.
---------------------------- exact H18.
---------------------------- split.
----------------------------- exact H20.
----------------------------- exact H21.
--------- assert (exists j: euclidean__axioms.Point, (exists (k: euclidean__axioms.Point) (l: euclidean__axioms.Point) (m: euclidean__axioms.Point) (n: euclidean__axioms.Point), (euclidean__defs.Supp j k l m n) /\ ((euclidean__defs.CongA J K L j k l) /\ (euclidean__defs.CongA D E F m k n)))) as H13.
---------- exact H12.
---------- destruct H13 as [j H13].
assert (exists k: euclidean__axioms.Point, (exists (l: euclidean__axioms.Point) (m: euclidean__axioms.Point) (n: euclidean__axioms.Point), (euclidean__defs.Supp j k l m n) /\ ((euclidean__defs.CongA J K L j k l) /\ (euclidean__defs.CongA D E F m k n)))) as H14.
----------- exact H13.
----------- destruct H14 as [k H14].
assert (exists l: euclidean__axioms.Point, (exists (m: euclidean__axioms.Point) (n: euclidean__axioms.Point), (euclidean__defs.Supp j k l m n) /\ ((euclidean__defs.CongA J K L j k l) /\ (euclidean__defs.CongA D E F m k n)))) as H15.
------------ exact H14.
------------ destruct H15 as [l H15].
assert (exists m: euclidean__axioms.Point, (exists (n: euclidean__axioms.Point), (euclidean__defs.Supp j k l m n) /\ ((euclidean__defs.CongA J K L j k l) /\ (euclidean__defs.CongA D E F m k n)))) as H16.
------------- exact H15.
------------- destruct H16 as [m H16].
assert (exists n: euclidean__axioms.Point, ((euclidean__defs.Supp j k l m n) /\ ((euclidean__defs.CongA J K L j k l) /\ (euclidean__defs.CongA D E F m k n)))) as H17.
-------------- exact H16.
-------------- destruct H17 as [n H17].
assert (* AndElim *) ((euclidean__defs.Supp j k l m n) /\ ((euclidean__defs.CongA J K L j k l) /\ (euclidean__defs.CongA D E F m k n))) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__defs.CongA J K L j k l) /\ (euclidean__defs.CongA D E F m k n)) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* Cut *) (euclidean__defs.CongA a b c A B C) as H22.
----------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (a) (b) (c) H10).
----------------- assert (* Cut *) (euclidean__defs.CongA a b c J K L) as H23.
------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (a) (b) (c) (A) (B) (C) (J) (K) (L) (H22) H0).
------------------ assert (* Cut *) (euclidean__defs.CongA a b c j k l) as H24.
------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (a) (b) (c) (J) (K) (L) (j) (k) (l) (H23) H20).
------------------- assert (* Cut *) (euclidean__defs.CongA d b e m k n) as H25.
-------------------- apply (@lemma__supplements.lemma__supplements (a) (b) (c) (d) (e) (j) (k) (l) (m) (n) (H24) (H8) H18).
-------------------- assert (* Cut *) (euclidean__defs.CongA P Q R m k n) as H26.
--------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (P) (Q) (R) (d) (b) (e) (m) (k) (n) (H11) H25).
--------------------- assert (* Cut *) (euclidean__defs.CongA m k n D E F) as H27.
---------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (D) (E) (F) (m) (k) (n) H21).
---------------------- assert (* Cut *) (euclidean__defs.CongA P Q R D E F) as H28.
----------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (P) (Q) (R) (m) (k) (n) (D) (E) (F) (H26) H27).
----------------------- assert (* Cut *) (euclidean__defs.CongA D E F P Q R) as H29.
------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (P) (Q) (R) (D) (E) (F) H28).
------------------------ split.
------------------------- exact H28.
------------------------- exact H29.
Qed.
