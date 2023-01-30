Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglestransitive.
Require Export lemma__supplementsymmetric.
Require Export logic.
Definition lemma__RTsymmetric : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.RT A B C D E F) -> (euclidean__defs.RT D E F A B C).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
assert (* Cut *) (exists (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e))) as H0.
- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as H0.
-- exact H.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as __TmpHyp.
--- exact H0.
--- assert (exists X: euclidean__axioms.Point, (exists (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D E F V Y Z)))) as H1.
---- exact __TmpHyp.
---- destruct H1 as [x H1].
assert (exists Y: euclidean__axioms.Point, (exists (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x Y U V Z) /\ ((euclidean__defs.CongA A B C x Y U) /\ (euclidean__defs.CongA D E F V Y Z)))) as H2.
----- exact H1.
----- destruct H2 as [x0 H2].
assert (exists Z: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V Z) /\ ((euclidean__defs.CongA A B C x x0 U) /\ (euclidean__defs.CongA D E F V x0 Z)))) as H3.
------ exact H2.
------ destruct H3 as [x1 H3].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V x1) /\ ((euclidean__defs.CongA A B C x x0 U) /\ (euclidean__defs.CongA D E F V x0 x1)))) as H4.
------- exact H3.
------- destruct H4 as [x2 H4].
assert (exists V: euclidean__axioms.Point, ((euclidean__defs.Supp x x0 x2 V x1) /\ ((euclidean__defs.CongA A B C x x0 x2) /\ (euclidean__defs.CongA D E F V x0 x1)))) as H5.
-------- exact H4.
-------- destruct H5 as [x3 H5].
assert (* AndElim *) ((euclidean__defs.Supp x x0 x2 x3 x1) /\ ((euclidean__defs.CongA A B C x x0 x2) /\ (euclidean__defs.CongA D E F x3 x0 x1))) as H6.
--------- exact H5.
--------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.CongA A B C x x0 x2) /\ (euclidean__defs.CongA D E F x3 x0 x1)) as H8.
---------- exact H7.
---------- destruct H8 as [H8 H9].
exists x.
exists x0.
exists x2.
exists x3.
exists x1.
split.
----------- exact H6.
----------- split.
------------ exact H8.
------------ exact H9.
- assert (exists a: euclidean__axioms.Point, (exists (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)))) as H1.
-- exact H0.
-- destruct H1 as [a H1].
assert (exists b: euclidean__axioms.Point, (exists (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)))) as H2.
--- exact H1.
--- destruct H2 as [b H2].
assert (exists c: euclidean__axioms.Point, (exists (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)))) as H3.
---- exact H2.
---- destruct H3 as [c H3].
assert (exists d: euclidean__axioms.Point, (exists (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)))) as H4.
----- exact H3.
----- destruct H4 as [d H4].
assert (exists e: euclidean__axioms.Point, ((euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)))) as H5.
------ exact H4.
------ destruct H5 as [e H5].
assert (* AndElim *) ((euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* Cut *) (euclidean__defs.Supp e b d c a) as H10.
--------- apply (@lemma__supplementsymmetric.lemma__supplementsymmetric (a) (b) (c) (e) (d) H6).
--------- assert (* Cut *) (euclidean__axioms.nCol d b e) as H11.
---------- apply (@euclidean__tactics.nCol__notCol (d) (b) (e)).
-----------apply (@euclidean__tactics.nCol__not__Col (d) (b) (e)).
------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (D) (E) (F) (d) (b) (e) H9).


---------- assert (* Cut *) (euclidean__defs.CongA d b e e b d) as H12.
----------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (d) (b) (e) H11).
----------- assert (* Cut *) (euclidean__axioms.nCol a b c) as H13.
------------ apply (@euclidean__tactics.nCol__notCol (a) (b) (c)).
-------------apply (@euclidean__tactics.nCol__not__Col (a) (b) (c)).
--------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (B) (C) (a) (b) (c) H8).


------------ assert (* Cut *) (euclidean__defs.CongA a b c c b a) as H14.
------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (a) (b) (c) H13).
------------- assert (* Cut *) (euclidean__defs.CongA D E F e b d) as H15.
-------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (D) (E) (F) (d) (b) (e) (e) (b) (d) (H9) H12).
-------------- assert (* Cut *) (euclidean__defs.CongA A B C c b a) as H16.
--------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (A) (B) (C) (a) (b) (c) (c) (b) (a) (H8) H14).
--------------- assert (* Cut *) (euclidean__defs.RT D E F A B C) as H17.
---------------- exists e.
exists b.
exists a.
exists d.
exists c.
split.
----------------- exact H10.
----------------- split.
------------------ exact H15.
------------------ exact H16.
---------------- exact H17.
Qed.
