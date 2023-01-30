Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export logic.
Definition lemma__RTcongruence : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__defs.RT A B C D E F) -> ((euclidean__defs.CongA A B C P Q R) -> (euclidean__defs.RT P Q R D E F)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro P.
intro Q.
intro R.
intro H.
intro H0.
assert (* Cut *) (exists (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e))) as H1.
- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as H1.
-- exact H.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as __TmpHyp.
--- exact H1.
--- assert (exists X: euclidean__axioms.Point, (exists (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D E F V Y Z)))) as H2.
---- exact __TmpHyp.
---- destruct H2 as [x H2].
assert (exists Y: euclidean__axioms.Point, (exists (Z: euclidean__axioms.Point) (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x Y U V Z) /\ ((euclidean__defs.CongA A B C x Y U) /\ (euclidean__defs.CongA D E F V Y Z)))) as H3.
----- exact H2.
----- destruct H3 as [x0 H3].
assert (exists Z: euclidean__axioms.Point, (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V Z) /\ ((euclidean__defs.CongA A B C x x0 U) /\ (euclidean__defs.CongA D E F V x0 Z)))) as H4.
------ exact H3.
------ destruct H4 as [x1 H4].
assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__defs.Supp x x0 U V x1) /\ ((euclidean__defs.CongA A B C x x0 U) /\ (euclidean__defs.CongA D E F V x0 x1)))) as H5.
------- exact H4.
------- destruct H5 as [x2 H5].
assert (exists V: euclidean__axioms.Point, ((euclidean__defs.Supp x x0 x2 V x1) /\ ((euclidean__defs.CongA A B C x x0 x2) /\ (euclidean__defs.CongA D E F V x0 x1)))) as H6.
-------- exact H5.
-------- destruct H6 as [x3 H6].
assert (* AndElim *) ((euclidean__defs.Supp x x0 x2 x3 x1) /\ ((euclidean__defs.CongA A B C x x0 x2) /\ (euclidean__defs.CongA D E F x3 x0 x1))) as H7.
--------- exact H6.
--------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.CongA A B C x x0 x2) /\ (euclidean__defs.CongA D E F x3 x0 x1)) as H9.
---------- exact H8.
---------- destruct H9 as [H9 H10].
exists x.
exists x0.
exists x2.
exists x3.
exists x1.
split.
----------- exact H7.
----------- split.
------------ exact H9.
------------ exact H10.
- assert (exists a: euclidean__axioms.Point, (exists (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)))) as H2.
-- exact H1.
-- destruct H2 as [a H2].
assert (exists b: euclidean__axioms.Point, (exists (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)))) as H3.
--- exact H2.
--- destruct H3 as [b H3].
assert (exists c: euclidean__axioms.Point, (exists (d: euclidean__axioms.Point) (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)))) as H4.
---- exact H3.
---- destruct H4 as [c H4].
assert (exists d: euclidean__axioms.Point, (exists (e: euclidean__axioms.Point), (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)))) as H5.
----- exact H4.
----- destruct H5 as [d H5].
assert (exists e: euclidean__axioms.Point, ((euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)))) as H6.
------ exact H5.
------ destruct H6 as [e H6].
assert (* AndElim *) ((euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e)) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* Cut *) (euclidean__defs.CongA P Q R A B C) as H11.
--------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (P) (Q) (R) H0).
--------- assert (* Cut *) (euclidean__defs.CongA P Q R a b c) as H12.
---------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (P) (Q) (R) (A) (B) (C) (a) (b) (c) (H11) H9).
---------- assert (* Cut *) (euclidean__defs.RT P Q R D E F) as H13.
----------- exists a.
exists b.
exists e.
exists c.
exists d.
split.
------------ exact H7.
------------ split.
------------- exact H12.
------------- exact H10.
----------- exact H13.
Qed.
