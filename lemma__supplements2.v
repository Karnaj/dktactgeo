Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__supplements.
Require Export logic.
Definition lemma__supplements2 : forall A B C D E F J K L P Q R, (euclidean__defs.RT A B C P Q R) -> ((euclidean__defs.CongA A B C J K L) -> ((euclidean__defs.RT J K L D E F) -> ((euclidean__defs.CongA P Q R D E F) /\ (euclidean__defs.CongA D E F P Q R)))).
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
assert (* Cut *) (exists a b c d e, (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA P Q R d b e))) as H2.
- assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA J K L X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as H2 by exact H1.
assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA J K L X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as __TmpHyp by exact H2.
destruct __TmpHyp as [x H3].
destruct H3 as [x0 H4].
destruct H4 as [x1 H5].
destruct H5 as [x2 H6].
destruct H6 as [x3 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA P Q R V Y Z))) as H12 by exact H.
assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA P Q R V Y Z))) as __TmpHyp0 by exact H12.
destruct __TmpHyp0 as [x4 H13].
destruct H13 as [x5 H14].
destruct H14 as [x6 H15].
destruct H15 as [x7 H16].
destruct H16 as [x8 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exists x4.
exists x5.
exists x7.
exists x8.
exists x6.
split.
-- exact H18.
-- split.
--- exact H20.
--- exact H21.
- destruct H2 as [a H3].
destruct H3 as [b H4].
destruct H4 as [c H5].
destruct H5 as [d H6].
destruct H6 as [e H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
assert (* Cut *) (exists j k l m n, (euclidean__defs.Supp j k l m n) /\ ((euclidean__defs.CongA J K L j k l) /\ (euclidean__defs.CongA D E F m k n))) as H12.
-- assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA J K L X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as H12 by exact H1.
assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA J K L X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as __TmpHyp by exact H12.
destruct __TmpHyp as [x H13].
destruct H13 as [x0 H14].
destruct H14 as [x1 H15].
destruct H15 as [x2 H16].
destruct H16 as [x3 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA P Q R V Y Z))) as H22 by exact H.
assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA P Q R V Y Z))) as __TmpHyp0 by exact H22.
destruct __TmpHyp0 as [x4 H23].
destruct H23 as [x5 H24].
destruct H24 as [x6 H25].
destruct H25 as [x7 H26].
destruct H26 as [x8 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exists x.
exists x0.
exists x2.
exists x3.
exists x1.
split.
--- exact H18.
--- split.
---- exact H20.
---- exact H21.
-- destruct H12 as [j H13].
destruct H13 as [k H14].
destruct H14 as [l H15].
destruct H15 as [m H16].
destruct H16 as [n H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
assert (* Cut *) (euclidean__defs.CongA a b c A B C) as H22.
--- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A B C a b c H10).
--- assert (* Cut *) (euclidean__defs.CongA a b c J K L) as H23.
---- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive a b c A B C J K L H22 H0).
---- assert (* Cut *) (euclidean__defs.CongA a b c j k l) as H24.
----- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive a b c J K L j k l H23 H20).
----- assert (* Cut *) (euclidean__defs.CongA d b e m k n) as H25.
------ apply (@lemma__supplements.lemma__supplements a b c d e j k l m n H24 H8 H18).
------ assert (* Cut *) (euclidean__defs.CongA P Q R m k n) as H26.
------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive P Q R d b e m k n H11 H25).
------- assert (* Cut *) (euclidean__defs.CongA m k n D E F) as H27.
-------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric D E F m k n H21).
-------- assert (* Cut *) (euclidean__defs.CongA P Q R D E F) as H28.
--------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive P Q R m k n D E F H26 H27).
--------- assert (* Cut *) (euclidean__defs.CongA D E F P Q R) as H29.
---------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric P Q R D E F H28).
---------- split.
----------- exact H28.
----------- exact H29.
Qed.
