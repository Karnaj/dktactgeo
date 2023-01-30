Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export logic.
Definition lemma__RTcongruence : forall A B C D E F P Q R, (euclidean__defs.RT A B C D E F) -> ((euclidean__defs.CongA A B C P Q R) -> (euclidean__defs.RT P Q R D E F)).
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
assert (* Cut *) (exists a b c d e, (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e))) as H1.
- assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as H1 by exact H.
assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as __TmpHyp by exact H1.
destruct __TmpHyp as [x H2].
destruct H2 as [x0 H3].
destruct H3 as [x1 H4].
destruct H4 as [x2 H5].
destruct H5 as [x3 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
exists x.
exists x0.
exists x2.
exists x3.
exists x1.
split.
-- exact H7.
-- split.
--- exact H9.
--- exact H10.
- destruct H1 as [a H2].
destruct H2 as [b H3].
destruct H3 as [c H4].
destruct H4 as [d H5].
destruct H5 as [e H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
assert (* Cut *) (euclidean__defs.CongA P Q R A B C) as H11.
-- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A B C P Q R H0).
-- assert (* Cut *) (euclidean__defs.CongA P Q R a b c) as H12.
--- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive P Q R A B C a b c H11 H9).
--- assert (* Cut *) (euclidean__defs.RT P Q R D E F) as H13.
---- exists a.
exists b.
exists e.
exists c.
exists d.
split.
----- exact H7.
----- split.
------ exact H12.
------ exact H10.
---- exact H13.
Qed.
