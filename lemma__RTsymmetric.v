Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglestransitive.
Require Export lemma__supplementsymmetric.
Require Export logic.
Definition lemma__RTsymmetric : forall A B C D E F, (euclidean__defs.RT A B C D E F) -> (euclidean__defs.RT D E F A B C).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
assert (* Cut *) (exists a b c d e, (euclidean__defs.Supp a b c d e) /\ ((euclidean__defs.CongA A B C a b c) /\ (euclidean__defs.CongA D E F d b e))) as H0.
- assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as H0 by exact H.
assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA A B C X Y U) /\ (euclidean__defs.CongA D E F V Y Z))) as __TmpHyp by exact H0.
destruct __TmpHyp as [x H1].
destruct H1 as [x0 H2].
destruct H2 as [x1 H3].
destruct H3 as [x2 H4].
destruct H4 as [x3 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
exists x.
exists x0.
exists x2.
exists x3.
exists x1.
split.
-- exact H6.
-- split.
--- exact H8.
--- exact H9.
- destruct H0 as [a H1].
destruct H1 as [b H2].
destruct H2 as [c H3].
destruct H3 as [d H4].
destruct H4 as [e H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
assert (* Cut *) (euclidean__defs.Supp e b d c a) as H10.
-- apply (@lemma__supplementsymmetric.lemma__supplementsymmetric a b c e d H6).
-- assert (* Cut *) (euclidean__axioms.nCol d b e) as H11.
--- apply (@euclidean__tactics.nCol__notCol d b e).
----apply (@euclidean__tactics.nCol__not__Col d b e).
-----apply (@lemma__equalanglesNC.lemma__equalanglesNC D E F d b e H9).


--- assert (* Cut *) (euclidean__defs.CongA d b e e b d) as H12.
---- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA d b e H11).
---- assert (* Cut *) (euclidean__axioms.nCol a b c) as H13.
----- apply (@euclidean__tactics.nCol__notCol a b c).
------apply (@euclidean__tactics.nCol__not__Col a b c).
-------apply (@lemma__equalanglesNC.lemma__equalanglesNC A B C a b c H8).


----- assert (* Cut *) (euclidean__defs.CongA a b c c b a) as H14.
------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA a b c H13).
------ assert (* Cut *) (euclidean__defs.CongA D E F e b d) as H15.
------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive D E F d b e e b d H9 H12).
------- assert (* Cut *) (euclidean__defs.CongA A B C c b a) as H16.
-------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B C a b c c b a H8 H14).
-------- assert (* Cut *) (euclidean__defs.RT D E F A B C) as H17.
--------- exists e.
exists b.
exists a.
exists d.
exists c.
split.
---------- exact H10.
---------- split.
----------- exact H15.
----------- exact H16.
--------- exact H17.
Qed.
