Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Definition lemma__PGflip : forall A B C D, (euclidean__defs.PG A B C D) -> (euclidean__defs.PG B A D C).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H0.
- assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H0 by exact H.
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp by exact H0.
destruct __TmpHyp as [H1 H2].
split.
-- exact H1.
-- exact H2.
- assert (* Cut *) (euclidean__defs.Par B A D C) as H1.
-- destruct H0 as [H1 H2].
assert (* Cut *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H3.
--- apply (@lemma__parallelflip.lemma__parallelflip A B C D H1).
--- destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
exact H7.
-- assert (* Cut *) (euclidean__defs.Par B C A D) as H2.
--- destruct H0 as [H2 H3].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A D B C H3).
--- assert (* Cut *) (euclidean__defs.PG B A D C) as H3.
---- split.
----- exact H1.
----- exact H2.
---- exact H3.
Qed.
