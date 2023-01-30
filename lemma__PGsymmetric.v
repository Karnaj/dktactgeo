Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Definition lemma__PGsymmetric : forall A B C D, (euclidean__defs.PG A B C D) -> (euclidean__defs.PG C D A B).
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
- assert (* Cut *) (euclidean__defs.Par C D A B) as H1.
-- destruct H0 as [H1 H2].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A B C D H1).
-- assert (* Cut *) (euclidean__defs.Par B C A D) as H2.
--- destruct H0 as [H2 H3].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A D B C H3).
--- assert (* Cut *) (euclidean__defs.Par C B D A) as H3.
---- destruct H0 as [H3 H4].
assert (* Cut *) ((euclidean__defs.Par C B A D) /\ ((euclidean__defs.Par B C D A) /\ (euclidean__defs.Par C B D A))) as H5.
----- apply (@lemma__parallelflip.lemma__parallelflip B C A D H2).
----- destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
exact H9.
---- assert (* Cut *) (euclidean__defs.PG C D A B) as H4.
----- split.
------ exact H1.
------ exact H3.
----- exact H4.
Qed.
