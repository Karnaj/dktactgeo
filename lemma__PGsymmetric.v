Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Definition lemma__PGsymmetric : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.PG A B C D) -> (euclidean__defs.PG C D A B).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H0.
- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H0.
-- exact H.
-- assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp.
--- exact H0.
--- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H1.
---- exact __TmpHyp.
---- destruct H1 as [H1 H2].
split.
----- exact H1.
----- exact H2.
- assert (* Cut *) (euclidean__defs.Par C D A B) as H1.
-- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H1.
--- exact H0.
--- destruct H1 as [H1 H2].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (B) (C) (D) H1).
-- assert (* Cut *) (euclidean__defs.Par B C A D) as H2.
--- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H2.
---- exact H0.
---- destruct H2 as [H2 H3].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (D) (B) (C) H3).
--- assert (* Cut *) (euclidean__defs.Par C B D A) as H3.
---- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H3.
----- exact H0.
----- destruct H3 as [H3 H4].
assert (* Cut *) ((euclidean__defs.Par C B A D) /\ ((euclidean__defs.Par B C D A) /\ (euclidean__defs.Par C B D A))) as H5.
------ apply (@lemma__parallelflip.lemma__parallelflip (B) (C) (A) (D) H2).
------ assert (* AndElim *) ((euclidean__defs.Par C B A D) /\ ((euclidean__defs.Par B C D A) /\ (euclidean__defs.Par C B D A))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.Par B C D A) /\ (euclidean__defs.Par C B D A)) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
exact H9.
---- assert (* Cut *) (euclidean__defs.PG C D A B) as H4.
----- split.
------ exact H1.
------ exact H3.
----- exact H4.
Qed.
