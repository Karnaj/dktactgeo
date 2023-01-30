Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Definition lemma__PGflip : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.PG A B C D) -> (euclidean__defs.PG B A D C).
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
- assert (* Cut *) (euclidean__defs.Par B A D C) as H1.
-- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H1.
--- exact H0.
--- destruct H1 as [H1 H2].
assert (* Cut *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H3.
---- apply (@lemma__parallelflip.lemma__parallelflip (A) (B) (C) (D) H1).
---- assert (* AndElim *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H4.
----- exact H3.
----- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C)) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
exact H7.
-- assert (* Cut *) (euclidean__defs.Par B C A D) as H2.
--- assert (* AndElim *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H2.
---- exact H0.
---- destruct H2 as [H2 H3].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric (A) (D) (B) (C) H3).
--- assert (* Cut *) (euclidean__defs.PG B A D C) as H3.
---- split.
----- exact H1.
----- exact H2.
---- exact H3.
Qed.
