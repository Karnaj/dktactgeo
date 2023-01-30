Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__PGrectangle.
Require Export lemma__squareparallelogram.
Require Export logic.
Definition lemma__squarerectangle : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.SQ A B C D) -> (euclidean__defs.RE A B C D).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (euclidean__defs.PG A B C D) as H0.
- apply (@lemma__squareparallelogram.lemma__squareparallelogram (A) (B) (C) (D) H).
- assert (* Cut *) (euclidean__defs.Per D A B) as H1.
-- assert (* AndElim *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H1.
--- exact H.
--- destruct H1 as [H1 H2].
assert (* AndElim *) ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A)) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
exact H7.
-- assert (* Cut *) (euclidean__defs.RE A B C D) as H2.
--- apply (@lemma__PGrectangle.lemma__PGrectangle (A) (D) (B) (C) (H0) H1).
--- exact H2.
Qed.
