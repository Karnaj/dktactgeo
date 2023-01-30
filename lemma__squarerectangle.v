Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__PGrectangle.
Require Export lemma__squareparallelogram.
Require Export logic.
Definition lemma__squarerectangle : forall A B C D, (euclidean__defs.SQ A B C D) -> (euclidean__defs.RE A B C D).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (euclidean__defs.PG A B C D) as H0.
- apply (@lemma__squareparallelogram.lemma__squareparallelogram A B C D H).
- assert (* Cut *) (euclidean__defs.Per D A B) as H1.
-- destruct H as [H1 H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H7.
-- assert (* Cut *) (euclidean__defs.RE A B C D) as H2.
--- apply (@lemma__PGrectangle.lemma__PGrectangle A D B C H0 H1).
--- exact H2.
Qed.
