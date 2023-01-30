Require Export euclidean__axioms.
Require Export lemma__NCorder.
Require Export lemma__collinearorder.
Require Export logic.
Definition lemma__oppositesideflip : forall A B P Q, (euclidean__axioms.TS P A B Q) -> (euclidean__axioms.TS P B A Q).
Proof.
intro A.
intro B.
intro P.
intro Q.
intro H.
assert (exists r, (euclidean__axioms.BetS P r Q) /\ ((euclidean__axioms.Col A B r) /\ (euclidean__axioms.nCol A B P))) as H0 by exact H.
destruct H0 as [r H1].
destruct H1 as [H2 H3].
destruct H3 as [H4 H5].
assert (* Cut *) (euclidean__axioms.nCol B A P) as H6.
- assert (* Cut *) ((euclidean__axioms.nCol B A P) /\ ((euclidean__axioms.nCol B P A) /\ ((euclidean__axioms.nCol P A B) /\ ((euclidean__axioms.nCol A P B) /\ (euclidean__axioms.nCol P B A))))) as H6.
-- apply (@lemma__NCorder.lemma__NCorder A B P H5).
-- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H7.
- assert (* Cut *) (euclidean__axioms.Col B A r) as H7.
-- assert (* Cut *) ((euclidean__axioms.Col B A r) /\ ((euclidean__axioms.Col B r A) /\ ((euclidean__axioms.Col r A B) /\ ((euclidean__axioms.Col A r B) /\ (euclidean__axioms.Col r B A))))) as H7.
--- apply (@lemma__collinearorder.lemma__collinearorder A B r H4).
--- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H8.
-- assert (* Cut *) (euclidean__axioms.TS P B A Q) as H8.
--- exists r.
split.
---- exact H2.
---- split.
----- exact H7.
----- exact H6.
--- exact H8.
Qed.
