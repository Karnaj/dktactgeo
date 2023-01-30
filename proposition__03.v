Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__congruencesymmetric.
Require Export lemma__lessthancongruence.
Require Export logic.
Definition proposition__03 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.Lt C D A B) -> ((euclidean__axioms.Cong E F A B) -> (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS E X F) /\ (euclidean__axioms.Cong E X C D))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.Cong A B E F) as H1.
- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (E) (F) (B) H0).
- assert (* Cut *) (euclidean__defs.Lt C D E F) as H2.
-- apply (@lemma__lessthancongruence.lemma__lessthancongruence (C) (D) (A) (B) (E) (F) (H) H1).
-- assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__axioms.BetS E G F) /\ (euclidean__axioms.Cong E G C D)) as H3.
--- exact H2.
--- assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.BetS E G F) /\ (euclidean__axioms.Cong E G C D))) as H4.
---- exact H3.
---- destruct H4 as [G H4].
assert (* AndElim *) ((euclidean__axioms.BetS E G F) /\ (euclidean__axioms.Cong E G C D)) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
exact H2.
Qed.
