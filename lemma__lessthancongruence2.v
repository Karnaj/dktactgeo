Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__congruencetransitive.
Require Export logic.
Definition lemma__lessthancongruence2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.Lt A B C D) -> ((euclidean__axioms.Cong A B E F) -> (euclidean__defs.Lt E F C D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__axioms.BetS C G D) /\ (euclidean__axioms.Cong C G A B)) as H1.
- exact H.
- assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.BetS C G D) /\ (euclidean__axioms.Cong C G A B))) as H2.
-- exact H1.
-- destruct H2 as [G H2].
assert (* AndElim *) ((euclidean__axioms.BetS C G D) /\ (euclidean__axioms.Cong C G A B)) as H3.
--- exact H2.
--- destruct H3 as [H3 H4].
assert (* Cut *) (euclidean__axioms.Cong C G E F) as H5.
---- apply (@lemma__congruencetransitive.lemma__congruencetransitive (C) (G) (A) (B) (E) (F) (H4) H0).
---- assert (* Cut *) (euclidean__defs.Lt E F C D) as H6.
----- exists G.
split.
------ exact H3.
------ exact H5.
----- exact H6.
Qed.
