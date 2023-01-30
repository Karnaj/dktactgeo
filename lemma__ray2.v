Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export logic.
Definition lemma__ray2 : forall A B C, (euclidean__defs.Out A B C) -> (euclidean__axioms.neq A B).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (exists E, (euclidean__axioms.BetS E A C) /\ (euclidean__axioms.BetS E A B)) as H0 by exact H.
destruct H0 as [E H1].
destruct H1 as [H2 H3].
assert (* Cut *) (euclidean__axioms.neq A B) as H4.
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E B))) as H4.
-- apply (@lemma__betweennotequal.lemma__betweennotequal E A B H3).
-- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
exact H5.
- exact H4.
Qed.
