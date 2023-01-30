Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export logic.
Definition lemma__raystrict : forall A B C, (euclidean__defs.Out A B C) -> (euclidean__axioms.neq A C).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (exists J, (euclidean__axioms.BetS J A C) /\ (euclidean__axioms.BetS J A B)) as H0 by exact H.
destruct H0 as [J H1].
destruct H1 as [H2 H3].
assert (* Cut *) (euclidean__axioms.neq A C) as H4.
- assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq J A) /\ (euclidean__axioms.neq J C))) as H4.
-- apply (@lemma__betweennotequal.lemma__betweennotequal J A C H2).
-- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
exact H5.
- exact H4.
Qed.
