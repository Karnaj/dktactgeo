Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export logic.
Definition lemma__rayimpliescollinear : forall A B C, (euclidean__defs.Out A B C) -> (euclidean__axioms.Col A B C).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (exists J, (euclidean__axioms.BetS J A C) /\ (euclidean__axioms.BetS J A B)) as H0 by exact H.
destruct H0 as [J H1].
destruct H1 as [H2 H3].
assert (* Cut *) (euclidean__axioms.neq J A) as H4.
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq J A) /\ (euclidean__axioms.neq J B))) as H4.
-- apply (@lemma__betweennotequal.lemma__betweennotequal J A B H3).
-- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
exact H7.
- assert (* Cut *) (euclidean__axioms.Col J A B) as H5.
-- right.
right.
right.
right.
left.
exact H3.
-- assert (* Cut *) (euclidean__axioms.Col J A C) as H6.
--- right.
right.
right.
right.
left.
exact H2.
--- assert (* Cut *) (euclidean__axioms.Col A B C) as H7.
---- apply (@euclidean__tactics.not__nCol__Col A B C).
-----intro H7.
apply (@euclidean__tactics.Col__nCol__False A B C H7).
------apply (@lemma__collinear4.lemma__collinear4 J A B C H5 H6 H4).


---- exact H7.
Qed.
