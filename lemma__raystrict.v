Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export logic.
Definition lemma__raystrict : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__defs.Out A B C) -> (euclidean__axioms.neq A C).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (exists (J: euclidean__axioms.Point), (euclidean__axioms.BetS J A C) /\ (euclidean__axioms.BetS J A B)) as H0.
- exact H.
- assert (exists J: euclidean__axioms.Point, ((euclidean__axioms.BetS J A C) /\ (euclidean__axioms.BetS J A B))) as H1.
-- exact H0.
-- destruct H1 as [J H1].
assert (* AndElim *) ((euclidean__axioms.BetS J A C) /\ (euclidean__axioms.BetS J A B)) as H2.
--- exact H1.
--- destruct H2 as [H2 H3].
assert (* Cut *) (euclidean__axioms.neq A C) as H4.
---- assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq J A) /\ (euclidean__axioms.neq J C))) as H4.
----- apply (@lemma__betweennotequal.lemma__betweennotequal (J) (A) (C) H2).
----- assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq J A) /\ (euclidean__axioms.neq J C))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq J A) /\ (euclidean__axioms.neq J C)) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
exact H5.
---- exact H4.
Qed.
