Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export logic.
Definition lemma__ray2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__defs.Out A B C) -> (euclidean__axioms.neq A B).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS E A C) /\ (euclidean__axioms.BetS E A B)) as H0.
- exact H.
- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS E A C) /\ (euclidean__axioms.BetS E A B))) as H1.
-- exact H0.
-- destruct H1 as [E H1].
assert (* AndElim *) ((euclidean__axioms.BetS E A C) /\ (euclidean__axioms.BetS E A B)) as H2.
--- exact H1.
--- destruct H2 as [H2 H3].
assert (* Cut *) (euclidean__axioms.neq A B) as H4.
---- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E B))) as H4.
----- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (A) (B) H3).
----- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E B))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E B)) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
exact H5.
---- exact H4.
Qed.
