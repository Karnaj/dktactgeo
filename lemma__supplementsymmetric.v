Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__ray5.
Require Export logic.
Definition lemma__supplementsymmetric : forall A B C D E, (euclidean__defs.Supp A B C E D) -> (euclidean__defs.Supp D B E C A).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
assert (* Cut *) ((euclidean__defs.Out B C E) /\ (euclidean__axioms.BetS A B D)) as H0.
- assert ((euclidean__defs.Out B C E) /\ (euclidean__axioms.BetS A B D)) as H0 by exact H.
assert ((euclidean__defs.Out B C E) /\ (euclidean__axioms.BetS A B D)) as __TmpHyp by exact H0.
destruct __TmpHyp as [H1 H2].
split.
-- exact H1.
-- exact H2.
- assert (* Cut *) (euclidean__axioms.BetS D B A) as H1.
-- destruct H0 as [H1 H2].
apply (@euclidean__axioms.axiom__betweennesssymmetry A B D H2).
-- assert (* Cut *) (euclidean__defs.Out B E C) as H2.
--- destruct H0 as [H2 H3].
apply (@lemma__ray5.lemma__ray5 B C E H2).
--- assert (* Cut *) (euclidean__defs.Supp D B E C A) as H3.
---- split.
----- exact H2.
----- exact H1.
---- exact H3.
Qed.
