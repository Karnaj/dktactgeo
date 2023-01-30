Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__ray5.
Require Export logic.
Definition lemma__supplementsymmetric : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__defs.Supp A B C E D) -> (euclidean__defs.Supp D B E C A).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
assert (* Cut *) ((euclidean__defs.Out B C E) /\ (euclidean__axioms.BetS A B D)) as H0.
- assert (* Cut *) ((euclidean__defs.Out B C E) /\ (euclidean__axioms.BetS A B D)) as H0.
-- exact H.
-- assert (* Cut *) ((euclidean__defs.Out B C E) /\ (euclidean__axioms.BetS A B D)) as __TmpHyp.
--- exact H0.
--- assert (* AndElim *) ((euclidean__defs.Out B C E) /\ (euclidean__axioms.BetS A B D)) as H1.
---- exact __TmpHyp.
---- destruct H1 as [H1 H2].
split.
----- exact H1.
----- exact H2.
- assert (* Cut *) (euclidean__axioms.BetS D B A) as H1.
-- assert (* AndElim *) ((euclidean__defs.Out B C E) /\ (euclidean__axioms.BetS A B D)) as H1.
--- exact H0.
--- destruct H1 as [H1 H2].
apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (D) H2).
-- assert (* Cut *) (euclidean__defs.Out B E C) as H2.
--- assert (* AndElim *) ((euclidean__defs.Out B C E) /\ (euclidean__axioms.BetS A B D)) as H2.
---- exact H0.
---- destruct H2 as [H2 H3].
apply (@lemma__ray5.lemma__ray5 (B) (C) (E) H2).
--- assert (* Cut *) (euclidean__defs.Supp D B E C A) as H3.
---- split.
----- exact H2.
----- exact H1.
---- exact H3.
Qed.
