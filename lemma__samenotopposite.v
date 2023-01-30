Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__planeseparation.
Require Export lemma__samesidesymmetric.
Require Export logic.
Definition lemma__samenotopposite : forall A B C D, (euclidean__defs.OS A B C D) -> (~(euclidean__axioms.TS A C D B)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (euclidean__defs.OS B A C D) as H0.
- assert (* Cut *) ((euclidean__defs.OS B A C D) /\ ((euclidean__defs.OS A B D C) /\ (euclidean__defs.OS B A D C))) as H0.
-- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric C D A B H).
-- destruct H0 as [H1 H2].
destruct H2 as [H3 H4].
exact H1.
- assert (* Cut *) (~(euclidean__axioms.TS A C D B)) as H1.
-- intro H1.
assert (* Cut *) (euclidean__axioms.TS B C D B) as H2.
--- apply (@lemma__planeseparation.lemma__planeseparation C D B A B H0 H1).
--- assert (* Cut *) (exists M, euclidean__axioms.BetS B M B) as H3.
---- assert (exists X, (euclidean__axioms.BetS B X B) /\ ((euclidean__axioms.Col C D X) /\ (euclidean__axioms.nCol C D B))) as H3 by exact H2.
assert (exists X, (euclidean__axioms.BetS B X B) /\ ((euclidean__axioms.Col C D X) /\ (euclidean__axioms.nCol C D B))) as __TmpHyp by exact H3.
destruct __TmpHyp as [x H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
assert (exists X, (euclidean__axioms.BetS A X B) /\ ((euclidean__axioms.Col C D X) /\ (euclidean__axioms.nCol C D A))) as H9 by exact H1.
assert (exists X, (euclidean__axioms.BetS A X B) /\ ((euclidean__axioms.Col C D X) /\ (euclidean__axioms.nCol C D A))) as __TmpHyp0 by exact H9.
destruct __TmpHyp0 as [x0 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exists x.
exact H5.
---- destruct H3 as [M H4].
assert (* Cut *) (~(euclidean__axioms.BetS B M B)) as H5.
----- apply (@euclidean__axioms.axiom__betweennessidentity B M).
----- apply (@H5 H4).
-- exact H1.
Qed.
