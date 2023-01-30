Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__planeseparation.
Require Export lemma__samesidesymmetric.
Require Export logic.
Definition lemma__samenotopposite : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.OS A B C D) -> (~(euclidean__axioms.TS A C D B)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (euclidean__defs.OS B A C D) as H0.
- assert (* Cut *) ((euclidean__defs.OS B A C D) /\ ((euclidean__defs.OS A B D C) /\ (euclidean__defs.OS B A D C))) as H0.
-- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric (C) (D) (A) (B) H).
-- assert (* AndElim *) ((euclidean__defs.OS B A C D) /\ ((euclidean__defs.OS A B D C) /\ (euclidean__defs.OS B A D C))) as H1.
--- exact H0.
--- destruct H1 as [H1 H2].
assert (* AndElim *) ((euclidean__defs.OS A B D C) /\ (euclidean__defs.OS B A D C)) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
exact H1.
- assert (* Cut *) (~(euclidean__axioms.TS A C D B)) as H1.
-- intro H1.
assert (* Cut *) (euclidean__axioms.TS B C D B) as H2.
--- apply (@lemma__planeseparation.lemma__planeseparation (C) (D) (B) (A) (B) (H0) H1).
--- assert (* Cut *) (exists (M: euclidean__axioms.Point), euclidean__axioms.BetS B M B) as H3.
---- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B X B) /\ ((euclidean__axioms.Col C D X) /\ (euclidean__axioms.nCol C D B))) as H3.
----- exact H2.
----- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B X B) /\ ((euclidean__axioms.Col C D X) /\ (euclidean__axioms.nCol C D B))) as __TmpHyp.
------ exact H3.
------ assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS B X B) /\ ((euclidean__axioms.Col C D X) /\ (euclidean__axioms.nCol C D B)))) as H4.
------- exact __TmpHyp.
------- destruct H4 as [x H4].
assert (* AndElim *) ((euclidean__axioms.BetS B x B) /\ ((euclidean__axioms.Col C D x) /\ (euclidean__axioms.nCol C D B))) as H5.
-------- exact H4.
-------- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Col C D x) /\ (euclidean__axioms.nCol C D B)) as H7.
--------- exact H6.
--------- destruct H7 as [H7 H8].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X B) /\ ((euclidean__axioms.Col C D X) /\ (euclidean__axioms.nCol C D A))) as H9.
---------- exact H1.
---------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X B) /\ ((euclidean__axioms.Col C D X) /\ (euclidean__axioms.nCol C D A))) as __TmpHyp0.
----------- exact H9.
----------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS A X B) /\ ((euclidean__axioms.Col C D X) /\ (euclidean__axioms.nCol C D A)))) as H10.
------------ exact __TmpHyp0.
------------ destruct H10 as [x0 H10].
assert (* AndElim *) ((euclidean__axioms.BetS A x0 B) /\ ((euclidean__axioms.Col C D x0) /\ (euclidean__axioms.nCol C D A))) as H11.
------------- exact H10.
------------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col C D x0) /\ (euclidean__axioms.nCol C D A)) as H13.
-------------- exact H12.
-------------- destruct H13 as [H13 H14].
exists x.
exact H5.
---- assert (exists M: euclidean__axioms.Point, (euclidean__axioms.BetS B M B)) as H4.
----- exact H3.
----- destruct H4 as [M H4].
assert (* Cut *) (~(euclidean__axioms.BetS B M B)) as H5.
------ apply (@euclidean__axioms.axiom__betweennessidentity (B) M).
------ apply (@H5 H4).
-- exact H1.
Qed.
