Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__NCorder.
Require Export lemma__collinearorder.
Require Export lemma__crisscross.
Require Export lemma__parallelNC.
Require Export lemma__samenotopposite.
Require Export logic.
Require Export proposition__33.
Definition proposition__33B : forall A B C D, (euclidean__defs.Par A B C D) -> ((euclidean__axioms.Cong A B C D) -> ((euclidean__defs.OS A C B D) -> ((euclidean__defs.Par A C B D) /\ (euclidean__axioms.Cong A C B D)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
intro H1.
assert (* Cut *) (~(euclidean__defs.CR A C B D)) as H2.
- intro H2.
assert (exists M, (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H3 by exact H2.
destruct H3 as [M H4].
destruct H4 as [H5 H6].
assert (* Cut *) (euclidean__axioms.Col B M D) as H7.
-- right.
right.
right.
right.
left.
exact H6.
-- assert (* Cut *) (euclidean__axioms.Col B D M) as H8.
--- assert (* Cut *) ((euclidean__axioms.Col M B D) /\ ((euclidean__axioms.Col M D B) /\ ((euclidean__axioms.Col D B M) /\ ((euclidean__axioms.Col B D M) /\ (euclidean__axioms.Col D M B))))) as H8.
---- apply (@lemma__collinearorder.lemma__collinearorder B M D H7).
---- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H15.
--- assert (* Cut *) (euclidean__axioms.nCol A B D) as H9.
---- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H9.
----- apply (@lemma__parallelNC.lemma__parallelNC A B C D H).
----- destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H15.
---- assert (* Cut *) (euclidean__axioms.nCol B D A) as H10.
----- assert (* Cut *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H10.
------ apply (@lemma__NCorder.lemma__NCorder A B D H9).
------ destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H13.
----- assert (* Cut *) (euclidean__axioms.TS A B D C) as H11.
------ exists M.
split.
------- exact H5.
------- split.
-------- exact H8.
-------- exact H10.
------ assert (* Cut *) (~(euclidean__axioms.TS A B D C)) as H12.
------- apply (@lemma__samenotopposite.lemma__samenotopposite A C B D H1).
------- apply (@H12 H11).
- assert (* Cut *) (euclidean__defs.CR A D C B) as H3.
-- apply (@lemma__crisscross.lemma__crisscross A C B D H H2).
-- assert (exists m, (euclidean__axioms.BetS A m D) /\ (euclidean__axioms.BetS C m B)) as H4 by exact H3.
destruct H4 as [m H5].
destruct H5 as [H6 H7].
assert (* Cut *) (euclidean__axioms.BetS B m C) as H8.
--- apply (@euclidean__axioms.axiom__betweennesssymmetry C m B H7).
--- assert (* Cut *) ((euclidean__defs.Par A C B D) /\ (euclidean__axioms.Cong A C B D)) as H9.
---- apply (@proposition__33.proposition__33 A B C D m H H0 H6 H8).
---- exact H9.
Qed.
