Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__NCorder.
Require Export lemma__collinearorder.
Require Export lemma__crisscross.
Require Export lemma__parallelNC.
Require Export lemma__samenotopposite.
Require Export logic.
Require Export proposition__33.
Definition proposition__33B : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.Par A B C D) -> ((euclidean__axioms.Cong A B C D) -> ((euclidean__defs.OS A C B D) -> ((euclidean__defs.Par A C B D) /\ (euclidean__axioms.Cong A C B D)))).
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
assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H3.
-- exact H2.
-- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D))) as H4.
--- exact H3.
--- destruct H4 as [M H4].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* Cut *) (euclidean__axioms.Col B M D) as H7.
----- right.
right.
right.
right.
left.
exact H6.
----- assert (* Cut *) (euclidean__axioms.Col B D M) as H8.
------ assert (* Cut *) ((euclidean__axioms.Col M B D) /\ ((euclidean__axioms.Col M D B) /\ ((euclidean__axioms.Col D B M) /\ ((euclidean__axioms.Col B D M) /\ (euclidean__axioms.Col D M B))))) as H8.
------- apply (@lemma__collinearorder.lemma__collinearorder (B) (M) (D) H7).
------- assert (* AndElim *) ((euclidean__axioms.Col M B D) /\ ((euclidean__axioms.Col M D B) /\ ((euclidean__axioms.Col D B M) /\ ((euclidean__axioms.Col B D M) /\ (euclidean__axioms.Col D M B))))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col M D B) /\ ((euclidean__axioms.Col D B M) /\ ((euclidean__axioms.Col B D M) /\ (euclidean__axioms.Col D M B)))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col D B M) /\ ((euclidean__axioms.Col B D M) /\ (euclidean__axioms.Col D M B))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col B D M) /\ (euclidean__axioms.Col D M B)) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
exact H15.
------ assert (* Cut *) (euclidean__axioms.nCol A B D) as H9.
------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H9.
-------- apply (@lemma__parallelNC.lemma__parallelNC (A) (B) (C) (D) H).
-------- assert (* AndElim *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
exact H15.
------- assert (* Cut *) (euclidean__axioms.nCol B D A) as H10.
-------- assert (* Cut *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H10.
--------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (D) H9).
--------- assert (* AndElim *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A)))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A)) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
exact H13.
-------- assert (* Cut *) (euclidean__axioms.TS A B D C) as H11.
--------- exists M.
split.
---------- exact H5.
---------- split.
----------- exact H8.
----------- exact H10.
--------- assert (* Cut *) (~(euclidean__axioms.TS A B D C)) as H12.
---------- apply (@lemma__samenotopposite.lemma__samenotopposite (A) (C) (B) (D) H1).
---------- apply (@H12 H11).
- assert (* Cut *) (euclidean__defs.CR A D C B) as H3.
-- apply (@lemma__crisscross.lemma__crisscross (A) (C) (B) (D) (H) H2).
-- assert (* Cut *) (exists (m: euclidean__axioms.Point), (euclidean__axioms.BetS A m D) /\ (euclidean__axioms.BetS C m B)) as H4.
--- exact H3.
--- assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.BetS A m D) /\ (euclidean__axioms.BetS C m B))) as H5.
---- exact H4.
---- destruct H5 as [m H5].
assert (* AndElim *) ((euclidean__axioms.BetS A m D) /\ (euclidean__axioms.BetS C m B)) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* Cut *) (euclidean__axioms.BetS B m C) as H8.
------ apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (m) (B) H7).
------ assert (* Cut *) ((euclidean__defs.Par A C B D) /\ (euclidean__axioms.Cong A C B D)) as H9.
------- apply (@proposition__33.proposition__33 (A) (B) (C) (D) (m) (H) (H0) (H6) H8).
------- exact H9.
Qed.
