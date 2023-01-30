Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__NCdistinct.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelsymmetric.
Require Export logic.
Require Export proposition__28B.
Definition proposition__28C : forall B D G H, (euclidean__defs.RT B G H G H D) -> ((euclidean__defs.OS B D G H) -> (euclidean__defs.Par G B H D)).
Proof.
intro B.
intro D.
intro G.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.nCol G H B) as H2.
- assert (exists X U V, (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))))) as H2 by exact H1.
assert (exists X U V, (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))))) as __TmpHyp by exact H2.
destruct __TmpHyp as [x H3].
destruct H3 as [x0 H4].
destruct H4 as [x1 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H14.
- assert (* Cut *) (euclidean__axioms.nCol G H D) as H3.
-- assert (exists X U V, (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))))) as H3 by exact H1.
assert (exists X U V, (euclidean__axioms.Col G H U) /\ ((euclidean__axioms.Col G H V) /\ ((euclidean__axioms.BetS B U X) /\ ((euclidean__axioms.BetS D V X) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol G H D)))))) as __TmpHyp by exact H3.
destruct __TmpHyp as [x H4].
destruct H4 as [x0 H5].
destruct H5 as [x1 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H16.
-- assert (* Cut *) (euclidean__axioms.neq H D) as H4.
--- assert (* Cut *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G)))))) as H4.
---- apply (@lemma__NCdistinct.lemma__NCdistinct G H D H3).
---- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H7.
--- assert (* Cut *) (euclidean__axioms.neq D H) as H5.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric H D H4).
---- assert (* Cut *) (euclidean__axioms.neq G B) as H6.
----- assert (* Cut *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq H B) /\ ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq B H) /\ (euclidean__axioms.neq B G)))))) as H6.
------ apply (@lemma__NCdistinct.lemma__NCdistinct G H B H2).
------ destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H11.
----- assert (* Cut *) (euclidean__axioms.neq B G) as H7.
------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G B H6).
------ assert (* Cut *) (exists A, (euclidean__axioms.BetS B G A) /\ (euclidean__axioms.Cong G A G B)) as H8.
------- apply (@lemma__extension.lemma__extension B G G B H7 H6).
------- destruct H8 as [A H9].
destruct H9 as [H10 H11].
assert (* Cut *) (euclidean__axioms.BetS A G B) as H12.
-------- apply (@euclidean__axioms.axiom__betweennesssymmetry B G A H10).
-------- assert (* Cut *) (exists C, (euclidean__axioms.BetS D H C) /\ (euclidean__axioms.Cong H C H D)) as H13.
--------- apply (@lemma__extension.lemma__extension D H H D H5 H4).
--------- destruct H13 as [C H14].
destruct H14 as [H15 H16].
assert (* Cut *) (euclidean__axioms.BetS C H D) as H17.
---------- apply (@euclidean__axioms.axiom__betweennesssymmetry D H C H15).
---------- assert (* Cut *) (euclidean__defs.Par A B C D) as H18.
----------- apply (@proposition__28B.proposition__28B A B C D G H H12 H17 H0 H1).
----------- assert (* Cut *) (euclidean__axioms.Col D H C) as H19.
------------ right.
right.
right.
right.
left.
exact H15.
------------ assert (* Cut *) (euclidean__axioms.Col C D H) as H20.
------------- assert (* Cut *) ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))))) as H20.
-------------- apply (@lemma__collinearorder.lemma__collinearorder D H C H19).
-------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H25.
------------- assert (* Cut *) (euclidean__axioms.neq H D) as H21.
-------------- assert (* Cut *) ((euclidean__axioms.neq G H) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D G)))))) as H21.
--------------- apply (@lemma__NCdistinct.lemma__NCdistinct G H D H3).
--------------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H4.
-------------- assert (* Cut *) (euclidean__defs.Par A B H D) as H22.
--------------- apply (@lemma__collinearparallel.lemma__collinearparallel A B H C D H18 H20 H21).
--------------- assert (* Cut *) (euclidean__defs.Par H D A B) as H23.
---------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A B H D H22).
---------------- assert (* Cut *) (euclidean__axioms.Col B G A) as H24.
----------------- right.
right.
right.
right.
left.
exact H10.
----------------- assert (* Cut *) (euclidean__axioms.Col A B G) as H25.
------------------ assert (* Cut *) ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B A G) /\ (euclidean__axioms.Col A G B))))) as H25.
------------------- apply (@lemma__collinearorder.lemma__collinearorder B G A H24).
------------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H30.
------------------ assert (* Cut *) (euclidean__defs.Par H D G B) as H26.
------------------- apply (@lemma__collinearparallel.lemma__collinearparallel H D G A B H23 H25 H6).
------------------- assert (* Cut *) (euclidean__defs.Par G B H D) as H27.
-------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric H D G B H26).
-------------------- exact H27.
Qed.
