Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__8__2.
Require Export lemma__Euclid4.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinearright.
Require Export lemma__equalanglesreflexive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__14.
Definition lemma__righttogether : forall A B C G, (euclidean__defs.Per G A B) -> ((euclidean__defs.Per B A C) -> ((euclidean__axioms.TS G B A C) -> ((euclidean__defs.RT G A B B A C) /\ (euclidean__axioms.BetS G A C)))).
Proof.
intro A.
intro B.
intro C.
intro G.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__defs.Per B A G) as H2.
- apply (@lemma__8__2.lemma__8__2 G A B H).
- assert (* Cut *) (euclidean__axioms.neq A G) as H3.
-- assert (exists X, (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B G X G) /\ (euclidean__axioms.neq A G)))) as H3 by exact H2.
assert (exists X, (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B G X G) /\ (euclidean__axioms.neq A G)))) as __TmpHyp by exact H3.
destruct __TmpHyp as [x H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
assert (exists X, (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B C X C) /\ (euclidean__axioms.neq A C)))) as H11 by exact H0.
assert (exists X, (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B C X C) /\ (euclidean__axioms.neq A C)))) as __TmpHyp0 by exact H11.
destruct __TmpHyp0 as [x0 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
assert (exists X, (euclidean__axioms.BetS G A X) /\ ((euclidean__axioms.Cong G A X A) /\ ((euclidean__axioms.Cong G B X B) /\ (euclidean__axioms.neq A B)))) as H19 by exact H.
assert (exists X, (euclidean__axioms.BetS G A X) /\ ((euclidean__axioms.Cong G A X A) /\ ((euclidean__axioms.Cong G B X B) /\ (euclidean__axioms.neq A B)))) as __TmpHyp1 by exact H19.
destruct __TmpHyp1 as [x1 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H10.
-- assert (* Cut *) (euclidean__axioms.neq G A) as H4.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A G H3).
--- assert (* Cut *) (exists D, (euclidean__axioms.BetS G A D) /\ (euclidean__axioms.Cong A D G A)) as H5.
---- apply (@lemma__extension.lemma__extension G A G A H4 H4).
---- destruct H5 as [D H6].
destruct H6 as [H7 H8].
assert (* Cut *) (B = B) as H9.
----- apply (@logic.eq__refl Point B).
----- assert (* Cut *) (euclidean__axioms.neq A B) as H10.
------ assert (exists X, (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B G X G) /\ (euclidean__axioms.neq A G)))) as H10 by exact H2.
assert (exists X, (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B G X G) /\ (euclidean__axioms.neq A G)))) as __TmpHyp by exact H10.
destruct __TmpHyp as [x H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
assert (exists X, (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B C X C) /\ (euclidean__axioms.neq A C)))) as H18 by exact H0.
assert (exists X, (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B C X C) /\ (euclidean__axioms.neq A C)))) as __TmpHyp0 by exact H18.
destruct __TmpHyp0 as [x0 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
assert (exists X, (euclidean__axioms.BetS G A X) /\ ((euclidean__axioms.Cong G A X A) /\ ((euclidean__axioms.Cong G B X B) /\ (euclidean__axioms.neq A B)))) as H26 by exact H.
assert (exists X, (euclidean__axioms.BetS G A X) /\ ((euclidean__axioms.Cong G A X A) /\ ((euclidean__axioms.Cong G B X B) /\ (euclidean__axioms.neq A B)))) as __TmpHyp1 by exact H26.
destruct __TmpHyp1 as [x1 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H33.
------ assert (* Cut *) (euclidean__defs.Out A B B) as H11.
------- apply (@lemma__ray4.lemma__ray4 A B B).
--------right.
left.
exact H9.

-------- exact H10.
------- assert (* Cut *) (euclidean__defs.Supp G A B B D) as H12.
-------- split.
--------- exact H11.
--------- exact H7.
-------- assert (* Cut *) (euclidean__axioms.nCol B A G) as H13.
--------- assert (exists X, (euclidean__axioms.BetS G X C) /\ ((euclidean__axioms.Col B A X) /\ (euclidean__axioms.nCol B A G))) as H13 by exact H1.
assert (exists X, (euclidean__axioms.BetS G X C) /\ ((euclidean__axioms.Col B A X) /\ (euclidean__axioms.nCol B A G))) as __TmpHyp by exact H13.
destruct __TmpHyp as [x H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H18.
--------- assert (* Cut *) (euclidean__axioms.nCol G A B) as H14.
---------- assert (* Cut *) ((euclidean__axioms.nCol A B G) /\ ((euclidean__axioms.nCol A G B) /\ ((euclidean__axioms.nCol G B A) /\ ((euclidean__axioms.nCol B G A) /\ (euclidean__axioms.nCol G A B))))) as H14.
----------- apply (@lemma__NCorder.lemma__NCorder B A G H13).
----------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H22.
---------- assert (* Cut *) (euclidean__defs.CongA G A B G A B) as H15.
----------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive G A B H14).
----------- assert (* Cut *) (euclidean__axioms.Col G A D) as H16.
------------ right.
right.
right.
right.
left.
exact H7.
------------ assert (* Cut *) (euclidean__axioms.neq A D) as H17.
------------- assert (* Cut *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G D))) as H17.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal G A D H7).
-------------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H18.
------------- assert (* Cut *) (euclidean__axioms.neq D A) as H18.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A D H17).
-------------- assert (* Cut *) (euclidean__defs.Per D A B) as H19.
--------------- apply (@lemma__collinearright.lemma__collinearright G A D B H H16 H18).
--------------- assert (* Cut *) (euclidean__defs.Per B A D) as H20.
---------------- apply (@lemma__8__2.lemma__8__2 D A B H19).
---------------- assert (* Cut *) (euclidean__defs.CongA B A C B A D) as H21.
----------------- apply (@lemma__Euclid4.lemma__Euclid4 B A C B A D H0 H20).
----------------- assert (* Cut *) (euclidean__defs.RT G A B B A C) as H22.
------------------ exists G.
exists A.
exists D.
exists B.
exists B.
split.
------------------- exact H12.
------------------- split.
-------------------- exact H15.
-------------------- exact H21.
------------------ assert (* Cut *) (euclidean__axioms.TS C B A G) as H23.
------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric B A G C H1).
------------------- assert (* Cut *) (euclidean__axioms.BetS G A C) as H24.
-------------------- assert (* Cut *) (forall A0 B0 C0 D0 E, (euclidean__defs.RT A0 B0 C0 D0 B0 E) -> ((euclidean__defs.Out B0 C0 D0) -> ((euclidean__axioms.TS E D0 B0 A0) -> (euclidean__axioms.BetS A0 B0 E)))) as H24.
--------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro E.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.Supp A0 B0 C0 D0 E) /\ (euclidean__axioms.BetS A0 B0 E)) as __2.
---------------------- apply (@proposition__14.proposition__14 A0 B0 C0 D0 E __ __0 __1).
---------------------- destruct __2 as [__2 __3].
exact __3.
--------------------- apply (@H24 G A B B C H22 H11 H23).
-------------------- split.
--------------------- exact H22.
--------------------- exact H24.
Qed.
