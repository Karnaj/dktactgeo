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
Definition lemma__righttogether : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (G: euclidean__axioms.Point), (euclidean__defs.Per G A B) -> ((euclidean__defs.Per B A C) -> ((euclidean__axioms.TS G B A C) -> ((euclidean__defs.RT G A B B A C) /\ (euclidean__axioms.BetS G A C)))).
Proof.
intro A.
intro B.
intro C.
intro G.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__defs.Per B A G) as H2.
- apply (@lemma__8__2.lemma__8__2 (G) (A) (B) H).
- assert (* Cut *) (euclidean__axioms.neq A G) as H3.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B G X G) /\ (euclidean__axioms.neq A G)))) as H3.
--- exact H2.
--- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B G X G) /\ (euclidean__axioms.neq A G)))) as __TmpHyp.
---- exact H3.
---- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B G X G) /\ (euclidean__axioms.neq A G))))) as H4.
----- exact __TmpHyp.
----- destruct H4 as [x H4].
assert (* AndElim *) ((euclidean__axioms.BetS B A x) /\ ((euclidean__axioms.Cong B A x A) /\ ((euclidean__axioms.Cong B G x G) /\ (euclidean__axioms.neq A G)))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Cong B A x A) /\ ((euclidean__axioms.Cong B G x G) /\ (euclidean__axioms.neq A G))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Cong B G x G) /\ (euclidean__axioms.neq A G)) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B C X C) /\ (euclidean__axioms.neq A C)))) as H11.
--------- exact H0.
--------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B C X C) /\ (euclidean__axioms.neq A C)))) as __TmpHyp0.
---------- exact H11.
---------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B C X C) /\ (euclidean__axioms.neq A C))))) as H12.
----------- exact __TmpHyp0.
----------- destruct H12 as [x0 H12].
assert (* AndElim *) ((euclidean__axioms.BetS B A x0) /\ ((euclidean__axioms.Cong B A x0 A) /\ ((euclidean__axioms.Cong B C x0 C) /\ (euclidean__axioms.neq A C)))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Cong B A x0 A) /\ ((euclidean__axioms.Cong B C x0 C) /\ (euclidean__axioms.neq A C))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Cong B C x0 C) /\ (euclidean__axioms.neq A C)) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G A X) /\ ((euclidean__axioms.Cong G A X A) /\ ((euclidean__axioms.Cong G B X B) /\ (euclidean__axioms.neq A B)))) as H19.
--------------- exact H.
--------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G A X) /\ ((euclidean__axioms.Cong G A X A) /\ ((euclidean__axioms.Cong G B X B) /\ (euclidean__axioms.neq A B)))) as __TmpHyp1.
---------------- exact H19.
---------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS G A X) /\ ((euclidean__axioms.Cong G A X A) /\ ((euclidean__axioms.Cong G B X B) /\ (euclidean__axioms.neq A B))))) as H20.
----------------- exact __TmpHyp1.
----------------- destruct H20 as [x1 H20].
assert (* AndElim *) ((euclidean__axioms.BetS G A x1) /\ ((euclidean__axioms.Cong G A x1 A) /\ ((euclidean__axioms.Cong G B x1 B) /\ (euclidean__axioms.neq A B)))) as H21.
------------------ exact H20.
------------------ destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Cong G A x1 A) /\ ((euclidean__axioms.Cong G B x1 B) /\ (euclidean__axioms.neq A B))) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Cong G B x1 B) /\ (euclidean__axioms.neq A B)) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
exact H10.
-- assert (* Cut *) (euclidean__axioms.neq G A) as H4.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (G) H3).
--- assert (* Cut *) (exists (D: euclidean__axioms.Point), (euclidean__axioms.BetS G A D) /\ (euclidean__axioms.Cong A D G A)) as H5.
---- apply (@lemma__extension.lemma__extension (G) (A) (G) (A) (H4) H4).
---- assert (exists D: euclidean__axioms.Point, ((euclidean__axioms.BetS G A D) /\ (euclidean__axioms.Cong A D G A))) as H6.
----- exact H5.
----- destruct H6 as [D H6].
assert (* AndElim *) ((euclidean__axioms.BetS G A D) /\ (euclidean__axioms.Cong A D G A)) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* Cut *) (B = B) as H9.
------- apply (@logic.eq__refl (Point) B).
------- assert (* Cut *) (euclidean__axioms.neq A B) as H10.
-------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B G X G) /\ (euclidean__axioms.neq A G)))) as H10.
--------- exact H2.
--------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B G X G) /\ (euclidean__axioms.neq A G)))) as __TmpHyp.
---------- exact H10.
---------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B G X G) /\ (euclidean__axioms.neq A G))))) as H11.
----------- exact __TmpHyp.
----------- destruct H11 as [x H11].
assert (* AndElim *) ((euclidean__axioms.BetS B A x) /\ ((euclidean__axioms.Cong B A x A) /\ ((euclidean__axioms.Cong B G x G) /\ (euclidean__axioms.neq A G)))) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Cong B A x A) /\ ((euclidean__axioms.Cong B G x G) /\ (euclidean__axioms.neq A G))) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Cong B G x G) /\ (euclidean__axioms.neq A G)) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B C X C) /\ (euclidean__axioms.neq A C)))) as H18.
--------------- exact H0.
--------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B C X C) /\ (euclidean__axioms.neq A C)))) as __TmpHyp0.
---------------- exact H18.
---------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS B A X) /\ ((euclidean__axioms.Cong B A X A) /\ ((euclidean__axioms.Cong B C X C) /\ (euclidean__axioms.neq A C))))) as H19.
----------------- exact __TmpHyp0.
----------------- destruct H19 as [x0 H19].
assert (* AndElim *) ((euclidean__axioms.BetS B A x0) /\ ((euclidean__axioms.Cong B A x0 A) /\ ((euclidean__axioms.Cong B C x0 C) /\ (euclidean__axioms.neq A C)))) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Cong B A x0 A) /\ ((euclidean__axioms.Cong B C x0 C) /\ (euclidean__axioms.neq A C))) as H22.
------------------- exact H21.
------------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Cong B C x0 C) /\ (euclidean__axioms.neq A C)) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G A X) /\ ((euclidean__axioms.Cong G A X A) /\ ((euclidean__axioms.Cong G B X B) /\ (euclidean__axioms.neq A B)))) as H26.
--------------------- exact H.
--------------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G A X) /\ ((euclidean__axioms.Cong G A X A) /\ ((euclidean__axioms.Cong G B X B) /\ (euclidean__axioms.neq A B)))) as __TmpHyp1.
---------------------- exact H26.
---------------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS G A X) /\ ((euclidean__axioms.Cong G A X A) /\ ((euclidean__axioms.Cong G B X B) /\ (euclidean__axioms.neq A B))))) as H27.
----------------------- exact __TmpHyp1.
----------------------- destruct H27 as [x1 H27].
assert (* AndElim *) ((euclidean__axioms.BetS G A x1) /\ ((euclidean__axioms.Cong G A x1 A) /\ ((euclidean__axioms.Cong G B x1 B) /\ (euclidean__axioms.neq A B)))) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.Cong G A x1 A) /\ ((euclidean__axioms.Cong G B x1 B) /\ (euclidean__axioms.neq A B))) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Cong G B x1 B) /\ (euclidean__axioms.neq A B)) as H32.
-------------------------- exact H31.
-------------------------- destruct H32 as [H32 H33].
exact H33.
-------- assert (* Cut *) (euclidean__defs.Out A B B) as H11.
--------- apply (@lemma__ray4.lemma__ray4 (A) (B) (B)).
----------right.
left.
exact H9.

---------- exact H10.
--------- assert (* Cut *) (euclidean__defs.Supp G A B B D) as H12.
---------- split.
----------- exact H11.
----------- exact H7.
---------- assert (* Cut *) (euclidean__axioms.nCol B A G) as H13.
----------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G X C) /\ ((euclidean__axioms.Col B A X) /\ (euclidean__axioms.nCol B A G))) as H13.
------------ exact H1.
------------ assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS G X C) /\ ((euclidean__axioms.Col B A X) /\ (euclidean__axioms.nCol B A G))) as __TmpHyp.
------------- exact H13.
------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS G X C) /\ ((euclidean__axioms.Col B A X) /\ (euclidean__axioms.nCol B A G)))) as H14.
-------------- exact __TmpHyp.
-------------- destruct H14 as [x H14].
assert (* AndElim *) ((euclidean__axioms.BetS G x C) /\ ((euclidean__axioms.Col B A x) /\ (euclidean__axioms.nCol B A G))) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col B A x) /\ (euclidean__axioms.nCol B A G)) as H17.
---------------- exact H16.
---------------- destruct H17 as [H17 H18].
exact H18.
----------- assert (* Cut *) (euclidean__axioms.nCol G A B) as H14.
------------ assert (* Cut *) ((euclidean__axioms.nCol A B G) /\ ((euclidean__axioms.nCol A G B) /\ ((euclidean__axioms.nCol G B A) /\ ((euclidean__axioms.nCol B G A) /\ (euclidean__axioms.nCol G A B))))) as H14.
------------- apply (@lemma__NCorder.lemma__NCorder (B) (A) (G) H13).
------------- assert (* AndElim *) ((euclidean__axioms.nCol A B G) /\ ((euclidean__axioms.nCol A G B) /\ ((euclidean__axioms.nCol G B A) /\ ((euclidean__axioms.nCol B G A) /\ (euclidean__axioms.nCol G A B))))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.nCol A G B) /\ ((euclidean__axioms.nCol G B A) /\ ((euclidean__axioms.nCol B G A) /\ (euclidean__axioms.nCol G A B)))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.nCol G B A) /\ ((euclidean__axioms.nCol B G A) /\ (euclidean__axioms.nCol G A B))) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.nCol B G A) /\ (euclidean__axioms.nCol G A B)) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
exact H22.
------------ assert (* Cut *) (euclidean__defs.CongA G A B G A B) as H15.
------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (G) (A) (B) H14).
------------- assert (* Cut *) (euclidean__axioms.Col G A D) as H16.
-------------- right.
right.
right.
right.
left.
exact H7.
-------------- assert (* Cut *) (euclidean__axioms.neq A D) as H17.
--------------- assert (* Cut *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G D))) as H17.
---------------- apply (@lemma__betweennotequal.lemma__betweennotequal (G) (A) (D) H7).
---------------- assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G D))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G D)) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
exact H18.
--------------- assert (* Cut *) (euclidean__axioms.neq D A) as H18.
---------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (D) H17).
---------------- assert (* Cut *) (euclidean__defs.Per D A B) as H19.
----------------- apply (@lemma__collinearright.lemma__collinearright (G) (A) (D) (B) (H) (H16) H18).
----------------- assert (* Cut *) (euclidean__defs.Per B A D) as H20.
------------------ apply (@lemma__8__2.lemma__8__2 (D) (A) (B) H19).
------------------ assert (* Cut *) (euclidean__defs.CongA B A C B A D) as H21.
------------------- apply (@lemma__Euclid4.lemma__Euclid4 (B) (A) (C) (B) (A) (D) (H0) H20).
------------------- assert (* Cut *) (euclidean__defs.RT G A B B A C) as H22.
-------------------- exists G.
exists A.
exists D.
exists B.
exists B.
split.
--------------------- exact H12.
--------------------- split.
---------------------- exact H15.
---------------------- exact H21.
-------------------- assert (* Cut *) (euclidean__axioms.TS C B A G) as H23.
--------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric (B) (A) (G) (C) H1).
--------------------- assert (* Cut *) (euclidean__axioms.BetS G A C) as H24.
---------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__defs.RT A0 B0 C0 D0 B0 E) -> ((euclidean__defs.Out B0 C0 D0) -> ((euclidean__axioms.TS E D0 B0 A0) -> (euclidean__axioms.BetS A0 B0 E)))) as H24.
----------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro E.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.Supp A0 B0 C0 D0 E) /\ (euclidean__axioms.BetS A0 B0 E)) as __2.
------------------------ apply (@proposition__14.proposition__14 (A0) (B0) (C0) (D0) (E) (__) (__0) __1).
------------------------ destruct __2 as [__2 __3].
exact __3.
----------------------- apply (@H24 (G) (A) (B) (B) (C) (H22) (H11) H23).
---------------------- split.
----------------------- exact H22.
----------------------- exact H24.
Qed.
