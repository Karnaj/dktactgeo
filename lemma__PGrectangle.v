Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__8__2.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__diagonalsmeet.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__equaltorightisright.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__supplementofright.
Require Export logic.
Require Export proposition__29C.
Require Export proposition__34.
Definition lemma__PGrectangle : forall A B C D, (euclidean__defs.PG A C D B) -> ((euclidean__defs.Per B A C) -> (euclidean__defs.RE A C D B)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A C B D) /\ ((euclidean__defs.CongA C A B B D C) /\ ((euclidean__defs.CongA A B D D C A) /\ (euclidean__axioms.Cong__3 C A B B D C))))) as H1.
- apply (@proposition__34.proposition__34 A B C D H).
- assert (* Cut *) (euclidean__defs.Par A C D B) as H2.
-- destruct H1 as [H2 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H as [H10 H11].
exact H10.
-- assert (* Cut *) (euclidean__axioms.nCol A C B) as H3.
--- destruct H1 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
assert (* Cut *) ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol A C B)))) as H11.
---- apply (@lemma__parallelNC.lemma__parallelNC A C D B H2).
---- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H17.
--- assert (* Cut *) (euclidean__axioms.nCol A B C) as H4.
---- destruct H1 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H12.
----- apply (@lemma__NCorder.lemma__NCorder A C B H3).
----- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H19.
---- assert (* Cut *) (euclidean__axioms.nCol C A B) as H5.
----- destruct H1 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H13.
------ apply (@lemma__NCorder.lemma__NCorder A B C H4).
------ destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H18.
----- assert (* Cut *) (euclidean__defs.CongA C A B B A C) as H6.
------ destruct H1 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA C A B H5).
------ assert (* Cut *) (euclidean__defs.Per C A B) as H7.
------- destruct H1 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
apply (@lemma__8__2.lemma__8__2 B A C H0).
------- assert (* Cut *) (euclidean__axioms.neq A B) as H8.
-------- destruct H1 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
assert (* Cut *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B C)))))) as H16.
--------- apply (@lemma__NCdistinct.lemma__NCdistinct C A B H5).
--------- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H19.
-------- assert (* Cut *) (euclidean__axioms.neq B A) as H9.
--------- destruct H1 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H8).
--------- assert (* Cut *) (euclidean__defs.CongA B A C C A B) as H10.
---------- destruct H1 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric C A B B A C H6).
---------- assert (* Cut *) (euclidean__defs.CongA B A C B D C) as H11.
----------- destruct H1 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive B A C C A B B D C H10 H15).
----------- assert (* Cut *) (euclidean__defs.CongA B D C B A C) as H12.
------------ destruct H1 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric B A C B D C H11).
------------ assert (* Cut *) (euclidean__defs.Per B D C) as H13.
------------- destruct H1 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
apply (@lemma__equaltorightisright.lemma__equaltorightisright B A C B D C H0 H12).
------------- assert (* Cut *) (euclidean__defs.Per C D B) as H14.
-------------- destruct H1 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
apply (@lemma__8__2.lemma__8__2 B D C H13).
-------------- assert (* Cut *) (euclidean__defs.Par A C B D) as H15.
--------------- destruct H1 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
assert (* Cut *) ((euclidean__defs.Par C A D B) /\ ((euclidean__defs.Par A C B D) /\ (euclidean__defs.Par C A B D))) as H23.
---------------- apply (@lemma__parallelflip.lemma__parallelflip A C D B H2).
---------------- destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H26.
--------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H16.
---------------- destruct H1 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H as [H24 H25].
exact H25.
---------------- assert (* Cut *) (euclidean__defs.TP A B C D) as H17.
----------------- destruct H1 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
apply (@lemma__paralleldef2B.lemma__paralleldef2B A B C D H16).
----------------- assert (* Cut *) (euclidean__defs.OS C D A B) as H18.
------------------ destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H1 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H23.
------------------ assert (* Cut *) (euclidean__axioms.neq C A) as H19.
------------------- destruct H1 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
assert (* Cut *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B C)))))) as H27.
-------------------- apply (@lemma__NCdistinct.lemma__NCdistinct C A B H5).
-------------------- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H28.
------------------- assert (* Cut *) (exists E, (euclidean__axioms.BetS B A E) /\ (euclidean__axioms.Cong A E A B)) as H20.
-------------------- destruct H1 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
apply (@lemma__extension.lemma__extension B A A B H9 H8).
-------------------- destruct H20 as [E H21].
destruct H21 as [H22 H23].
destruct H1 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
assert (* Cut *) (euclidean__axioms.BetS E A B) as H32.
--------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B A E H22).
--------------------- assert (* Cut *) (euclidean__defs.RT C A B A B D) as H33.
---------------------- assert (* Cut *) (forall B0 D0 E0 G H33, (euclidean__defs.Par G B0 H33 D0) -> ((euclidean__defs.OS B0 D0 G H33) -> ((euclidean__axioms.BetS E0 G H33) -> (euclidean__defs.RT B0 G H33 G H33 D0)))) as H33.
----------------------- intro B0.
intro D0.
intro E0.
intro G.
intro H33.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA E0 G B0 G H33 D0) /\ (euclidean__defs.RT B0 G H33 G H33 D0)) as __2.
------------------------ apply (@proposition__29C.proposition__29C B0 D0 E0 G H33 __ __0 __1).
------------------------ destruct __2 as [__2 __3].
exact __3.
----------------------- apply (@H33 C D E A B H15 H18 H32).
---------------------- assert (* Cut *) (exists p q r s t, (euclidean__defs.Supp p q r s t) /\ ((euclidean__defs.CongA C A B p q r) /\ (euclidean__defs.CongA A B D s q t))) as H34.
----------------------- assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA C A B X Y U) /\ (euclidean__defs.CongA A B D V Y Z))) as H34 by exact H33.
assert (exists X Y Z U V, (euclidean__defs.Supp X Y U V Z) /\ ((euclidean__defs.CongA C A B X Y U) /\ (euclidean__defs.CongA A B D V Y Z))) as __TmpHyp by exact H34.
destruct __TmpHyp as [x H35].
destruct H35 as [x0 H36].
destruct H36 as [x1 H37].
destruct H37 as [x2 H38].
destruct H38 as [x3 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exists x.
exists x0.
exists x2.
exists x3.
exists x1.
split.
------------------------ exact H40.
------------------------ split.
------------------------- exact H42.
------------------------- exact H43.
----------------------- destruct H34 as [p H35].
destruct H35 as [q H36].
destruct H36 as [r H37].
destruct H37 as [s H38].
destruct H38 as [t H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
assert (* Cut *) (euclidean__defs.CongA p q r C A B) as H44.
------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric C A B p q r H42).
------------------------ assert (* Cut *) (euclidean__defs.Per p q r) as H45.
------------------------- apply (@lemma__equaltorightisright.lemma__equaltorightisright C A B p q r H7 H44).
------------------------- assert (* Cut *) (euclidean__defs.Per s q t) as H46.
-------------------------- assert (* Cut *) (forall A0 B0 C0 D0 F, (euclidean__defs.Supp A0 B0 C0 D0 F) -> ((euclidean__defs.Per A0 B0 C0) -> (euclidean__defs.Per D0 B0 F))) as H46.
--------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro F.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.Per F B0 D0) /\ (euclidean__defs.Per D0 B0 F)) as __1.
---------------------------- apply (@lemma__supplementofright.lemma__supplementofright A0 B0 C0 D0 F __ __0).
---------------------------- destruct __1 as [__1 __2].
exact __2.
--------------------------- apply (@H46 p q r s t H40 H45).
-------------------------- assert (* Cut *) (euclidean__defs.CongA s q t A B D) as H47.
--------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A B D s q t H43).
--------------------------- assert (* Cut *) (euclidean__defs.Per A B D) as H48.
---------------------------- apply (@lemma__equaltorightisright.lemma__equaltorightisright s q t A B D H46 H43).
---------------------------- assert (* Cut *) (euclidean__defs.Per D B A) as H49.
----------------------------- apply (@lemma__8__2.lemma__8__2 A B D H48).
----------------------------- assert (* Cut *) (euclidean__defs.CongA D C A A B D) as H50.
------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A B D D C A H30).
------------------------------ assert (* Cut *) (euclidean__defs.Per D C A) as H51.
------------------------------- apply (@lemma__equaltorightisright.lemma__equaltorightisright A B D D C A H48 H50).
------------------------------- assert (* Cut *) (euclidean__defs.Per A C D) as H52.
-------------------------------- apply (@lemma__8__2.lemma__8__2 D C A H51).
-------------------------------- assert (* Cut *) (exists M, (euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS C M B)) as H53.
--------------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet A C D B H).
--------------------------------- destruct H53 as [M H54].
destruct H54 as [H55 H56].
assert (* Cut *) (euclidean__axioms.neq A D) as H57.
---------------------------------- assert (* Cut *) ((euclidean__axioms.neq M D) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A D))) as H57.
----------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A M D H55).
----------------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H61.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H58.
----------------------------------- assert (* Cut *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C B))) as H58.
------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal C M B H56).
------------------------------------ destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H62.
----------------------------------- assert (* Cut *) (euclidean__defs.CR A D C B) as H59.
------------------------------------ exists M.
split.
------------------------------------- exact H55.
------------------------------------- exact H56.
------------------------------------ assert (* Cut *) (euclidean__defs.RE A C D B) as H60.
------------------------------------- split.
-------------------------------------- exact H0.
-------------------------------------- split.
--------------------------------------- exact H52.
--------------------------------------- split.
---------------------------------------- exact H14.
---------------------------------------- split.
----------------------------------------- exact H49.
----------------------------------------- exact H59.
------------------------------------- exact H60.
Qed.
