Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCorder.
Require Export lemma__angledistinct.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__diagonalsmeet.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglesflip.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelflip.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__26A.
Require Export proposition__29B.
Definition proposition__34 : forall A B C D, (euclidean__defs.PG A C D B) -> ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A C B D) /\ ((euclidean__defs.CongA C A B B D C) /\ ((euclidean__defs.CongA A B D D C A) /\ (euclidean__axioms.Cong__3 C A B B D C))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) ((euclidean__defs.Par A C D B) /\ (euclidean__defs.Par A B C D)) as H0.
- assert ((euclidean__defs.Par A C D B) /\ (euclidean__defs.Par A B C D)) as H0 by exact H.
assert ((euclidean__defs.Par A C D B) /\ (euclidean__defs.Par A B C D)) as __TmpHyp by exact H0.
destruct __TmpHyp as [H1 H2].
split.
-- exact H1.
-- exact H2.
- assert (* Cut *) (euclidean__defs.Par A C B D) as H1.
-- destruct H0 as [H1 H2].
assert (* Cut *) ((euclidean__defs.Par C A D B) /\ ((euclidean__defs.Par A C B D) /\ (euclidean__defs.Par C A B D))) as H3.
--- apply (@lemma__parallelflip.lemma__parallelflip A C D B H1).
--- destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
exact H6.
-- assert (* Cut *) (exists M, (euclidean__axioms.BetS A M D) /\ (euclidean__axioms.BetS C M B)) as H2.
--- destruct H0 as [H2 H3].
apply (@lemma__diagonalsmeet.lemma__diagonalsmeet A C D B H).
--- destruct H2 as [M H3].
destruct H3 as [H4 H5].
destruct H0 as [H6 H7].
assert (* Cut *) (euclidean__axioms.BetS B M C) as H8.
---- apply (@euclidean__axioms.axiom__betweennesssymmetry C M B H5).
---- assert (* Cut *) (euclidean__axioms.Col B M C) as H9.
----- right.
right.
right.
right.
left.
exact H8.
----- assert (* Cut *) (euclidean__axioms.Col B C M) as H10.
------ assert (* Cut *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H10.
------- apply (@lemma__collinearorder.lemma__collinearorder B M C H9).
------- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H17.
------ assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H11.
------- assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H11 by exact H1.
assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H11.
destruct __TmpHyp as [x H12].
destruct H12 as [x0 H13].
destruct H13 as [x1 H14].
destruct H14 as [x2 H15].
destruct H15 as [x3 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H37 by exact H7.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H37.
destruct __TmpHyp0 as [x4 H38].
destruct H38 as [x5 H39].
destruct H39 as [x6 H40].
destruct H40 as [x7 H41].
destruct H41 as [x8 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C D B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H63 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C D B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H63.
destruct __TmpHyp1 as [x9 H64].
destruct H64 as [x10 H65].
destruct H65 as [x11 H66].
destruct H66 as [x12 H67].
destruct H67 as [x13 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H59.
------- assert (* Cut *) (euclidean__axioms.neq A B) as H12.
-------- assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H12 by exact H1.
assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H12.
destruct __TmpHyp as [x H13].
destruct H13 as [x0 H14].
destruct H14 as [x1 H15].
destruct H15 as [x2 H16].
destruct H16 as [x3 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H38 by exact H7.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H38.
destruct __TmpHyp0 as [x4 H39].
destruct H39 as [x5 H40].
destruct H40 as [x6 H41].
destruct H41 as [x7 H42].
destruct H42 as [x8 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C D B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H64 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C D B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H64.
destruct __TmpHyp1 as [x9 H65].
destruct H65 as [x10 H66].
destruct H66 as [x11 H67].
destruct H67 as [x12 H68].
destruct H68 as [x13 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H44.
-------- assert (* Cut *) (euclidean__axioms.neq C D) as H13.
--------- assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H13 by exact H1.
assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H13.
destruct __TmpHyp as [x H14].
destruct H14 as [x0 H15].
destruct H15 as [x1 H16].
destruct H16 as [x2 H17].
destruct H17 as [x3 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H39 by exact H7.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H39.
destruct __TmpHyp0 as [x4 H40].
destruct H40 as [x5 H41].
destruct H41 as [x6 H42].
destruct H42 as [x7 H43].
destruct H43 as [x8 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C D B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H65 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col A C U) /\ ((euclidean__axioms.Col A C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A C D B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H65.
destruct __TmpHyp1 as [x9 H66].
destruct H66 as [x10 H67].
destruct H67 as [x11 H68].
destruct H68 as [x12 H69].
destruct H69 as [x13 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H47.
--------- assert (* Cut *) (~(euclidean__axioms.Col B C A)) as H14.
---------- intro H14.
assert (* Cut *) (euclidean__axioms.Col A B C) as H15.
----------- assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H15.
------------ apply (@lemma__collinearorder.lemma__collinearorder B C A H14).
------------ destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H20.
----------- assert (* Cut *) (C = C) as H16.
------------ apply (@logic.eq__refl Point C).
------------ assert (* Cut *) (euclidean__axioms.Col C D C) as H17.
------------- right.
left.
exact H16.
------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H18.
-------------- exists C.
split.
--------------- exact H12.
--------------- split.
---------------- exact H13.
---------------- split.
----------------- exact H15.
----------------- exact H17.
-------------- apply (@H11 H18).
---------- assert (* Cut *) (euclidean__axioms.TS A B C D) as H15.
----------- exists M.
split.
------------ exact H4.
------------ split.
------------- exact H10.
------------- apply (@euclidean__tactics.nCol__notCol B C A H14).
----------- assert (* Cut *) (euclidean__defs.CongA A B C B C D) as H16.
------------ apply (@proposition__29B.proposition__29B A D B C H7 H15).
------------ assert (* Cut *) (~(euclidean__axioms.Col B C D)) as H17.
------------- intro H17.
assert (* Cut *) (euclidean__axioms.Col C D B) as H18.
-------------- assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H18.
--------------- apply (@lemma__collinearorder.lemma__collinearorder B C D H17).
--------------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H21.
-------------- assert (* Cut *) (B = B) as H19.
--------------- apply (@logic.eq__refl Point B).
--------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H20.
---------------- right.
right.
left.
exact H19.
---------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H21.
----------------- exists B.
split.
------------------ exact H12.
------------------ split.
------------------- exact H13.
------------------- split.
-------------------- exact H20.
-------------------- exact H18.
----------------- assert (~(euclidean__defs.Meet A B C D)) as H22 by exact H11.
apply (@H11 H21).
------------- assert (* Cut *) (euclidean__defs.CongA B C D D C B) as H18.
-------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B C D).
---------------apply (@euclidean__tactics.nCol__notCol B C D H17).

-------------- assert (* Cut *) (euclidean__defs.CongA A B C D C B) as H19.
--------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B C B C D D C B H16 H18).
--------------- assert (* Cut *) (euclidean__axioms.Col C B M) as H20.
---------------- assert (* Cut *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col C M B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B))))) as H20.
----------------- apply (@lemma__collinearorder.lemma__collinearorder B C M H10).
----------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H21.
---------------- assert (* Cut *) (euclidean__axioms.nCol C B A) as H21.
----------------- assert (* Cut *) (euclidean__axioms.nCol B C A) as H21.
------------------ apply (@euclidean__tactics.nCol__notCol B C A H14).
------------------ assert (* Cut *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H22.
------------------- apply (@lemma__NCorder.lemma__NCorder B C A H21).
------------------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H23.
----------------- assert (* Cut *) (euclidean__axioms.TS A C B D) as H22.
------------------ exists M.
split.
------------------- exact H4.
------------------- split.
-------------------- exact H20.
-------------------- exact H21.
------------------ assert (* Cut *) (euclidean__defs.CongA A C B C B D) as H23.
------------------- apply (@proposition__29B.proposition__29B A D C B H1 H22).
------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H24.
-------------------- assert (* Cut *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A C B) /\ ((euclidean__axioms.nCol C A B) /\ (euclidean__axioms.nCol A B C))))) as H24.
--------------------- apply (@lemma__NCorder.lemma__NCorder C B A H21).
--------------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H32.
-------------------- assert (* Cut *) (euclidean__defs.CongA B C A A C B) as H25.
--------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B C A).
----------------------apply (@euclidean__tactics.nCol__notCol B C A H14).

--------------------- assert (* Cut *) (euclidean__defs.CongA B C A C B D) as H26.
---------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive B C A A C B C B D H25 H23).
---------------------- assert (euclidean__axioms.Triangle A B C) as H27 by exact H24.
assert (* Cut *) (euclidean__axioms.nCol D C B) as H28.
----------------------- apply (@euclidean__tactics.nCol__notCol D C B).
------------------------apply (@euclidean__tactics.nCol__not__Col D C B).
-------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC A B C D C B H19).


----------------------- assert (euclidean__axioms.Triangle D C B) as H29 by exact H28.
assert (* Cut *) (euclidean__axioms.Cong B C C B) as H30.
------------------------ apply (@euclidean__axioms.cn__equalityreverse B C).
------------------------ assert (* Cut *) ((euclidean__axioms.Cong A B D C) /\ ((euclidean__axioms.Cong A C D B) /\ (euclidean__defs.CongA B A C C D B))) as H31.
------------------------- apply (@proposition__26A.proposition__26A A B C D C B H27 H29 H19 H26 H30).
------------------------- assert (* Cut *) (euclidean__axioms.Cong A B C D) as H32.
-------------------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
assert (* Cut *) ((euclidean__axioms.Cong B A C D) /\ ((euclidean__axioms.Cong B A D C) /\ (euclidean__axioms.Cong A B C D))) as H36.
--------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A B D C H32).
--------------------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H40.
-------------------------- assert (* Cut *) (euclidean__axioms.Cong A C B D) as H33.
--------------------------- destruct H31 as [H33 H34].
destruct H34 as [H35 H36].
assert (* Cut *) ((euclidean__axioms.Cong C A B D) /\ ((euclidean__axioms.Cong C A D B) /\ (euclidean__axioms.Cong A C B D))) as H37.
---------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A C D B H35).
---------------------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H41.
--------------------------- assert (* Cut *) (euclidean__axioms.Cong C A B D) as H34.
---------------------------- destruct H31 as [H34 H35].
destruct H35 as [H36 H37].
assert (* Cut *) ((euclidean__axioms.Cong C A D B) /\ ((euclidean__axioms.Cong C A B D) /\ (euclidean__axioms.Cong A C D B))) as H38.
----------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A C B D H33).
----------------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H41.
---------------------------- assert (* Cut *) (euclidean__axioms.Cong C B B C) as H35.
----------------------------- destruct H31 as [H35 H36].
destruct H36 as [H37 H38].
apply (@euclidean__axioms.cn__equalityreverse C B).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 C A B B D C) as H36.
------------------------------ destruct H31 as [H36 H37].
destruct H37 as [H38 H39].
split.
------------------------------- exact H34.
------------------------------- split.
-------------------------------- exact H36.
-------------------------------- exact H35.
------------------------------ assert (* Cut *) (euclidean__defs.CongA C A B B D C) as H37.
------------------------------- destruct H31 as [H37 H38].
destruct H38 as [H39 H40].
apply (@lemma__equalanglesflip.lemma__equalanglesflip B A C C D B H40).
------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D D A) as H38.
-------------------------------- destruct H31 as [H38 H39].
destruct H39 as [H40 H41].
apply (@euclidean__axioms.cn__equalityreverse A D).
-------------------------------- assert (* Cut *) (A = A) as H39.
--------------------------------- destruct H31 as [H39 H40].
destruct H40 as [H41 H42].
apply (@logic.eq__refl Point A).
--------------------------------- assert (* Cut *) (D = D) as H40.
---------------------------------- destruct H31 as [H40 H41].
destruct H41 as [H42 H43].
apply (@logic.eq__refl Point D).
---------------------------------- assert (* Cut *) (euclidean__axioms.neq A C) as H41.
----------------------------------- destruct H31 as [H41 H42].
destruct H42 as [H43 H44].
assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq C B)))))) as H45.
------------------------------------ apply (@lemma__angledistinct.lemma__angledistinct B A C C D B H44).
------------------------------------ destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H48.
----------------------------------- assert (* Cut *) (euclidean__axioms.neq C A) as H42.
------------------------------------ destruct H31 as [H42 H43].
destruct H43 as [H44 H45].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A C H41).
------------------------------------ assert (* Cut *) (euclidean__axioms.neq C D) as H43.
------------------------------------- destruct H31 as [H43 H44].
destruct H44 as [H45 H46].
assert (* Cut *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq B C)))))) as H47.
-------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct C A B B D C H37).
-------------------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H13.
------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H44.
-------------------------------------- destruct H31 as [H44 H45].
destruct H45 as [H46 H47].
assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq C B)))))) as H48.
--------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct B A C C D B H47).
--------------------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H49.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H45.
--------------------------------------- destruct H31 as [H45 H46].
destruct H46 as [H47 H48].
assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq C B)))))) as H49.
---------------------------------------- apply (@lemma__angledistinct.lemma__angledistinct B A C C D B H48).
---------------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H58.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H46.
---------------------------------------- destruct H31 as [H46 H47].
destruct H47 as [H48 H49].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D B H45).
---------------------------------------- assert (* Cut *) (euclidean__defs.Out C A A) as H47.
----------------------------------------- destruct H31 as [H47 H48].
destruct H48 as [H49 H50].
apply (@lemma__ray4.lemma__ray4 C A A).
------------------------------------------right.
left.
exact H39.

------------------------------------------ exact H42.
----------------------------------------- assert (* Cut *) (euclidean__defs.Out C D D) as H48.
------------------------------------------ destruct H31 as [H48 H49].
destruct H49 as [H50 H51].
apply (@lemma__ray4.lemma__ray4 C D D).
-------------------------------------------right.
left.
exact H40.

------------------------------------------- exact H43.
------------------------------------------ assert (* Cut *) (euclidean__defs.Out B A A) as H49.
------------------------------------------- destruct H31 as [H49 H50].
destruct H50 as [H51 H52].
apply (@lemma__ray4.lemma__ray4 B A A).
--------------------------------------------right.
left.
exact H39.

-------------------------------------------- exact H44.
------------------------------------------- assert (* Cut *) (euclidean__defs.Out B D D) as H50.
-------------------------------------------- destruct H31 as [H50 H51].
destruct H51 as [H52 H53].
apply (@lemma__ray4.lemma__ray4 B D D).
---------------------------------------------right.
left.
exact H40.

--------------------------------------------- exact H46.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A C D) as H51.
--------------------------------------------- destruct H31 as [H51 H52].
destruct H52 as [H53 H54].
assert (* Cut *) ((euclidean__axioms.Cong B A D C) /\ ((euclidean__axioms.Cong B A C D) /\ (euclidean__axioms.Cong A B D C))) as H55.
---------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A B C D H32).
---------------------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H58.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C A B D) as H52.
---------------------------------------------- destruct H31 as [H52 H53].
destruct H53 as [H54 H55].
assert (* Cut *) ((euclidean__axioms.Cong A B D C) /\ ((euclidean__axioms.Cong A B C D) /\ (euclidean__axioms.Cong B A D C))) as H56.
----------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip B A C D H51).
----------------------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H34.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D C A) as H53.
----------------------------------------------- destruct H31 as [H53 H54].
destruct H54 as [H55 H56].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B C A D H52).
----------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B D)) as H54.
------------------------------------------------ intro H54.
assert (* Cut *) (D = D) as H55.
------------------------------------------------- destruct H31 as [H55 H56].
destruct H56 as [H57 H58].
exact H40.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D D) as H56.
-------------------------------------------------- right.
right.
left.
exact H55.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H57.
--------------------------------------------------- exists D.
split.
---------------------------------------------------- exact H12.
---------------------------------------------------- split.
----------------------------------------------------- exact H43.
----------------------------------------------------- split.
------------------------------------------------------ exact H54.
------------------------------------------------------ exact H56.
--------------------------------------------------- apply (@H11 H57).
------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B D D C A) as H55.
------------------------------------------------- exists A.
exists D.
exists D.
exists A.
split.
-------------------------------------------------- exact H49.
-------------------------------------------------- split.
--------------------------------------------------- exact H50.
--------------------------------------------------- split.
---------------------------------------------------- exact H48.
---------------------------------------------------- split.
----------------------------------------------------- exact H47.
----------------------------------------------------- split.
------------------------------------------------------ exact H51.
------------------------------------------------------ split.
------------------------------------------------------- exact H53.
------------------------------------------------------- split.
-------------------------------------------------------- exact H38.
-------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol A B D H54).
------------------------------------------------- split.
-------------------------------------------------- exact H32.
-------------------------------------------------- split.
--------------------------------------------------- exact H33.
--------------------------------------------------- split.
---------------------------------------------------- exact H37.
---------------------------------------------------- split.
----------------------------------------------------- exact H55.
----------------------------------------------------- exact H36.
Qed.
