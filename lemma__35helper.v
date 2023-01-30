Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__diagonalsmeet.
Require Export lemma__equalitysymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export lemma__lessthantransitive.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__trichotomy2.
Require Export logic.
Require Export proposition__34.
Definition lemma__35helper : forall A B C D E F, (euclidean__defs.PG A B C D) -> ((euclidean__defs.PG E B C F) -> ((euclidean__axioms.BetS A D F) -> ((euclidean__axioms.Col A E F) -> (euclidean__axioms.BetS A E F)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H3.
- assert ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H3 by exact H0.
assert ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as __TmpHyp by exact H3.
destruct __TmpHyp as [H4 H5].
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H6 by exact H.
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp0 by exact H6.
destruct __TmpHyp0 as [H7 H8].
split.
-- exact H7.
-- exact H8.
- assert (* Cut *) ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H4.
-- assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H4 by exact H3.
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp by exact H4.
destruct __TmpHyp as [H5 H6].
assert ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as H7 by exact H0.
assert ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par E F B C)) as __TmpHyp0 by exact H7.
destruct __TmpHyp0 as [H8 H9].
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H10 by exact H.
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp1 by exact H10.
destruct __TmpHyp1 as [H11 H12].
split.
--- exact H8.
--- exact H9.
-- assert (* Cut *) (euclidean__defs.Par A B D C) as H5.
--- destruct H4 as [H5 H6].
destruct H3 as [H7 H8].
assert (* Cut *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H9.
---- apply (@lemma__parallelflip.lemma__parallelflip A B C D H7).
---- destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
exact H12.
--- assert (* Cut *) (euclidean__defs.Par E B F C) as H6.
---- destruct H4 as [H6 H7].
destruct H3 as [H8 H9].
assert (* Cut *) ((euclidean__defs.Par B E C F) /\ ((euclidean__defs.Par E B F C) /\ (euclidean__defs.Par B E F C))) as H10.
----- apply (@lemma__parallelflip.lemma__parallelflip E B C F H6).
----- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H13.
---- assert (* Cut *) (euclidean__axioms.Cong A D B C) as H7.
----- destruct H4 as [H7 H8].
destruct H3 as [H9 H10].
assert (* Cut *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H11.
------ apply (@proposition__34.proposition__34 A D B C H).
------ destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H12.
----- assert (* Cut *) (euclidean__axioms.Cong E F B C) as H8.
------ destruct H4 as [H8 H9].
destruct H3 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.Cong E F B C) /\ ((euclidean__axioms.Cong E B F C) /\ ((euclidean__defs.CongA B E F F C B) /\ ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B))))) as H12.
------- apply (@proposition__34.proposition__34 E F B C H0).
------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H13.
------ assert (* Cut *) (euclidean__axioms.Cong B C E F) as H9.
------- destruct H4 as [H9 H10].
destruct H3 as [H11 H12].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B E F C H8).
------- assert (* Cut *) (euclidean__axioms.Cong A D E F) as H10.
-------- destruct H4 as [H10 H11].
destruct H3 as [H12 H13].
apply (@lemma__congruencetransitive.lemma__congruencetransitive A D B C E F H7 H9).
-------- assert (* Cut *) (euclidean__axioms.Col A D F) as H11.
--------- right.
right.
right.
right.
left.
exact H1.
--------- assert (* Cut *) (euclidean__axioms.Col F A E) as H12.
---------- destruct H4 as [H12 H13].
destruct H3 as [H14 H15].
assert (* Cut *) ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A))))) as H16.
----------- apply (@lemma__collinearorder.lemma__collinearorder A E F H2).
----------- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H21.
---------- assert (* Cut *) (euclidean__axioms.Col F A D) as H13.
----------- destruct H4 as [H13 H14].
destruct H3 as [H15 H16].
assert (* Cut *) ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))))) as H17.
------------ apply (@lemma__collinearorder.lemma__collinearorder A D F H11).
------------ destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H22.
----------- assert (* Cut *) (euclidean__axioms.neq A F) as H14.
------------ destruct H4 as [H14 H15].
destruct H3 as [H16 H17].
assert (* Cut *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A F))) as H18.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal A D F H1).
------------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H22.
------------ assert (* Cut *) (euclidean__axioms.neq F A) as H15.
------------- destruct H4 as [H15 H16].
destruct H3 as [H17 H18].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A F H14).
------------- assert (* Cut *) (euclidean__axioms.Col A E D) as H16.
-------------- destruct H4 as [H16 H17].
destruct H3 as [H18 H19].
apply (@euclidean__tactics.not__nCol__Col A E D).
---------------intro H20.
apply (@euclidean__tactics.Col__nCol__False A E D H20).
----------------apply (@lemma__collinear4.lemma__collinear4 F A E D H12 H13 H15).


-------------- assert (* Cut *) (exists M, (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H17.
--------------- destruct H4 as [H17 H18].
destruct H3 as [H19 H20].
apply (@lemma__diagonalsmeet.lemma__diagonalsmeet A B C D H).
--------------- destruct H17 as [M H18].
destruct H18 as [H19 H20].
destruct H4 as [H21 H22].
destruct H3 as [H23 H24].
assert (* Cut *) (euclidean__axioms.BetS D M B) as H25.
---------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B M D H20).
---------------- assert (* Cut *) (euclidean__axioms.BetS C M A) as H26.
----------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A M C H19).
----------------- assert (euclidean__axioms.BetS B M D) as H27 by exact H20.
assert (* Cut *) (exists m, (euclidean__axioms.BetS E m C) /\ (euclidean__axioms.BetS B m F)) as H28.
------------------ apply (@lemma__diagonalsmeet.lemma__diagonalsmeet E B C F H0).
------------------ destruct H28 as [m H29].
destruct H29 as [H30 H31].
assert (* Cut *) (euclidean__axioms.BetS F m B) as H32.
------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B m F H31).
------------------- assert (euclidean__axioms.BetS B m F) as H33 by exact H31.
assert (* Cut *) (euclidean__axioms.nCol A D B) as H34.
-------------------- assert (* Cut *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H34.
--------------------- apply (@lemma__parallelNC.lemma__parallelNC A D B C H24).
--------------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H35.
-------------------- assert (euclidean__axioms.Col A D F) as H35 by exact H11.
assert (* Cut *) (A = A) as H36.
--------------------- apply (@logic.eq__refl Point A).
--------------------- assert (* Cut *) (euclidean__axioms.Col A D A) as H37.
---------------------- right.
left.
exact H36.
---------------------- assert (* Cut *) (euclidean__axioms.nCol A F B) as H38.
----------------------- apply (@euclidean__tactics.nCol__notCol A F B).
------------------------apply (@euclidean__tactics.nCol__not__Col A F B).
-------------------------apply (@lemma__NChelper.lemma__NChelper A D B A F H34 H37 H35 H14).


----------------------- assert (* Cut *) (exists Q, (euclidean__axioms.BetS B Q F) /\ (euclidean__axioms.BetS A M Q)) as H39.
------------------------ apply (@euclidean__axioms.postulate__Pasch__outer B A D M F H27 H1 H38).
------------------------ destruct H39 as [Q H40].
destruct H40 as [H41 H42].
assert (* Cut *) (euclidean__axioms.Col A M Q) as H43.
------------------------- right.
right.
right.
right.
left.
exact H42.
------------------------- assert (* Cut *) (euclidean__axioms.Col A M C) as H44.
-------------------------- right.
right.
right.
right.
left.
exact H19.
-------------------------- assert (* Cut *) (euclidean__axioms.Col M A Q) as H45.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col M A Q) /\ ((euclidean__axioms.Col M Q A) /\ ((euclidean__axioms.Col Q A M) /\ ((euclidean__axioms.Col A Q M) /\ (euclidean__axioms.Col Q M A))))) as H45.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder A M Q H43).
---------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H46.
--------------------------- assert (* Cut *) (euclidean__axioms.Col M A C) as H46.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col M A C) /\ ((euclidean__axioms.Col M C A) /\ ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A))))) as H46.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder A M C H44).
----------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H47.
---------------------------- assert (* Cut *) (euclidean__axioms.neq A M) as H47.
----------------------------- assert (* Cut *) ((euclidean__axioms.neq M Q) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A Q))) as H47.
------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A M Q H42).
------------------------------ destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H50.
----------------------------- assert (* Cut *) (euclidean__axioms.neq M A) as H48.
------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A M H47).
------------------------------ assert (* Cut *) (euclidean__axioms.Col A Q C) as H49.
------------------------------- apply (@euclidean__tactics.not__nCol__Col A Q C).
--------------------------------intro H49.
apply (@euclidean__tactics.Col__nCol__False A Q C H49).
---------------------------------apply (@lemma__collinear4.lemma__collinear4 M A Q C H45 H46 H48).


------------------------------- assert (A = A) as H50 by exact H36.
assert (* Cut *) (C = C) as H51.
-------------------------------- apply (@logic.eq__refl Point C).
-------------------------------- assert (* Cut *) (euclidean__axioms.Col F A A) as H52.
--------------------------------- right.
right.
left.
exact H50.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col C C B) as H53.
---------------------------------- left.
exact H51.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq A F) as H54.
----------------------------------- assert (* Cut *) ((euclidean__axioms.neq M Q) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A Q))) as H54.
------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A M Q H42).
------------------------------------ destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H14.
----------------------------------- assert (euclidean__axioms.neq F A) as H55 by exact H15.
assert (* Cut *) (euclidean__axioms.neq B C) as H56.
------------------------------------ assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H56 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H56.
destruct __TmpHyp as [x H57].
destruct H57 as [x0 H58].
destruct H58 as [x1 H59].
destruct H59 as [x2 H60].
destruct H60 as [x3 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H82 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H82.
destruct __TmpHyp0 as [x4 H83].
destruct H83 as [x5 H84].
destruct H84 as [x6 H85].
destruct H85 as [x7 H86].
destruct H86 as [x8 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H108 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H108.
destruct __TmpHyp1 as [x9 H109].
destruct H109 as [x10 H110].
destruct H110 as [x11 H111].
destruct H111 as [x12 H112].
destruct H112 as [x13 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H134 by exact H21.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H134.
destruct __TmpHyp2 as [x14 H135].
destruct H135 as [x15 H136].
destruct H136 as [x16 H137].
destruct H137 as [x17 H138].
destruct H138 as [x18 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H160 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H160.
destruct __TmpHyp3 as [x19 H161].
destruct H161 as [x20 H162].
destruct H162 as [x21 H163].
destruct H163 as [x22 H164].
destruct H164 as [x23 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
destruct H183 as [H184 H185].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H186 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H186.
destruct __TmpHyp4 as [x24 H187].
destruct H187 as [x25 H188].
destruct H188 as [x26 H189].
destruct H189 as [x27 H190].
destruct H190 as [x28 H191].
destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
destruct H199 as [H200 H201].
destruct H201 as [H202 H203].
destruct H203 as [H204 H205].
destruct H205 as [H206 H207].
destruct H207 as [H208 H209].
destruct H209 as [H210 H211].
exact H168.
------------------------------------ assert (* Cut *) (euclidean__axioms.neq C B) as H57.
------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B C H56).
------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet F A C B)) as H58.
-------------------------------------- intro H58.
assert (exists p, (euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F A p) /\ (euclidean__axioms.Col C B p)))) as H59 by exact H58.
destruct H59 as [p H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
assert (euclidean__axioms.Col A D F) as H67 by exact H35.
assert (* Cut *) (euclidean__axioms.Col F A D) as H68.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))))) as H68.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A D F H67).
---------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H73.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H69.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D F) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A F))) as H69.
----------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A D F H1).
----------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H72.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D p) as H70.
----------------------------------------- apply (@euclidean__tactics.not__nCol__Col A D p).
------------------------------------------intro H70.
apply (@euclidean__tactics.Col__nCol__False A D p H70).
-------------------------------------------apply (@lemma__collinear4.lemma__collinear4 F A D p H68 H65 H61).


----------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C p) as H71.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B C p) /\ ((euclidean__axioms.Col B p C) /\ ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C))))) as H71.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C B p H66).
------------------------------------------- destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H72.
------------------------------------------ assert (* Cut *) (euclidean__defs.Meet A D B C) as H72.
------------------------------------------- exists p.
split.
-------------------------------------------- exact H69.
-------------------------------------------- split.
--------------------------------------------- exact H56.
--------------------------------------------- split.
---------------------------------------------- exact H70.
---------------------------------------------- exact H71.
------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A D B C)) as H73.
-------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H73 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H73.
destruct __TmpHyp as [x H74].
destruct H74 as [x0 H75].
destruct H75 as [x1 H76].
destruct H76 as [x2 H77].
destruct H77 as [x3 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H99 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H99.
destruct __TmpHyp0 as [x4 H100].
destruct H100 as [x5 H101].
destruct H101 as [x6 H102].
destruct H102 as [x7 H103].
destruct H103 as [x8 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H125 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H125.
destruct __TmpHyp1 as [x9 H126].
destruct H126 as [x10 H127].
destruct H127 as [x11 H128].
destruct H128 as [x12 H129].
destruct H129 as [x13 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H151 by exact H21.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H151.
destruct __TmpHyp2 as [x14 H152].
destruct H152 as [x15 H153].
destruct H153 as [x16 H154].
destruct H154 as [x17 H155].
destruct H155 as [x18 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H177 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H177.
destruct __TmpHyp3 as [x19 H178].
destruct H178 as [x20 H179].
destruct H179 as [x21 H180].
destruct H180 as [x22 H181].
destruct H181 as [x23 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
destruct H198 as [H199 H200].
destruct H200 as [H201 H202].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H203 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H203.
destruct __TmpHyp4 as [x24 H204].
destruct H204 as [x25 H205].
destruct H205 as [x26 H206].
destruct H206 as [x27 H207].
destruct H207 as [x28 H208].
destruct H208 as [H209 H210].
destruct H210 as [H211 H212].
destruct H212 as [H213 H214].
destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
destruct H218 as [H219 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
exact H199.
-------------------------------------------- apply (@H73 H72).
-------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F Q B) as H59.
--------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B Q F H41).
--------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A D B C)) as H60.
---------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H60 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H60.
destruct __TmpHyp as [x H61].
destruct H61 as [x0 H62].
destruct H62 as [x1 H63].
destruct H63 as [x2 H64].
destruct H64 as [x3 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H86 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H86.
destruct __TmpHyp0 as [x4 H87].
destruct H87 as [x5 H88].
destruct H88 as [x6 H89].
destruct H89 as [x7 H90].
destruct H90 as [x8 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H112 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H112.
destruct __TmpHyp1 as [x9 H113].
destruct H113 as [x10 H114].
destruct H114 as [x11 H115].
destruct H115 as [x12 H116].
destruct H116 as [x13 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H138 by exact H21.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H138.
destruct __TmpHyp2 as [x14 H139].
destruct H139 as [x15 H140].
destruct H140 as [x16 H141].
destruct H141 as [x17 H142].
destruct H142 as [x18 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H164 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H164.
destruct __TmpHyp3 as [x19 H165].
destruct H165 as [x20 H166].
destruct H166 as [x21 H167].
destruct H167 as [x22 H168].
destruct H168 as [x23 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
destruct H183 as [H184 H185].
destruct H185 as [H186 H187].
destruct H187 as [H188 H189].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H190 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H190.
destruct __TmpHyp4 as [x24 H191].
destruct H191 as [x25 H192].
destruct H192 as [x26 H193].
destruct H193 as [x27 H194].
destruct H194 as [x28 H195].
destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
destruct H199 as [H200 H201].
destruct H201 as [H202 H203].
destruct H203 as [H204 H205].
destruct H205 as [H206 H207].
destruct H207 as [H208 H209].
destruct H209 as [H210 H211].
destruct H211 as [H212 H213].
destruct H213 as [H214 H215].
exact H186.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C Q) as H61.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q A C) /\ ((euclidean__axioms.Col Q C A) /\ ((euclidean__axioms.Col C A Q) /\ ((euclidean__axioms.Col A C Q) /\ (euclidean__axioms.Col C Q A))))) as H61.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A Q C H49).
------------------------------------------ destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H68.
----------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A Q C) as H62.
------------------------------------------ apply (@lemma__collinearbetween.lemma__collinearbetween F A C B A C Q H52 H53 H55 H57 H55 H57 H58 H59 H61).
------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS C Q A) as H63.
------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A Q C H62).
------------------------------------------- assert (* Cut *) (~(A = E)) as H64.
-------------------------------------------- intro H64.
assert (* Cut *) (euclidean__axioms.Cong A F A F) as H65.
--------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive A F).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F E F) as H66.
---------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.BetS A0 D F) -> ((euclidean__axioms.Col A0 E F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__axioms.Col F A0 E) -> ((euclidean__axioms.Col F A0 D) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((euclidean__axioms.Col A0 E D) -> ((euclidean__axioms.BetS A0 M C) -> ((euclidean__axioms.BetS C M A0) -> ((euclidean__axioms.nCol A0 D B) -> ((euclidean__axioms.Col A0 D F) -> ((A0 = A0) -> ((euclidean__axioms.Col A0 D A0) -> ((euclidean__axioms.nCol A0 F B) -> ((euclidean__axioms.BetS A0 M Q) -> ((euclidean__axioms.Col A0 M Q) -> ((euclidean__axioms.Col A0 M C) -> ((euclidean__axioms.Col M A0 Q) -> ((euclidean__axioms.Col M A0 C) -> ((euclidean__axioms.neq A0 M) -> ((euclidean__axioms.neq M A0) -> ((euclidean__axioms.Col A0 Q C) -> ((A0 = A0) -> ((euclidean__axioms.Col F A0 A0) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((~(euclidean__defs.Meet F A0 C B)) -> ((~(euclidean__defs.Meet A0 D B C)) -> ((euclidean__axioms.Col A0 C Q) -> ((euclidean__axioms.BetS A0 Q C) -> ((euclidean__axioms.BetS C Q A0) -> ((euclidean__axioms.Cong A0 F A0 F) -> (euclidean__axioms.Cong A0 F E F))))))))))))))))))))))))))))))))))))))))) with (x := A).
-----------------------------------------------intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
exact H104.

----------------------------------------------- exact H64.
----------------------------------------------- exact H.
----------------------------------------------- exact H1.
----------------------------------------------- exact H2.
----------------------------------------------- exact H23.
----------------------------------------------- exact H24.
----------------------------------------------- exact H5.
----------------------------------------------- exact H7.
----------------------------------------------- exact H10.
----------------------------------------------- exact H11.
----------------------------------------------- exact H12.
----------------------------------------------- exact H13.
----------------------------------------------- exact H14.
----------------------------------------------- exact H15.
----------------------------------------------- exact H16.
----------------------------------------------- exact H19.
----------------------------------------------- exact H26.
----------------------------------------------- exact H34.
----------------------------------------------- exact H35.
----------------------------------------------- exact H36.
----------------------------------------------- exact H37.
----------------------------------------------- exact H38.
----------------------------------------------- exact H42.
----------------------------------------------- exact H43.
----------------------------------------------- exact H44.
----------------------------------------------- exact H45.
----------------------------------------------- exact H46.
----------------------------------------------- exact H47.
----------------------------------------------- exact H48.
----------------------------------------------- exact H49.
----------------------------------------------- exact H50.
----------------------------------------------- exact H52.
----------------------------------------------- exact H54.
----------------------------------------------- exact H55.
----------------------------------------------- exact H58.
----------------------------------------------- exact H60.
----------------------------------------------- exact H61.
----------------------------------------------- exact H62.
----------------------------------------------- exact H63.
----------------------------------------------- exact H65.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E F A D) as H67.
----------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric E A D F H10).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F A D) as H68.
------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point E (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.BetS A0 D F) -> ((euclidean__axioms.Col A0 E F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__axioms.Col F A0 E) -> ((euclidean__axioms.Col F A0 D) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((euclidean__axioms.Col A0 E D) -> ((euclidean__axioms.BetS A0 M C) -> ((euclidean__axioms.BetS C M A0) -> ((euclidean__axioms.nCol A0 D B) -> ((euclidean__axioms.Col A0 D F) -> ((A0 = A0) -> ((euclidean__axioms.Col A0 D A0) -> ((euclidean__axioms.nCol A0 F B) -> ((euclidean__axioms.BetS A0 M Q) -> ((euclidean__axioms.Col A0 M Q) -> ((euclidean__axioms.Col A0 M C) -> ((euclidean__axioms.Col M A0 Q) -> ((euclidean__axioms.Col M A0 C) -> ((euclidean__axioms.neq A0 M) -> ((euclidean__axioms.neq M A0) -> ((euclidean__axioms.Col A0 Q C) -> ((A0 = A0) -> ((euclidean__axioms.Col F A0 A0) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((~(euclidean__defs.Meet F A0 C B)) -> ((~(euclidean__defs.Meet A0 D B C)) -> ((euclidean__axioms.Col A0 C Q) -> ((euclidean__axioms.BetS A0 Q C) -> ((euclidean__axioms.BetS C Q A0) -> ((euclidean__axioms.Cong A0 F A0 F) -> ((euclidean__axioms.Cong A0 F E F) -> ((euclidean__axioms.Cong E F A0 D) -> (euclidean__axioms.Cong A0 F A0 D))))))))))))))))))))))))))))))))))))))))))) with (x := A).
-------------------------------------------------intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
exact H108.

------------------------------------------------- exact H64.
------------------------------------------------- exact H.
------------------------------------------------- exact H1.
------------------------------------------------- exact H2.
------------------------------------------------- exact H23.
------------------------------------------------- exact H24.
------------------------------------------------- exact H5.
------------------------------------------------- exact H7.
------------------------------------------------- exact H10.
------------------------------------------------- exact H11.
------------------------------------------------- exact H12.
------------------------------------------------- exact H13.
------------------------------------------------- exact H14.
------------------------------------------------- exact H15.
------------------------------------------------- exact H16.
------------------------------------------------- exact H19.
------------------------------------------------- exact H26.
------------------------------------------------- exact H34.
------------------------------------------------- exact H35.
------------------------------------------------- exact H36.
------------------------------------------------- exact H37.
------------------------------------------------- exact H38.
------------------------------------------------- exact H42.
------------------------------------------------- exact H43.
------------------------------------------------- exact H44.
------------------------------------------------- exact H45.
------------------------------------------------- exact H46.
------------------------------------------------- exact H47.
------------------------------------------------- exact H48.
------------------------------------------------- exact H49.
------------------------------------------------- exact H50.
------------------------------------------------- exact H52.
------------------------------------------------- exact H54.
------------------------------------------------- exact H55.
------------------------------------------------- exact H58.
------------------------------------------------- exact H60.
------------------------------------------------- exact H61.
------------------------------------------------- exact H62.
------------------------------------------------- exact H63.
------------------------------------------------- exact H65.
------------------------------------------------- exact H66.
------------------------------------------------- exact H67.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A D A F) as H69.
------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.BetS A0 D F) -> ((euclidean__axioms.Col A0 E F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__axioms.Col F A0 E) -> ((euclidean__axioms.Col F A0 D) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((euclidean__axioms.Col A0 E D) -> ((euclidean__axioms.BetS A0 M C) -> ((euclidean__axioms.BetS C M A0) -> ((euclidean__axioms.nCol A0 D B) -> ((euclidean__axioms.Col A0 D F) -> ((A0 = A0) -> ((euclidean__axioms.Col A0 D A0) -> ((euclidean__axioms.nCol A0 F B) -> ((euclidean__axioms.BetS A0 M Q) -> ((euclidean__axioms.Col A0 M Q) -> ((euclidean__axioms.Col A0 M C) -> ((euclidean__axioms.Col M A0 Q) -> ((euclidean__axioms.Col M A0 C) -> ((euclidean__axioms.neq A0 M) -> ((euclidean__axioms.neq M A0) -> ((euclidean__axioms.Col A0 Q C) -> ((A0 = A0) -> ((euclidean__axioms.Col F A0 A0) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((~(euclidean__defs.Meet F A0 C B)) -> ((~(euclidean__defs.Meet A0 D B C)) -> ((euclidean__axioms.Col A0 C Q) -> ((euclidean__axioms.BetS A0 Q C) -> ((euclidean__axioms.BetS C Q A0) -> ((euclidean__axioms.Cong A0 F A0 F) -> ((euclidean__axioms.Cong A0 F E F) -> ((euclidean__axioms.Cong E F A0 D) -> ((euclidean__axioms.Cong A0 F A0 D) -> (euclidean__axioms.Cong A0 D A0 F)))))))))))))))))))))))))))))))))))))))))))) with (x := A).
--------------------------------------------------intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
exact H76.

-------------------------------------------------- exact H64.
-------------------------------------------------- exact H.
-------------------------------------------------- exact H1.
-------------------------------------------------- exact H2.
-------------------------------------------------- exact H23.
-------------------------------------------------- exact H24.
-------------------------------------------------- exact H5.
-------------------------------------------------- exact H7.
-------------------------------------------------- exact H10.
-------------------------------------------------- exact H11.
-------------------------------------------------- exact H12.
-------------------------------------------------- exact H13.
-------------------------------------------------- exact H14.
-------------------------------------------------- exact H15.
-------------------------------------------------- exact H16.
-------------------------------------------------- exact H19.
-------------------------------------------------- exact H26.
-------------------------------------------------- exact H34.
-------------------------------------------------- exact H35.
-------------------------------------------------- exact H36.
-------------------------------------------------- exact H37.
-------------------------------------------------- exact H38.
-------------------------------------------------- exact H42.
-------------------------------------------------- exact H43.
-------------------------------------------------- exact H44.
-------------------------------------------------- exact H45.
-------------------------------------------------- exact H46.
-------------------------------------------------- exact H47.
-------------------------------------------------- exact H48.
-------------------------------------------------- exact H49.
-------------------------------------------------- exact H50.
-------------------------------------------------- exact H52.
-------------------------------------------------- exact H54.
-------------------------------------------------- exact H55.
-------------------------------------------------- exact H58.
-------------------------------------------------- exact H60.
-------------------------------------------------- exact H61.
-------------------------------------------------- exact H62.
-------------------------------------------------- exact H63.
-------------------------------------------------- exact H65.
-------------------------------------------------- exact H66.
-------------------------------------------------- exact H67.
-------------------------------------------------- exact H68.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D A D) as H70.
-------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive A D).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt A D A F) as H71.
--------------------------------------------------- exists D.
split.
---------------------------------------------------- exact H1.
---------------------------------------------------- exact H70.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt A F A F) as H72.
---------------------------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 A D A F A F H71 H69).
---------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt A F A F)) as H73.
----------------------------------------------------- apply (@lemma__trichotomy2.lemma__trichotomy2 A F A F H72).
----------------------------------------------------- apply (@H73 H72).
-------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A F E)) as H65.
--------------------------------------------- intro H65.
assert (* Cut *) (euclidean__axioms.BetS E F A) as H66.
---------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A F E H65).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A D C) as H67.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)))) as H67.
------------------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC A B D C H5).
------------------------------------------------ destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H70.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D E) as H68.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))))) as H68.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A E D H16).
------------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H75.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A E C) as H69.
------------------------------------------------- apply (@euclidean__tactics.nCol__notCol A E C).
--------------------------------------------------apply (@euclidean__tactics.nCol__not__Col A E C).
---------------------------------------------------apply (@lemma__NChelper.lemma__NChelper A D C A E H67 H37 H68 H64).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C A E) as H70.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A C E) /\ (euclidean__axioms.nCol C E A))))) as H70.
--------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder A E C H69).
--------------------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H75.
-------------------------------------------------- assert (* Cut *) (exists r, (euclidean__axioms.BetS C r F) /\ (euclidean__axioms.BetS E r Q)) as H71.
--------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner C E A Q F H63 H66 H70).
--------------------------------------------------- destruct H71 as [r H72].
destruct H72 as [H73 H74].
assert (* Cut *) (euclidean__axioms.BetS Q r E) as H75.
---------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E r Q H74).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E B F) as H76.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B F) /\ ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol B F C) /\ (euclidean__axioms.nCol E B C)))) as H76.
------------------------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC E B F C H6).
------------------------------------------------------ destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H77.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F B E) as H77.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol B E F) /\ ((euclidean__axioms.nCol B F E) /\ ((euclidean__axioms.nCol F E B) /\ ((euclidean__axioms.nCol E F B) /\ (euclidean__axioms.nCol F B E))))) as H77.
------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder E B F H76).
------------------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H85.
------------------------------------------------------ assert (* Cut *) (exists H78, (euclidean__axioms.BetS E H78 B) /\ (euclidean__axioms.BetS F r H78)) as H78.
------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer E F Q r B H74 H59 H77).
------------------------------------------------------- destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
assert (* Cut *) (euclidean__axioms.Col E H79 B) as H83.
-------------------------------------------------------- right.
right.
right.
right.
left.
exact H81.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F r H79) as H84.
--------------------------------------------------------- right.
right.
right.
right.
left.
exact H82.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B H79) as H85.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H79 E B) /\ ((euclidean__axioms.Col H79 B E) /\ ((euclidean__axioms.Col B E H79) /\ ((euclidean__axioms.Col E B H79) /\ (euclidean__axioms.Col B H79 E))))) as H85.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E H79 B H83).
----------------------------------------------------------- destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
exact H92.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C r F) as H86.
----------------------------------------------------------- right.
right.
right.
right.
left.
exact H73.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col r F C) as H87.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col r C F) /\ ((euclidean__axioms.Col r F C) /\ ((euclidean__axioms.Col F C r) /\ ((euclidean__axioms.Col C F r) /\ (euclidean__axioms.Col F r C))))) as H87.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C r F H86).
------------------------------------------------------------- destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H90.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col r F H79) as H88.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col r F H79) /\ ((euclidean__axioms.Col r H79 F) /\ ((euclidean__axioms.Col H79 F r) /\ ((euclidean__axioms.Col F H79 r) /\ (euclidean__axioms.Col H79 r F))))) as H88.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F r H79 H84).
-------------------------------------------------------------- destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H89.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq r F) as H89.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq r F) /\ ((euclidean__axioms.neq C r) /\ (euclidean__axioms.neq C F))) as H89.
--------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C r F H73).
--------------------------------------------------------------- destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
exact H90.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F C H79) as H90.
--------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col F C H79).
----------------------------------------------------------------intro H90.
apply (@euclidean__tactics.Col__nCol__False F C H79 H90).
-----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 r F C H79 H87 H88 H89).


--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H91.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E F)))))) as H91.
----------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct F B E H77).
----------------------------------------------------------------- destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
exact H94.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H92.
----------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B E H91).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F C) as H93.
------------------------------------------------------------------ assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H93 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H93.
destruct __TmpHyp as [x H94].
destruct H94 as [x0 H95].
destruct H95 as [x1 H96].
destruct H96 as [x2 H97].
destruct H97 as [x3 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H119 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H119.
destruct __TmpHyp0 as [x4 H120].
destruct H120 as [x5 H121].
destruct H121 as [x6 H122].
destruct H122 as [x7 H123].
destruct H123 as [x8 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H145 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H145.
destruct __TmpHyp1 as [x9 H146].
destruct H146 as [x10 H147].
destruct H147 as [x11 H148].
destruct H148 as [x12 H149].
destruct H149 as [x13 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H171 by exact H21.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H171.
destruct __TmpHyp2 as [x14 H172].
destruct H172 as [x15 H173].
destruct H173 as [x16 H174].
destruct H174 as [x17 H175].
destruct H175 as [x18 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H197 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H197.
destruct __TmpHyp3 as [x19 H198].
destruct H198 as [x20 H199].
destruct H199 as [x21 H200].
destruct H200 as [x22 H201].
destruct H201 as [x23 H202].
destruct H202 as [H203 H204].
destruct H204 as [H205 H206].
destruct H206 as [H207 H208].
destruct H208 as [H209 H210].
destruct H210 as [H211 H212].
destruct H212 as [H213 H214].
destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
destruct H218 as [H219 H220].
destruct H220 as [H221 H222].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H223 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H223.
destruct __TmpHyp4 as [x24 H224].
destruct H224 as [x25 H225].
destruct H225 as [x26 H226].
destruct H226 as [x27 H227].
destruct H227 as [x28 H228].
destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
destruct H232 as [H233 H234].
destruct H234 as [H235 H236].
destruct H236 as [H237 H238].
destruct H238 as [H239 H240].
destruct H240 as [H241 H242].
destruct H242 as [H243 H244].
destruct H244 as [H245 H246].
destruct H246 as [H247 H248].
exact H101.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E B F C) as H94.
------------------------------------------------------------------- exists H79.
split.
-------------------------------------------------------------------- exact H92.
-------------------------------------------------------------------- split.
--------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------- split.
---------------------------------------------------------------------- exact H85.
---------------------------------------------------------------------- exact H90.
------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet E B F C)) as H95.
-------------------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H95 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H95.
destruct __TmpHyp as [x H96].
destruct H96 as [x0 H97].
destruct H97 as [x1 H98].
destruct H98 as [x2 H99].
destruct H99 as [x3 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H121 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H121.
destruct __TmpHyp0 as [x4 H122].
destruct H122 as [x5 H123].
destruct H123 as [x6 H124].
destruct H124 as [x7 H125].
destruct H125 as [x8 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H147 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H147.
destruct __TmpHyp1 as [x9 H148].
destruct H148 as [x10 H149].
destruct H149 as [x11 H150].
destruct H150 as [x12 H151].
destruct H151 as [x13 H152].
destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H173 by exact H21.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H173.
destruct __TmpHyp2 as [x14 H174].
destruct H174 as [x15 H175].
destruct H175 as [x16 H176].
destruct H176 as [x17 H177].
destruct H177 as [x18 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H199 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H199.
destruct __TmpHyp3 as [x19 H200].
destruct H200 as [x20 H201].
destruct H201 as [x21 H202].
destruct H202 as [x22 H203].
destruct H203 as [x23 H204].
destruct H204 as [H205 H206].
destruct H206 as [H207 H208].
destruct H208 as [H209 H210].
destruct H210 as [H211 H212].
destruct H212 as [H213 H214].
destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
destruct H218 as [H219 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H225 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H225.
destruct __TmpHyp4 as [x24 H226].
destruct H226 as [x25 H227].
destruct H227 as [x26 H228].
destruct H228 as [x27 H229].
destruct H229 as [x28 H230].
destruct H230 as [H231 H232].
destruct H232 as [H233 H234].
destruct H234 as [H235 H236].
destruct H236 as [H237 H238].
destruct H238 as [H239 H240].
destruct H240 as [H241 H242].
destruct H242 as [H243 H244].
destruct H244 as [H245 H246].
destruct H246 as [H247 H248].
destruct H248 as [H249 H250].
exact H117.
-------------------------------------------------------------------- apply (@H95 H94).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F E) as H66.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H66.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F A E H12).
----------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H67.
---------------------------------------------- assert ((A = F) \/ ((A = E) \/ ((F = E) \/ ((euclidean__axioms.BetS F A E) \/ ((euclidean__axioms.BetS A F E) \/ (euclidean__axioms.BetS A E F)))))) as H67 by exact H66.
assert (* Cut *) (euclidean__axioms.BetS A E F) as H68.
----------------------------------------------- assert ((A = F) \/ ((A = E) \/ ((F = E) \/ ((euclidean__axioms.BetS F A E) \/ ((euclidean__axioms.BetS A F E) \/ (euclidean__axioms.BetS A E F)))))) as H68 by exact H67.
assert ((A = F) \/ ((A = E) \/ ((F = E) \/ ((euclidean__axioms.BetS F A E) \/ ((euclidean__axioms.BetS A F E) \/ (euclidean__axioms.BetS A E F)))))) as __TmpHyp by exact H68.
destruct __TmpHyp as [H69|H69].
------------------------------------------------ assert (* Cut *) (~(~(euclidean__axioms.BetS A E F))) as H70.
------------------------------------------------- intro H70.
assert (* Cut *) (euclidean__axioms.BetS A D A) as H71.
-------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.BetS A0 D F) -> ((euclidean__axioms.Col A0 E F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__axioms.Col F A0 E) -> ((euclidean__axioms.Col F A0 D) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((euclidean__axioms.Col A0 E D) -> ((euclidean__axioms.BetS A0 M C) -> ((euclidean__axioms.BetS C M A0) -> ((euclidean__axioms.nCol A0 D B) -> ((euclidean__axioms.Col A0 D F) -> ((A0 = A0) -> ((euclidean__axioms.Col A0 D A0) -> ((euclidean__axioms.nCol A0 F B) -> ((euclidean__axioms.BetS A0 M Q) -> ((euclidean__axioms.Col A0 M Q) -> ((euclidean__axioms.Col A0 M C) -> ((euclidean__axioms.Col M A0 Q) -> ((euclidean__axioms.Col M A0 C) -> ((euclidean__axioms.neq A0 M) -> ((euclidean__axioms.neq M A0) -> ((euclidean__axioms.Col A0 Q C) -> ((A0 = A0) -> ((euclidean__axioms.Col F A0 A0) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.neq F A0) -> ((~(euclidean__defs.Meet F A0 C B)) -> ((~(euclidean__defs.Meet A0 D B C)) -> ((euclidean__axioms.Col A0 C Q) -> ((euclidean__axioms.BetS A0 Q C) -> ((euclidean__axioms.BetS C Q A0) -> ((~(A0 = E)) -> ((~(euclidean__axioms.BetS A0 F E)) -> ((euclidean__axioms.Col A0 F E) -> ((~(euclidean__axioms.BetS A0 E F)) -> (euclidean__axioms.BetS A0 D A0)))))))))))))))))))))))))))))))))))))))))))) with (x := A).
---------------------------------------------------intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
exact H72.

--------------------------------------------------- exact H69.
--------------------------------------------------- exact H.
--------------------------------------------------- exact H1.
--------------------------------------------------- exact H2.
--------------------------------------------------- exact H23.
--------------------------------------------------- exact H24.
--------------------------------------------------- exact H5.
--------------------------------------------------- exact H7.
--------------------------------------------------- exact H10.
--------------------------------------------------- exact H11.
--------------------------------------------------- exact H12.
--------------------------------------------------- exact H13.
--------------------------------------------------- exact H14.
--------------------------------------------------- exact H15.
--------------------------------------------------- exact H16.
--------------------------------------------------- exact H19.
--------------------------------------------------- exact H26.
--------------------------------------------------- exact H34.
--------------------------------------------------- exact H35.
--------------------------------------------------- exact H36.
--------------------------------------------------- exact H37.
--------------------------------------------------- exact H38.
--------------------------------------------------- exact H42.
--------------------------------------------------- exact H43.
--------------------------------------------------- exact H44.
--------------------------------------------------- exact H45.
--------------------------------------------------- exact H46.
--------------------------------------------------- exact H47.
--------------------------------------------------- exact H48.
--------------------------------------------------- exact H49.
--------------------------------------------------- exact H50.
--------------------------------------------------- exact H52.
--------------------------------------------------- exact H54.
--------------------------------------------------- exact H55.
--------------------------------------------------- exact H58.
--------------------------------------------------- exact H60.
--------------------------------------------------- exact H61.
--------------------------------------------------- exact H62.
--------------------------------------------------- exact H63.
--------------------------------------------------- exact H64.
--------------------------------------------------- exact H65.
--------------------------------------------------- exact H66.
--------------------------------------------------- exact H70.
-------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A D A)) as H72.
--------------------------------------------------- apply (@euclidean__axioms.axiom__betweennessidentity A D).
--------------------------------------------------- apply (@H14 H69).
------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E F)).
--------------------------------------------------intro H71.
destruct H34 as [H72 H73].
destruct H38 as [H74 H75].
destruct H73 as [H76 H77].
destruct H75 as [H78 H79].
destruct H77 as [H80 H81].
destruct H79 as [H82 H83].
destruct H81 as [H84 H85].
destruct H83 as [H86 H87].
destruct H85 as [H88 H89].
destruct H87 as [H90 H91].
assert (* Cut *) (False) as H92.
--------------------------------------------------- apply (@H14 H69).
--------------------------------------------------- assert (* Cut *) (False) as H93.
---------------------------------------------------- apply (@H54 H69).
---------------------------------------------------- assert (* Cut *) (False) as H94.
----------------------------------------------------- apply (@H70 H71).
----------------------------------------------------- contradiction H94.

------------------------------------------------ destruct H69 as [H70|H70].
------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E F))) as H71.
-------------------------------------------------- intro H71.
apply (@H64 H70).
-------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E F)).
---------------------------------------------------intro H72.
destruct H34 as [H73 H74].
destruct H38 as [H75 H76].
destruct H74 as [H77 H78].
destruct H76 as [H79 H80].
destruct H78 as [H81 H82].
destruct H80 as [H83 H84].
destruct H82 as [H85 H86].
destruct H84 as [H87 H88].
destruct H86 as [H89 H90].
destruct H88 as [H91 H92].
assert (* Cut *) (False) as H93.
---------------------------------------------------- apply (@H64 H70).
---------------------------------------------------- assert (* Cut *) (False) as H94.
----------------------------------------------------- apply (@H71 H72).
----------------------------------------------------- contradiction H94.

------------------------------------------------- destruct H70 as [H71|H71].
-------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E F))) as H72.
--------------------------------------------------- intro H72.
assert (* Cut *) (E = F) as H73.
---------------------------------------------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric E F H71).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E F) as H74.
----------------------------------------------------- right.
right.
left.
exact H73.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B F) as H75.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col E B F) /\ ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))))) as H75.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B E F H74).
------------------------------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H76.
------------------------------------------------------ assert (* Cut *) (F = F) as H76.
------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point F (fun E0 => (euclidean__defs.PG E0 B C F) -> ((euclidean__axioms.Col A E0 F) -> ((euclidean__defs.Par E0 B C F) -> ((euclidean__defs.Par E0 F B C) -> ((euclidean__defs.Par E0 B F C) -> ((euclidean__axioms.Cong E0 F B C) -> ((euclidean__axioms.Cong B C E0 F) -> ((euclidean__axioms.Cong A D E0 F) -> ((euclidean__axioms.Col F A E0) -> ((euclidean__axioms.Col A E0 D) -> ((euclidean__axioms.BetS E0 m C) -> ((~(A = E0)) -> ((~(euclidean__axioms.BetS A F E0)) -> ((euclidean__axioms.Col A F E0) -> ((~(euclidean__axioms.BetS A E0 F)) -> ((E0 = F) -> ((euclidean__axioms.Col B E0 F) -> ((euclidean__axioms.Col E0 B F) -> (F = F)))))))))))))))))))) with (y := E).
--------------------------------------------------------intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
assert (F = F) as H94 by exact H91.
exact H94.

-------------------------------------------------------- exact H71.
-------------------------------------------------------- exact H0.
-------------------------------------------------------- exact H2.
-------------------------------------------------------- exact H21.
-------------------------------------------------------- exact H22.
-------------------------------------------------------- exact H6.
-------------------------------------------------------- exact H8.
-------------------------------------------------------- exact H9.
-------------------------------------------------------- exact H10.
-------------------------------------------------------- exact H12.
-------------------------------------------------------- exact H16.
-------------------------------------------------------- exact H30.
-------------------------------------------------------- exact H64.
-------------------------------------------------------- exact H65.
-------------------------------------------------------- exact H66.
-------------------------------------------------------- exact H72.
-------------------------------------------------------- exact H73.
-------------------------------------------------------- exact H74.
-------------------------------------------------------- exact H75.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F C F) as H77.
-------------------------------------------------------- right.
left.
exact H76.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H78.
--------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H78 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H78.
destruct __TmpHyp0 as [x H79].
destruct H79 as [x0 H80].
destruct H80 as [x1 H81].
destruct H81 as [x2 H82].
destruct H82 as [x3 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H104 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H104.
destruct __TmpHyp1 as [x4 H105].
destruct H105 as [x5 H106].
destruct H106 as [x6 H107].
destruct H107 as [x7 H108].
destruct H108 as [x8 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H130 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H130.
destruct __TmpHyp2 as [x9 H131].
destruct H131 as [x10 H132].
destruct H132 as [x11 H133].
destruct H133 as [x12 H134].
destruct H134 as [x13 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H156 by exact H21.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H156.
destruct __TmpHyp3 as [x14 H157].
destruct H157 as [x15 H158].
destruct H158 as [x16 H159].
destruct H159 as [x17 H160].
destruct H160 as [x18 H161].
destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H182 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H182.
destruct __TmpHyp4 as [x19 H183].
destruct H183 as [x20 H184].
destruct H184 as [x21 H185].
destruct H185 as [x22 H186].
destruct H186 as [x23 H187].
destruct H187 as [H188 H189].
destruct H189 as [H190 H191].
destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
destruct H199 as [H200 H201].
destruct H201 as [H202 H203].
destruct H203 as [H204 H205].
destruct H205 as [H206 H207].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H208 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H208.
destruct __TmpHyp5 as [x24 H209].
destruct H209 as [x25 H210].
destruct H210 as [x26 H211].
destruct H211 as [x27 H212].
destruct H212 as [x28 H213].
destruct H213 as [H214 H215].
destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
destruct H219 as [H220 H221].
destruct H221 as [H222 H223].
destruct H223 as [H224 H225].
destruct H225 as [H226 H227].
destruct H227 as [H228 H229].
destruct H229 as [H230 H231].
destruct H231 as [H232 H233].
exact H162.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F C) as H79.
---------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H79 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H79.
destruct __TmpHyp0 as [x H80].
destruct H80 as [x0 H81].
destruct H81 as [x1 H82].
destruct H82 as [x2 H83].
destruct H83 as [x3 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H105 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H105.
destruct __TmpHyp1 as [x4 H106].
destruct H106 as [x5 H107].
destruct H107 as [x6 H108].
destruct H108 as [x7 H109].
destruct H109 as [x8 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H131 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H131.
destruct __TmpHyp2 as [x9 H132].
destruct H132 as [x10 H133].
destruct H133 as [x11 H134].
destruct H134 as [x12 H135].
destruct H135 as [x13 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H157 by exact H21.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H157.
destruct __TmpHyp3 as [x14 H158].
destruct H158 as [x15 H159].
destruct H159 as [x16 H160].
destruct H160 as [x17 H161].
destruct H161 as [x18 H162].
destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H183 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H183.
destruct __TmpHyp4 as [x19 H184].
destruct H184 as [x20 H185].
destruct H185 as [x21 H186].
destruct H186 as [x22 H187].
destruct H187 as [x23 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
destruct H198 as [H199 H200].
destruct H200 as [H201 H202].
destruct H202 as [H203 H204].
destruct H204 as [H205 H206].
destruct H206 as [H207 H208].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H209 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H209.
destruct __TmpHyp5 as [x24 H210].
destruct H210 as [x25 H211].
destruct H211 as [x26 H212].
destruct H212 as [x27 H213].
destruct H213 as [x28 H214].
destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
destruct H218 as [H219 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
destruct H232 as [H233 H234].
exact H87.
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E B F C) as H80.
----------------------------------------------------------- exists F.
split.
------------------------------------------------------------ exact H78.
------------------------------------------------------------ split.
------------------------------------------------------------- exact H79.
------------------------------------------------------------- split.
-------------------------------------------------------------- exact H75.
-------------------------------------------------------------- exact H77.
----------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet E B F C)) as H81.
------------------------------------------------------------ assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H81 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H81.
destruct __TmpHyp0 as [x H82].
destruct H82 as [x0 H83].
destruct H83 as [x1 H84].
destruct H84 as [x2 H85].
destruct H85 as [x3 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H107 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H107.
destruct __TmpHyp1 as [x4 H108].
destruct H108 as [x5 H109].
destruct H109 as [x6 H110].
destruct H110 as [x7 H111].
destruct H111 as [x8 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H133 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H133.
destruct __TmpHyp2 as [x9 H134].
destruct H134 as [x10 H135].
destruct H135 as [x11 H136].
destruct H136 as [x12 H137].
destruct H137 as [x13 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H159 by exact H21.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H159.
destruct __TmpHyp3 as [x14 H160].
destruct H160 as [x15 H161].
destruct H161 as [x16 H162].
destruct H162 as [x17 H163].
destruct H163 as [x18 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H185 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H185.
destruct __TmpHyp4 as [x19 H186].
destruct H186 as [x20 H187].
destruct H187 as [x21 H188].
destruct H188 as [x22 H189].
destruct H189 as [x23 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
destruct H198 as [H199 H200].
destruct H200 as [H201 H202].
destruct H202 as [H203 H204].
destruct H204 as [H205 H206].
destruct H206 as [H207 H208].
destruct H208 as [H209 H210].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H211 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H211.
destruct __TmpHyp5 as [x24 H212].
destruct H212 as [x25 H213].
destruct H213 as [x26 H214].
destruct H214 as [x27 H215].
destruct H215 as [x28 H216].
destruct H216 as [H217 H218].
destruct H218 as [H219 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
destruct H232 as [H233 H234].
destruct H234 as [H235 H236].
exact H103.
------------------------------------------------------------ apply (@H81 H80).
--------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E F)).
----------------------------------------------------intro H73.
destruct H34 as [H74 H75].
destruct H38 as [H76 H77].
destruct H75 as [H78 H79].
destruct H77 as [H80 H81].
destruct H79 as [H82 H83].
destruct H81 as [H84 H85].
destruct H83 as [H86 H87].
destruct H85 as [H88 H89].
destruct H87 as [H90 H91].
destruct H89 as [H92 H93].
assert (* Cut *) (False) as H94.
----------------------------------------------------- apply (@H72 H73).
----------------------------------------------------- contradiction H94.

-------------------------------------------------- destruct H71 as [H72|H72].
--------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E F))) as H73.
---------------------------------------------------- intro H73.
assert (* Cut *) (euclidean__axioms.BetS F D A) as H74.
----------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A D F H1).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D A E) as H75.
------------------------------------------------------ apply (@lemma__3__6a.lemma__3__6a F D A E H74 H72).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong D A D A) as H76.
------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive D A).
------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt D A D E) as H77.
-------------------------------------------------------- exists A.
split.
--------------------------------------------------------- exact H75.
--------------------------------------------------------- exact H76.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D A A D) as H78.
--------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse D A).
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt A D D E) as H79.
---------------------------------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 D A D E A D H77 H78).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D E E D) as H80.
----------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse D E).
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt A D E D) as H81.
------------------------------------------------------------ apply (@lemma__lessthancongruence.lemma__lessthancongruence A D D E E D H79 H80).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A D A D) as H82.
------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive A D).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt A D A F) as H83.
-------------------------------------------------------------- exists D.
split.
--------------------------------------------------------------- exact H1.
--------------------------------------------------------------- exact H82.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D D A) as H84.
--------------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse A D).
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt D A A F) as H85.
---------------------------------------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 A D A F D A H83 H84).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F F A) as H86.
----------------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse A F).
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt D A F A) as H87.
------------------------------------------------------------------ apply (@lemma__lessthancongruence.lemma__lessthancongruence D A A F F A H85 H86).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong F A F A) as H88.
------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive F A).
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt F A F E) as H89.
-------------------------------------------------------------------- exists A.
split.
--------------------------------------------------------------------- exact H72.
--------------------------------------------------------------------- exact H88.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt D A F E) as H90.
--------------------------------------------------------------------- apply (@lemma__lessthantransitive.lemma__lessthantransitive D A F A F E H87 H89).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D A F E) as H91.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong D A F E) /\ ((euclidean__axioms.Cong D A E F) /\ (euclidean__axioms.Cong A D F E))) as H91.
----------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A D E F H10).
----------------------------------------------------------------------- destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H92.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt F E F E) as H92.
----------------------------------------------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 D A F E F E H90 H91).
----------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt F E F E)) as H93.
------------------------------------------------------------------------ apply (@lemma__trichotomy2.lemma__trichotomy2 F E F E H92).
------------------------------------------------------------------------ apply (@H93 H92).
---------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E F)).
-----------------------------------------------------intro H74.
destruct H34 as [H75 H76].
destruct H38 as [H77 H78].
destruct H76 as [H79 H80].
destruct H78 as [H81 H82].
destruct H80 as [H83 H84].
destruct H82 as [H85 H86].
destruct H84 as [H87 H88].
destruct H86 as [H89 H90].
destruct H88 as [H91 H92].
destruct H90 as [H93 H94].
assert (* Cut *) (False) as H95.
------------------------------------------------------ apply (@H73 H74).
------------------------------------------------------ contradiction H95.

--------------------------------------------------- destruct H72 as [H73|H73].
---------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E F))) as H74.
----------------------------------------------------- intro H74.
apply (@H65 H73).
----------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E F)).
------------------------------------------------------intro H75.
destruct H34 as [H76 H77].
destruct H38 as [H78 H79].
destruct H77 as [H80 H81].
destruct H79 as [H82 H83].
destruct H81 as [H84 H85].
destruct H83 as [H86 H87].
destruct H85 as [H88 H89].
destruct H87 as [H90 H91].
destruct H89 as [H92 H93].
destruct H91 as [H94 H95].
assert (* Cut *) (False) as H96.
------------------------------------------------------- apply (@H65 H73).
------------------------------------------------------- assert (* Cut *) (False) as H97.
-------------------------------------------------------- apply (@H74 H75).
-------------------------------------------------------- contradiction H97.

---------------------------------------------------- exact H73.
----------------------------------------------- exact H68.
Qed.
