Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__3__7b.
Require Export lemma__EFreflexive.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__diagonalsmeet.
Require Export lemma__inequalitysymmetric.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export lemma__lessthantransitive.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelPasch.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__trichotomy2.
Require Export logic.
Require Export proposition__34.
Require Export proposition__35A.
Definition proposition__35 : forall A B C D E F, (euclidean__defs.PG A B C D) -> ((euclidean__defs.PG E B C F) -> ((euclidean__axioms.Col A D E) -> ((euclidean__axioms.Col A D F) -> (euclidean__axioms.EF A B C D E B C F)))).
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
---- assert (* Cut *) (euclidean__defs.Par F C E B) as H7.
----- destruct H4 as [H7 H8].
destruct H3 as [H9 H10].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric E B F C H6).
----- assert (* Cut *) (euclidean__axioms.Cong A D B C) as H8.
------ destruct H4 as [H8 H9].
destruct H3 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H12.
------- apply (@proposition__34.proposition__34 A D B C H).
------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H13.
------ assert (* Cut *) (euclidean__axioms.Cong E F B C) as H9.
------- destruct H4 as [H9 H10].
destruct H3 as [H11 H12].
assert (* Cut *) ((euclidean__axioms.Cong E F B C) /\ ((euclidean__axioms.Cong E B F C) /\ ((euclidean__defs.CongA B E F F C B) /\ ((euclidean__defs.CongA E F C C B E) /\ (euclidean__axioms.Cong__3 B E F F C B))))) as H13.
-------- apply (@proposition__34.proposition__34 E F B C H0).
-------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H14.
------- assert (* Cut *) (euclidean__axioms.Cong B C E F) as H10.
-------- destruct H4 as [H10 H11].
destruct H3 as [H12 H13].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B E F C H9).
-------- assert (* Cut *) (euclidean__axioms.Cong A D E F) as H11.
--------- destruct H4 as [H11 H12].
destruct H3 as [H13 H14].
apply (@lemma__congruencetransitive.lemma__congruencetransitive A D B C E F H8 H10).
--------- assert (* Cut *) (euclidean__axioms.neq A D) as H12.
---------- assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H12 by exact H7.
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H12.
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
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H38 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H38.
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
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H64 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H64.
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
assert ((exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) /\ (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H90 by exact H4.
assert ((exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) /\ (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as __TmpHyp2 by exact H90.
destruct __TmpHyp2 as [H91 H92].
destruct H91 as [x14 H93].
destruct H93 as [x15 H94].
destruct H94 as [x16 H95].
destruct H95 as [x17 H96].
destruct H96 as [x18 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H92 as [x19 H118].
destruct H118 as [x20 H119].
destruct H119 as [x21 H120].
destruct H120 as [x22 H121].
destruct H121 as [x23 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
assert ((exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) /\ (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H143 by exact H3.
assert ((exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) /\ (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as __TmpHyp3 by exact H143.
destruct __TmpHyp3 as [H144 H145].
destruct H144 as [x24 H146].
destruct H146 as [x25 H147].
destruct H147 as [x26 H148].
destruct H148 as [x27 H149].
destruct H149 as [x28 H150].
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
destruct H145 as [x29 H171].
destruct H171 as [x30 H172].
destruct H172 as [x31 H173].
destruct H173 as [x32 H174].
destruct H174 as [x33 H175].
destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
destruct H183 as [H184 H185].
destruct H185 as [H186 H187].
destruct H187 as [H188 H189].
destruct H189 as [H190 H191].
destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
exact H176.
---------- assert (* Cut *) (euclidean__axioms.neq E F) as H13.
----------- assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H13 by exact H7.
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H13.
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
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H39 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H39.
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
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H65 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H65.
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
assert ((exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) /\ (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H91 by exact H4.
assert ((exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) /\ (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as __TmpHyp2 by exact H91.
destruct __TmpHyp2 as [H92 H93].
destruct H92 as [x14 H94].
destruct H94 as [x15 H95].
destruct H95 as [x16 H96].
destruct H96 as [x17 H97].
destruct H97 as [x18 H98].
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
destruct H93 as [x19 H119].
destruct H119 as [x20 H120].
destruct H120 as [x21 H121].
destruct H121 as [x22 H122].
destruct H122 as [x23 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
assert ((exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) /\ (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as H144 by exact H3.
assert ((exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) /\ (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V)))))))))))) as __TmpHyp3 by exact H144.
destruct __TmpHyp3 as [H145 H146].
destruct H145 as [x24 H147].
destruct H147 as [x25 H148].
destruct H148 as [x26 H149].
destruct H149 as [x27 H150].
destruct H150 as [x28 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H146 as [x29 H172].
destruct H172 as [x30 H173].
destruct H173 as [x31 H174].
destruct H174 as [x32 H175].
destruct H175 as [x33 H176].
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
exact H124.
----------- assert (* Cut *) (euclidean__axioms.neq D A) as H14.
------------ destruct H4 as [H14 H15].
destruct H3 as [H16 H17].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A D H12).
------------ assert (* Cut *) (~(~(euclidean__axioms.EF A B C D E B C F))) as H15.
------------- intro H15.
assert (* Cut *) (~(euclidean__axioms.BetS A D F)) as H16.
-------------- intro H16.
assert (euclidean__axioms.Col A D F) as H17 by exact H2.
assert (* Cut *) (euclidean__axioms.Col D A F) as H18.
--------------- destruct H4 as [H18 H19].
destruct H3 as [H20 H21].
assert (* Cut *) ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col D F A) /\ ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col A F D) /\ (euclidean__axioms.Col F D A))))) as H22.
---------------- apply (@lemma__collinearorder.lemma__collinearorder A D F H17).
---------------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H23.
--------------- assert (* Cut *) (euclidean__axioms.Col D A E) as H19.
---------------- destruct H4 as [H19 H20].
destruct H3 as [H21 H22].
assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H23.
----------------- apply (@lemma__collinearorder.lemma__collinearorder A D E H1).
----------------- destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H24.
---------------- assert (* Cut *) (euclidean__axioms.Col A F E) as H20.
----------------- destruct H4 as [H20 H21].
destruct H3 as [H22 H23].
apply (@euclidean__tactics.not__nCol__Col A F E).
------------------intro H24.
apply (@euclidean__tactics.Col__nCol__False A F E H24).
-------------------apply (@lemma__collinear4.lemma__collinear4 D A F E H18 H19 H14).


----------------- assert (* Cut *) (euclidean__axioms.Col A E F) as H21.
------------------ destruct H4 as [H21 H22].
destruct H3 as [H23 H24].
assert (* Cut *) ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A))))) as H25.
------------------- apply (@lemma__collinearorder.lemma__collinearorder A F E H20).
------------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H32.
------------------ assert (* Cut *) (euclidean__axioms.EF A B C D E B C F) as H22.
------------------- destruct H4 as [H22 H23].
destruct H3 as [H24 H25].
apply (@proposition__35A.proposition__35A A B C D E F H H0 H16 H21).
------------------- apply (@H15 H22).
-------------- assert (* Cut *) (~(euclidean__axioms.BetS A D E)) as H17.
--------------- intro H17.
assert (* Cut *) (exists H18, (euclidean__axioms.BetS B H18 E) /\ (euclidean__axioms.BetS C H18 D)) as H18.
---------------- destruct H4 as [H18 H19].
destruct H3 as [H20 H21].
apply (@lemma__parallelPasch.lemma__parallelPasch A B C D E H H17).
---------------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H4 as [H23 H24].
destruct H3 as [H25 H26].
assert (* Cut *) (euclidean__axioms.BetS D H19 C) as H27.
----------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C H19 D H22).
----------------- assert (* Cut *) (euclidean__axioms.Col B H19 E) as H28.
------------------ right.
right.
right.
right.
left.
exact H21.
------------------ assert (* Cut *) (euclidean__axioms.Col B E H19) as H29.
------------------- assert (* Cut *) ((euclidean__axioms.Col H19 B E) /\ ((euclidean__axioms.Col H19 E B) /\ ((euclidean__axioms.Col E B H19) /\ ((euclidean__axioms.Col B E H19) /\ (euclidean__axioms.Col E H19 B))))) as H29.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder B H19 E H28).
-------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H36.
------------------- assert (* Cut *) (euclidean__axioms.nCol A D B) as H30.
-------------------- assert (* Cut *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H30.
--------------------- apply (@lemma__parallelNC.lemma__parallelNC A D B C H26).
--------------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H31.
-------------------- assert (euclidean__axioms.Col A D E) as H31 by exact H1.
assert (* Cut *) (D = D) as H32.
--------------------- apply (@logic.eq__refl Point D).
--------------------- assert (* Cut *) (euclidean__axioms.Col A D D) as H33.
---------------------- right.
right.
left.
exact H32.
---------------------- assert (* Cut *) (euclidean__axioms.neq D E) as H34.
----------------------- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H34.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A D E H17).
------------------------ destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H35.
----------------------- assert (* Cut *) (euclidean__axioms.nCol D E B) as H35.
------------------------ apply (@euclidean__tactics.nCol__notCol D E B).
-------------------------apply (@euclidean__tactics.nCol__not__Col D E B).
--------------------------apply (@lemma__NChelper.lemma__NChelper A D B D E H30 H33 H31 H34).


------------------------ assert (* Cut *) (euclidean__axioms.nCol B E D) as H36.
------------------------- assert (* Cut *) ((euclidean__axioms.nCol E D B) /\ ((euclidean__axioms.nCol E B D) /\ ((euclidean__axioms.nCol B D E) /\ ((euclidean__axioms.nCol D B E) /\ (euclidean__axioms.nCol B E D))))) as H36.
-------------------------- apply (@lemma__NCorder.lemma__NCorder D E B H35).
-------------------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
exact H44.
------------------------- assert (* Cut *) (euclidean__axioms.TS D B E C) as H37.
-------------------------- exists H19.
split.
--------------------------- exact H27.
--------------------------- split.
---------------------------- exact H29.
---------------------------- exact H36.
-------------------------- assert (* Cut *) (euclidean__axioms.TS C B E D) as H38.
--------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric B E D C H37).
--------------------------- assert (* Cut *) (euclidean__defs.Par F C B E) as H39.
---------------------------- assert (* Cut *) ((euclidean__defs.Par C F E B) /\ ((euclidean__defs.Par F C B E) /\ (euclidean__defs.Par C F B E))) as H39.
----------------------------- apply (@lemma__parallelflip.lemma__parallelflip F C E B H7).
----------------------------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H42.
---------------------------- assert (* Cut *) (euclidean__defs.Par B E F C) as H40.
----------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric F C B E H39).
----------------------------- assert (* Cut *) (euclidean__defs.TP B E F C) as H41.
------------------------------ apply (@lemma__paralleldef2B.lemma__paralleldef2B B E F C H40).
------------------------------ assert (* Cut *) (euclidean__defs.OS F C B E) as H42.
------------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H47.
------------------------------- assert (* Cut *) (euclidean__axioms.TS F B E D) as H43.
-------------------------------- apply (@lemma__planeseparation.lemma__planeseparation B E F C D H42 H38).
-------------------------------- assert (exists e, (euclidean__axioms.BetS F e D) /\ ((euclidean__axioms.Col B E e) /\ (euclidean__axioms.nCol B E F))) as H44 by exact H43.
destruct H44 as [e H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
assert (* Cut *) (euclidean__axioms.neq F D) as H50.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq e D) /\ ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F D))) as H50.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal F e D H46).
---------------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H54.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col F e D) as H51.
---------------------------------- right.
right.
right.
right.
left.
exact H46.
---------------------------------- assert (* Cut *) (~(euclidean__axioms.neq e E)) as H52.
----------------------------------- intro H52.
assert (* Cut *) (euclidean__axioms.neq A D) as H53.
------------------------------------ assert (* Cut *) ((euclidean__axioms.neq e D) /\ ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F D))) as H53.
------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal F e D H46).
------------------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H12.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col D E F) as H54.
------------------------------------- apply (@euclidean__tactics.not__nCol__Col D E F).
--------------------------------------intro H54.
apply (@euclidean__tactics.Col__nCol__False D E F H54).
---------------------------------------apply (@lemma__collinear4.lemma__collinear4 A D E F H31 H2 H53).


------------------------------------- assert (* Cut *) (euclidean__axioms.Col F D E) as H55.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D))))) as H55.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D E F H54).
--------------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H60.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col F D e) as H56.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col e F D) /\ ((euclidean__axioms.Col e D F) /\ ((euclidean__axioms.Col D F e) /\ ((euclidean__axioms.Col F D e) /\ (euclidean__axioms.Col D e F))))) as H56.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F e D H51).
---------------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H63.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col D E e) as H57.
---------------------------------------- apply (@euclidean__tactics.not__nCol__Col D E e).
-----------------------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False D E e H57).
------------------------------------------apply (@lemma__collinear4.lemma__collinear4 F D E e H55 H56 H50).


---------------------------------------- assert (* Cut *) (euclidean__axioms.Col e E D) as H58.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E D e) /\ ((euclidean__axioms.Col E e D) /\ ((euclidean__axioms.Col e D E) /\ ((euclidean__axioms.Col D e E) /\ (euclidean__axioms.Col e E D))))) as H58.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder D E e H57).
------------------------------------------ destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H66.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col e E B) as H59.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col E B e) /\ ((euclidean__axioms.Col E e B) /\ ((euclidean__axioms.Col e B E) /\ ((euclidean__axioms.Col B e E) /\ (euclidean__axioms.Col e E B))))) as H59.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B E e H48).
------------------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H67.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E D B) as H60.
------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E D B).
--------------------------------------------intro H60.
apply (@euclidean__tactics.Col__nCol__False E D B H60).
---------------------------------------------apply (@lemma__collinear4.lemma__collinear4 e E D B H58 H59 H52).


------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E D) as H61.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D E B) /\ ((euclidean__axioms.Col D B E) /\ ((euclidean__axioms.Col B E D) /\ ((euclidean__axioms.Col E B D) /\ (euclidean__axioms.Col B D E))))) as H61.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E D B H60).
--------------------------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H66.
-------------------------------------------- apply (@euclidean__tactics.Col__nCol__False B E F H49).
---------------------------------------------apply (@euclidean__tactics.not__nCol__Col B E F).
----------------------------------------------intro H62.
apply (@euclidean__tactics.Col__nCol__False B E D H36 H61).


----------------------------------- assert (* Cut *) (euclidean__axioms.BetS F E D) as H53.
------------------------------------ apply (@eq__ind euclidean__axioms.Point e (fun X => euclidean__axioms.BetS F X D)) with (y := E).
------------------------------------- exact H46.
-------------------------------------apply (@euclidean__tactics.NNPP (e = E) H52).

------------------------------------ assert (* Cut *) (euclidean__axioms.BetS D E F) as H54.
------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry F E D H53).
------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A D F) as H55.
-------------------------------------- apply (@lemma__3__7b.lemma__3__7b A D E F H17 H54).
-------------------------------------- apply (@H16 H55).
--------------- assert (* Cut *) (euclidean__defs.Par B A D C) as H18.
---------------- destruct H4 as [H18 H19].
destruct H3 as [H20 H21].
assert (* Cut *) ((euclidean__defs.Par B A D C) /\ ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par B A C D))) as H22.
----------------- apply (@lemma__parallelflip.lemma__parallelflip A B D C H5).
----------------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H23.
---------------- assert (* Cut *) (euclidean__defs.Par D C B A) as H19.
----------------- destruct H4 as [H19 H20].
destruct H3 as [H21 H22].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric B A D C H18).
----------------- assert (* Cut *) (euclidean__defs.Par D A C B) as H20.
------------------ destruct H4 as [H20 H21].
destruct H3 as [H22 H23].
assert (* Cut *) ((euclidean__defs.Par D A B C) /\ ((euclidean__defs.Par A D C B) /\ (euclidean__defs.Par D A C B))) as H24.
------------------- apply (@lemma__parallelflip.lemma__parallelflip A D B C H23).
------------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H28.
------------------ assert (* Cut *) (euclidean__defs.PG D C B A) as H21.
------------------- split.
-------------------- exact H19.
-------------------- exact H20.
------------------- assert (* Cut *) (euclidean__defs.Par B E F C) as H22.
-------------------- destruct H4 as [H22 H23].
destruct H3 as [H24 H25].
assert (* Cut *) ((euclidean__defs.Par B E F C) /\ ((euclidean__defs.Par E B C F) /\ (euclidean__defs.Par B E C F))) as H26.
--------------------- apply (@lemma__parallelflip.lemma__parallelflip E B F C H6).
--------------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H27.
-------------------- assert (* Cut *) (euclidean__defs.Par F C B E) as H23.
--------------------- destruct H4 as [H23 H24].
destruct H3 as [H25 H26].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric B E F C H22).
--------------------- assert (* Cut *) (euclidean__defs.Par F E C B) as H24.
---------------------- destruct H4 as [H24 H25].
destruct H3 as [H26 H27].
assert (* Cut *) ((euclidean__defs.Par F E B C) /\ ((euclidean__defs.Par E F C B) /\ (euclidean__defs.Par F E C B))) as H28.
----------------------- apply (@lemma__parallelflip.lemma__parallelflip E F B C H25).
----------------------- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H32.
---------------------- assert (* Cut *) (euclidean__defs.PG F C B E) as H25.
----------------------- split.
------------------------ exact H23.
------------------------ exact H24.
----------------------- assert (* Cut *) (~(euclidean__axioms.BetS E A D)) as H26.
------------------------ intro H26.
assert (* Cut *) (euclidean__axioms.BetS D A E) as H27.
------------------------- destruct H4 as [H27 H28].
destruct H3 as [H29 H30].
apply (@euclidean__axioms.axiom__betweennesssymmetry E A D H26).
------------------------- assert (* Cut *) (euclidean__axioms.Col D A E) as H28.
-------------------------- right.
right.
right.
right.
left.
exact H27.
-------------------------- assert (* Cut *) (euclidean__axioms.Col A D E) as H29.
--------------------------- destruct H4 as [H29 H30].
destruct H3 as [H31 H32].
assert (* Cut *) ((euclidean__axioms.Col A D E) /\ ((euclidean__axioms.Col A E D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D E A) /\ (euclidean__axioms.Col E A D))))) as H33.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder D A E H28).
---------------------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H34.
--------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H30.
---------------------------- destruct H4 as [H30 H31].
destruct H3 as [H32 H33].
assert (* Cut *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq D A) /\ (euclidean__axioms.neq D E))) as H34.
----------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D A E H27).
----------------------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H12.
---------------------------- assert (* Cut *) (euclidean__axioms.Col D E F) as H31.
----------------------------- destruct H4 as [H31 H32].
destruct H3 as [H33 H34].
apply (@euclidean__tactics.not__nCol__Col D E F).
------------------------------intro H35.
apply (@euclidean__tactics.Col__nCol__False D E F H35).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 A D E F H29 H2 H30).


----------------------------- assert (* Cut *) (euclidean__axioms.Col D F E) as H32.
------------------------------ destruct H4 as [H32 H33].
destruct H3 as [H34 H35].
assert (* Cut *) ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D))))) as H36.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D E F H31).
------------------------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
exact H43.
------------------------------ assert (* Cut *) (euclidean__axioms.EF D C B A F C B E) as H33.
------------------------------- destruct H4 as [H33 H34].
destruct H3 as [H35 H36].
apply (@proposition__35A.proposition__35A D C B A F E H21 H25 H27 H32).
------------------------------- assert (* Cut *) (euclidean__axioms.EF D C B A E B C F) as H34.
-------------------------------- destruct H4 as [H34 H35].
destruct H3 as [H36 H37].
assert (* Cut *) ((euclidean__axioms.EF D C B A C B E F) /\ ((euclidean__axioms.EF D C B A E B C F) /\ ((euclidean__axioms.EF D C B A B E F C) /\ ((euclidean__axioms.EF D C B A C F E B) /\ ((euclidean__axioms.EF D C B A E F C B) /\ ((euclidean__axioms.EF D C B A B C F E) /\ (euclidean__axioms.EF D C B A F E B C))))))) as H38.
--------------------------------- apply (@euclidean__axioms.axiom__EFpermutation D C B A F C B E H33).
--------------------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H41.
-------------------------------- assert (* Cut *) (euclidean__axioms.EF E B C F D C B A) as H35.
--------------------------------- destruct H4 as [H35 H36].
destruct H3 as [H37 H38].
apply (@euclidean__axioms.axiom__EFsymmetric D C B A E B C F H34).
--------------------------------- assert (* Cut *) (euclidean__axioms.EF E B C F A B C D) as H36.
---------------------------------- destruct H4 as [H36 H37].
destruct H3 as [H38 H39].
assert (* Cut *) ((euclidean__axioms.EF E B C F C B A D) /\ ((euclidean__axioms.EF E B C F A B C D) /\ ((euclidean__axioms.EF E B C F B A D C) /\ ((euclidean__axioms.EF E B C F C D A B) /\ ((euclidean__axioms.EF E B C F A D C B) /\ ((euclidean__axioms.EF E B C F B C D A) /\ (euclidean__axioms.EF E B C F D A B C))))))) as H40.
----------------------------------- apply (@euclidean__axioms.axiom__EFpermutation E B C F D C B A H35).
----------------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H43.
---------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E B C F) as H37.
----------------------------------- destruct H4 as [H37 H38].
destruct H3 as [H39 H40].
apply (@euclidean__axioms.axiom__EFsymmetric E B C F A B C D H36).
----------------------------------- apply (@H15 H37).
------------------------ assert (* Cut *) (~(euclidean__axioms.BetS D A F)) as H27.
------------------------- intro H27.
assert (* Cut *) (exists H28, (euclidean__axioms.BetS C H28 F) /\ (euclidean__axioms.BetS B H28 A)) as H28.
-------------------------- destruct H4 as [H28 H29].
destruct H3 as [H30 H31].
apply (@lemma__parallelPasch.lemma__parallelPasch D C B A F H21 H27).
-------------------------- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H4 as [H33 H34].
destruct H3 as [H35 H36].
assert (* Cut *) (euclidean__axioms.BetS A H29 B) as H37.
--------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B H29 A H32).
--------------------------- assert (* Cut *) (euclidean__axioms.Col C H29 F) as H38.
---------------------------- right.
right.
right.
right.
left.
exact H31.
---------------------------- assert (* Cut *) (euclidean__axioms.Col C F H29) as H39.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col H29 C F) /\ ((euclidean__axioms.Col H29 F C) /\ ((euclidean__axioms.Col F C H29) /\ ((euclidean__axioms.Col C F H29) /\ (euclidean__axioms.Col F H29 C))))) as H39.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder C H29 F H38).
------------------------------ destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H46.
----------------------------- assert (* Cut *) (euclidean__axioms.nCol D A C) as H40.
------------------------------ assert (* Cut *) ((euclidean__axioms.nCol D A C) /\ ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol D A B)))) as H40.
------------------------------- apply (@lemma__parallelNC.lemma__parallelNC D A C B H20).
------------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H41.
------------------------------ assert (* Cut *) (euclidean__axioms.Col D A F) as H41.
------------------------------- right.
right.
right.
right.
left.
exact H27.
------------------------------- assert (* Cut *) (A = A) as H42.
-------------------------------- apply (@logic.eq__refl Point A).
-------------------------------- assert (* Cut *) (euclidean__axioms.Col D A A) as H43.
--------------------------------- right.
right.
left.
exact H42.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq A F) as H44.
---------------------------------- assert (* Cut *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq D A) /\ (euclidean__axioms.neq D F))) as H44.
----------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D A F H27).
----------------------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H45.
---------------------------------- assert (* Cut *) (euclidean__axioms.nCol A F C) as H45.
----------------------------------- apply (@euclidean__tactics.nCol__notCol A F C).
------------------------------------apply (@euclidean__tactics.nCol__not__Col A F C).
-------------------------------------apply (@lemma__NChelper.lemma__NChelper D A C A F H40 H43 H41 H44).


----------------------------------- assert (* Cut *) (euclidean__axioms.nCol C F A) as H46.
------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol F A C) /\ ((euclidean__axioms.nCol F C A) /\ ((euclidean__axioms.nCol C A F) /\ ((euclidean__axioms.nCol A C F) /\ (euclidean__axioms.nCol C F A))))) as H46.
------------------------------------- apply (@lemma__NCorder.lemma__NCorder A F C H45).
------------------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H54.
------------------------------------ assert (* Cut *) (euclidean__axioms.TS A C F B) as H47.
------------------------------------- exists H29.
split.
-------------------------------------- exact H37.
-------------------------------------- split.
--------------------------------------- exact H39.
--------------------------------------- exact H46.
------------------------------------- assert (* Cut *) (euclidean__axioms.TS B C F A) as H48.
-------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric C F A B H47).
-------------------------------------- assert (* Cut *) (euclidean__defs.Par E B C F) as H49.
--------------------------------------- assert (* Cut *) ((euclidean__defs.Par E F C B) /\ ((euclidean__defs.Par F E B C) /\ (euclidean__defs.Par E F B C))) as H49.
---------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip F E C B H24).
---------------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H33.
--------------------------------------- assert (* Cut *) (euclidean__defs.Par C F E B) as H50.
---------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric E B C F H49).
---------------------------------------- assert (* Cut *) (euclidean__defs.TP C F E B) as H51.
----------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B C F E B H50).
----------------------------------------- assert (* Cut *) (euclidean__defs.OS E B C F) as H52.
------------------------------------------ destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H57.
------------------------------------------ assert (* Cut *) (euclidean__axioms.TS E C F A) as H53.
------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation C F E B A H52 H48).
------------------------------------------- assert (exists e, (euclidean__axioms.BetS E e A) /\ ((euclidean__axioms.Col C F e) /\ (euclidean__axioms.nCol C F E))) as H54 by exact H53.
destruct H54 as [e H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
assert (* Cut *) (euclidean__axioms.neq E A) as H60.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq e A) /\ ((euclidean__axioms.neq E e) /\ (euclidean__axioms.neq E A))) as H60.
--------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E e A H56).
--------------------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H64.
-------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq e F)) as H61.
--------------------------------------------- intro H61.
assert (* Cut *) (euclidean__axioms.Col D A E) as H62.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H62.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A D E H1).
----------------------------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
exact H63.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D A) as H63.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq e A) /\ ((euclidean__axioms.neq E e) /\ (euclidean__axioms.neq E A))) as H63.
------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal E e A H56).
------------------------------------------------ destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H14.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F E) as H64.
------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col A F E).
-------------------------------------------------intro H64.
apply (@euclidean__tactics.Col__nCol__False A F E H64).
--------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D A F E H41 H62 H63).


------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E A F) as H65.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A))))) as H65.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A F E H64).
-------------------------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H70.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E e A) as H66.
-------------------------------------------------- right.
right.
right.
right.
left.
exact H56.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A e) as H67.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col e E A) /\ ((euclidean__axioms.Col e A E) /\ ((euclidean__axioms.Col A E e) /\ ((euclidean__axioms.Col E A e) /\ (euclidean__axioms.Col A e E))))) as H67.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E e A H66).
---------------------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H74.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F e) as H68.
---------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col A F e).
-----------------------------------------------------intro H68.
apply (@euclidean__tactics.Col__nCol__False A F e H68).
------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 E A F e H65 H67 H60).


---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e F A) as H69.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F A e) /\ ((euclidean__axioms.Col F e A) /\ ((euclidean__axioms.Col e A F) /\ ((euclidean__axioms.Col A e F) /\ (euclidean__axioms.Col e F A))))) as H69.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A F e H68).
------------------------------------------------------ destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H77.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e F C) as H70.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col F C e) /\ ((euclidean__axioms.Col F e C) /\ ((euclidean__axioms.Col e C F) /\ ((euclidean__axioms.Col C e F) /\ (euclidean__axioms.Col e F C))))) as H70.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C F e H58).
------------------------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H78.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col F A C) as H71.
------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col F A C).
--------------------------------------------------------intro H71.
apply (@euclidean__tactics.Col__nCol__False F A C H71).
---------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 e F A C H69 H70 H61).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C F A) as H72.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A F C) /\ ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C F A) /\ ((euclidean__axioms.Col F C A) /\ (euclidean__axioms.Col C A F))))) as H72.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F A C H71).
--------------------------------------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H77.
-------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False C F E H59).
---------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col C F E).
----------------------------------------------------------intro H73.
apply (@euclidean__tactics.Col__nCol__False C F A H46 H72).


--------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E F A) as H62.
---------------------------------------------- apply (@eq__ind euclidean__axioms.Point e (fun X => euclidean__axioms.BetS E X A)) with (y := F).
----------------------------------------------- exact H56.
-----------------------------------------------apply (@euclidean__tactics.NNPP (e = F) H61).

---------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A F E) as H63.
----------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E F A H62).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D A E) as H64.
------------------------------------------------ apply (@lemma__3__7b.lemma__3__7b D A F E H27 H63).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS E A D) as H65.
------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry D A E H64).
------------------------------------------------- apply (@H26 H65).
------------------------- assert (* Cut *) ((A = D) \/ ((A = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D A F) \/ ((euclidean__axioms.BetS A D F) \/ (euclidean__axioms.BetS A F D)))))) as H28.
-------------------------- destruct H4 as [H28 H29].
destruct H3 as [H30 H31].
exact H2.
-------------------------- assert (* Cut *) ((A = D) \/ ((A = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A E) \/ ((euclidean__axioms.BetS A D E) \/ (euclidean__axioms.BetS A E D)))))) as H29.
--------------------------- destruct H4 as [H29 H30].
destruct H3 as [H31 H32].
exact H1.
--------------------------- assert (* Cut *) (~(A = F)) as H30.
---------------------------- intro H30.
assert (* Cut *) ((F = D) \/ ((F = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A E) \/ ((euclidean__axioms.BetS A D E) \/ (euclidean__axioms.BetS A E D)))))) as H31.
----------------------------- destruct H4 as [H31 H32].
destruct H3 as [H33 H34].
apply (@eq__ind__r euclidean__axioms.Point F (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.Col A0 D E) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.neq A0 D) -> ((euclidean__axioms.neq D A0) -> ((~(euclidean__axioms.EF A0 B C D E B C F)) -> ((~(euclidean__axioms.BetS A0 D F)) -> ((~(euclidean__axioms.BetS A0 D E)) -> ((euclidean__defs.Par B A0 D C) -> ((euclidean__defs.Par D C B A0) -> ((euclidean__defs.Par D A0 C B) -> ((euclidean__defs.PG D C B A0) -> ((~(euclidean__axioms.BetS E A0 D)) -> ((~(euclidean__axioms.BetS D A0 F)) -> (((A0 = D) \/ ((A0 = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D A0 F) \/ ((euclidean__axioms.BetS A0 D F) \/ (euclidean__axioms.BetS A0 F D)))))) -> (((A0 = D) \/ ((A0 = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A0 E) \/ ((euclidean__axioms.BetS A0 D E) \/ (euclidean__axioms.BetS A0 E D)))))) -> ((F = D) \/ ((F = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A0 E) \/ ((euclidean__axioms.BetS A0 D E) \/ (euclidean__axioms.BetS A0 E D)))))))))))))))))))))))))))) with (x := A).
------------------------------intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
exact H55.

------------------------------ exact H30.
------------------------------ exact H.
------------------------------ exact H1.
------------------------------ exact H2.
------------------------------ exact H33.
------------------------------ exact H34.
------------------------------ exact H5.
------------------------------ exact H8.
------------------------------ exact H11.
------------------------------ exact H12.
------------------------------ exact H14.
------------------------------ exact H15.
------------------------------ exact H16.
------------------------------ exact H17.
------------------------------ exact H18.
------------------------------ exact H19.
------------------------------ exact H20.
------------------------------ exact H21.
------------------------------ exact H26.
------------------------------ exact H27.
------------------------------ exact H28.
------------------------------ exact H29.
----------------------------- assert (* Cut *) (euclidean__axioms.neq A F) as H32.
------------------------------ assert ((F = D) \/ ((F = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A E) \/ ((euclidean__axioms.BetS A D E) \/ (euclidean__axioms.BetS A E D)))))) as H32 by exact H31.
assert ((F = D) \/ ((F = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A E) \/ ((euclidean__axioms.BetS A D E) \/ (euclidean__axioms.BetS A E D)))))) as __TmpHyp by exact H32.
destruct __TmpHyp as [H33|H33].
------------------------------- assert (* Cut *) (A = D) as H34.
-------------------------------- destruct H4 as [H34 H35].
destruct H3 as [H36 H37].
apply (@eq__ind euclidean__axioms.Point A (fun F0 => (euclidean__defs.PG E B C F0) -> ((euclidean__axioms.Col A D F0) -> ((euclidean__defs.Par E B C F0) -> ((euclidean__defs.Par E F0 B C) -> ((euclidean__defs.Par E B F0 C) -> ((euclidean__defs.Par F0 C E B) -> ((euclidean__axioms.Cong E F0 B C) -> ((euclidean__axioms.Cong B C E F0) -> ((euclidean__axioms.Cong A D E F0) -> ((euclidean__axioms.neq E F0) -> ((~(euclidean__axioms.EF A B C D E B C F0)) -> ((~(euclidean__axioms.BetS A D F0)) -> ((euclidean__defs.Par B E F0 C) -> ((euclidean__defs.Par F0 C B E) -> ((euclidean__defs.Par F0 E C B) -> ((euclidean__defs.PG F0 C B E) -> ((~(euclidean__axioms.BetS D A F0)) -> (((A = D) \/ ((A = F0) \/ ((D = F0) \/ ((euclidean__axioms.BetS D A F0) \/ ((euclidean__axioms.BetS A D F0) \/ (euclidean__axioms.BetS A F0 D)))))) -> ((F0 = D) -> (A = D))))))))))))))))))))) with (y := F).
---------------------------------intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
assert (A = D) as H57 by exact H56.
exact H57.

--------------------------------- exact H30.
--------------------------------- exact H0.
--------------------------------- exact H2.
--------------------------------- exact H34.
--------------------------------- exact H35.
--------------------------------- exact H6.
--------------------------------- exact H7.
--------------------------------- exact H9.
--------------------------------- exact H10.
--------------------------------- exact H11.
--------------------------------- exact H13.
--------------------------------- exact H15.
--------------------------------- exact H16.
--------------------------------- exact H22.
--------------------------------- exact H23.
--------------------------------- exact H24.
--------------------------------- exact H25.
--------------------------------- exact H27.
--------------------------------- exact H28.
--------------------------------- exact H33.
-------------------------------- assert (* Cut *) (~(A = F)) as H35.
--------------------------------- intro H35.
apply (@H12 H34).
--------------------------------- exact H35.
------------------------------- destruct H33 as [H34|H34].
-------------------------------- assert (* Cut *) (~(A = F)) as H35.
--------------------------------- intro H35.
assert (* Cut *) (euclidean__axioms.neq F E) as H36.
---------------------------------- destruct H4 as [H36 H37].
destruct H3 as [H38 H39].
apply (@eq__ind__r euclidean__axioms.Point F (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.Col A0 D E) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.neq A0 D) -> ((euclidean__axioms.neq D A0) -> ((~(euclidean__axioms.EF A0 B C D E B C F)) -> ((~(euclidean__axioms.BetS A0 D F)) -> ((~(euclidean__axioms.BetS A0 D E)) -> ((euclidean__defs.Par B A0 D C) -> ((euclidean__defs.Par D C B A0) -> ((euclidean__defs.Par D A0 C B) -> ((euclidean__defs.PG D C B A0) -> ((~(euclidean__axioms.BetS E A0 D)) -> ((~(euclidean__axioms.BetS D A0 F)) -> (((A0 = D) \/ ((A0 = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D A0 F) \/ ((euclidean__axioms.BetS A0 D F) \/ (euclidean__axioms.BetS A0 F D)))))) -> (((A0 = D) \/ ((A0 = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A0 E) \/ ((euclidean__axioms.BetS A0 D E) \/ (euclidean__axioms.BetS A0 E D)))))) -> ((A0 = F) -> (euclidean__axioms.neq F E)))))))))))))))))))))))) with (x := A).
-----------------------------------intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
apply (@eq__ind__r euclidean__axioms.Point E (fun F0 => (euclidean__defs.PG F0 B C D) -> ((euclidean__defs.PG E B C F0) -> ((euclidean__defs.Par F0 D B C) -> ((euclidean__defs.Par F0 B C D) -> ((euclidean__axioms.Col F0 D F0) -> ((euclidean__axioms.Col F0 D E) -> ((euclidean__defs.Par E B C F0) -> ((euclidean__defs.Par E F0 B C) -> ((euclidean__defs.Par F0 B D C) -> ((euclidean__defs.Par E B F0 C) -> ((euclidean__defs.Par F0 C E B) -> ((euclidean__axioms.Cong F0 D B C) -> ((euclidean__axioms.Cong E F0 B C) -> ((euclidean__axioms.Cong B C E F0) -> ((euclidean__axioms.neq F0 D) -> ((euclidean__axioms.Cong F0 D E F0) -> ((euclidean__axioms.neq E F0) -> ((euclidean__defs.PG D C B F0) -> ((euclidean__defs.Par D F0 C B) -> ((euclidean__defs.Par D C B F0) -> ((euclidean__defs.Par B F0 D C) -> ((~(euclidean__axioms.BetS F0 D E)) -> ((~(euclidean__axioms.BetS F0 D F0)) -> ((~(euclidean__axioms.EF F0 B C D E B C F0)) -> ((euclidean__axioms.neq D F0) -> ((euclidean__defs.Par B E F0 C) -> ((euclidean__defs.Par F0 C B E) -> ((euclidean__defs.Par F0 E C B) -> ((euclidean__defs.PG F0 C B E) -> (((F0 = D) \/ ((F0 = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D F0 E) \/ ((euclidean__axioms.BetS F0 D E) \/ (euclidean__axioms.BetS F0 E D)))))) -> (((F0 = D) \/ ((F0 = F0) \/ ((D = F0) \/ ((euclidean__axioms.BetS D F0 F0) \/ ((euclidean__axioms.BetS F0 D F0) \/ (euclidean__axioms.BetS F0 F0 D)))))) -> ((~(euclidean__axioms.BetS D F0 F0)) -> ((~(euclidean__axioms.BetS E F0 D)) -> ((F0 = F0) -> (euclidean__axioms.neq F0 E)))))))))))))))))))))))))))))))))))) with (x := F).
------------------------------------intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
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
exact H78.

------------------------------------ exact H34.
------------------------------------ exact H40.
------------------------------------ exact H0.
------------------------------------ exact H44.
------------------------------------ exact H43.
------------------------------------ exact H42.
------------------------------------ exact H41.
------------------------------------ exact H36.
------------------------------------ exact H37.
------------------------------------ exact H45.
------------------------------------ exact H6.
------------------------------------ exact H7.
------------------------------------ exact H46.
------------------------------------ exact H9.
------------------------------------ exact H10.
------------------------------------ exact H48.
------------------------------------ exact H47.
------------------------------------ exact H13.
------------------------------------ exact H56.
------------------------------------ exact H55.
------------------------------------ exact H54.
------------------------------------ exact H53.
------------------------------------ exact H52.
------------------------------------ exact H51.
------------------------------------ exact H50.
------------------------------------ exact H49.
------------------------------------ exact H22.
------------------------------------ exact H23.
------------------------------------ exact H24.
------------------------------------ exact H25.
------------------------------------ exact H60.
------------------------------------ exact H59.
------------------------------------ exact H58.
------------------------------------ exact H57.
------------------------------------ exact H61.

----------------------------------- exact H30.
----------------------------------- exact H.
----------------------------------- exact H1.
----------------------------------- exact H2.
----------------------------------- exact H38.
----------------------------------- exact H39.
----------------------------------- exact H5.
----------------------------------- exact H8.
----------------------------------- exact H11.
----------------------------------- exact H12.
----------------------------------- exact H14.
----------------------------------- exact H15.
----------------------------------- exact H16.
----------------------------------- exact H17.
----------------------------------- exact H18.
----------------------------------- exact H19.
----------------------------------- exact H20.
----------------------------------- exact H21.
----------------------------------- exact H26.
----------------------------------- exact H27.
----------------------------------- exact H28.
----------------------------------- exact H29.
----------------------------------- exact H35.
---------------------------------- apply (@H36 H34).
--------------------------------- exact H35.
-------------------------------- destruct H34 as [H35|H35].
--------------------------------- assert (* Cut *) (~(A = F)) as H36.
---------------------------------- intro H36.
assert (* Cut *) (exists p, (euclidean__axioms.BetS E p C) /\ (euclidean__axioms.BetS B p F)) as H37.
----------------------------------- destruct H4 as [H37 H38].
destruct H3 as [H39 H40].
apply (@lemma__diagonalsmeet.lemma__diagonalsmeet E B C F H0).
----------------------------------- destruct H37 as [p H38].
destruct H38 as [H39 H40].
destruct H4 as [H41 H42].
destruct H3 as [H43 H44].
assert (* Cut *) (euclidean__axioms.Col E p C) as H45.
------------------------------------ right.
right.
right.
right.
left.
exact H39.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col B p F) as H46.
------------------------------------- right.
right.
right.
right.
left.
exact H40.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col F B p) as H47.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p B F) /\ ((euclidean__axioms.Col p F B) /\ ((euclidean__axioms.Col F B p) /\ ((euclidean__axioms.Col B F p) /\ (euclidean__axioms.Col F p B))))) as H47.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B p F H46).
--------------------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H52.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C p) as H48.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p E C) /\ ((euclidean__axioms.Col p C E) /\ ((euclidean__axioms.Col C E p) /\ ((euclidean__axioms.Col E C p) /\ (euclidean__axioms.Col C p E))))) as H48.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E p C H45).
---------------------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H55.
--------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E F C) as H49.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B E F) /\ ((euclidean__axioms.nCol B F C) /\ ((euclidean__axioms.nCol E F C) /\ (euclidean__axioms.nCol B E C)))) as H49.
----------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC B E F C H22).
----------------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H54.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq E C) as H50.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C E)))))) as H50.
------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct E F C H49).
------------------------------------------ destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H55.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E F B) as H51.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol E F B) /\ ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol F B C) /\ (euclidean__axioms.nCol E F C)))) as H51.
------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC E F B C H42).
------------------------------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H52.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq F B) as H52.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq B F) /\ (euclidean__axioms.neq B E)))))) as H52.
-------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct E F B H51).
-------------------------------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H55.
------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E C F B) as H53.
-------------------------------------------- exists p.
split.
--------------------------------------------- exact H50.
--------------------------------------------- split.
---------------------------------------------- exact H52.
---------------------------------------------- split.
----------------------------------------------- exact H48.
----------------------------------------------- exact H47.
-------------------------------------------- assert (* Cut *) (euclidean__defs.Meet D C F B) as H54.
--------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.Col A0 D E) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.neq A0 D) -> ((euclidean__axioms.neq D A0) -> ((~(euclidean__axioms.EF A0 B C D E B C F)) -> ((~(euclidean__axioms.BetS A0 D F)) -> ((~(euclidean__axioms.BetS A0 D E)) -> ((euclidean__defs.Par B A0 D C) -> ((euclidean__defs.Par D C B A0) -> ((euclidean__defs.Par D A0 C B) -> ((euclidean__defs.PG D C B A0) -> ((~(euclidean__axioms.BetS E A0 D)) -> ((~(euclidean__axioms.BetS D A0 F)) -> (((A0 = D) \/ ((A0 = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D A0 F) \/ ((euclidean__axioms.BetS A0 D F) \/ (euclidean__axioms.BetS A0 F D)))))) -> (((A0 = D) \/ ((A0 = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A0 E) \/ ((euclidean__axioms.BetS A0 D E) \/ (euclidean__axioms.BetS A0 E D)))))) -> ((A0 = F) -> (euclidean__defs.Meet D C F B)))))))))))))))))))))))) with (x := A).
----------------------------------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
apply (@eq__ind__r euclidean__axioms.Point E (fun D0 => (euclidean__defs.PG F B C D0) -> ((euclidean__defs.Par F D0 B C) -> ((euclidean__defs.Par F B C D0) -> ((euclidean__axioms.Col F D0 F) -> ((euclidean__axioms.Col F D0 E) -> ((euclidean__defs.Par F B D0 C) -> ((euclidean__axioms.Cong F D0 B C) -> ((euclidean__axioms.neq F D0) -> ((euclidean__axioms.Cong F D0 E F) -> ((euclidean__defs.PG D0 C B F) -> ((euclidean__defs.Par D0 F C B) -> ((euclidean__defs.Par D0 C B F) -> ((euclidean__defs.Par B F D0 C) -> ((~(euclidean__axioms.BetS F D0 E)) -> ((~(euclidean__axioms.BetS F D0 F)) -> ((~(euclidean__axioms.EF F B C D0 E B C F)) -> ((euclidean__axioms.neq D0 F) -> (((F = D0) \/ ((F = E) \/ ((D0 = E) \/ ((euclidean__axioms.BetS D0 F E) \/ ((euclidean__axioms.BetS F D0 E) \/ (euclidean__axioms.BetS F E D0)))))) -> (((F = D0) \/ ((F = F) \/ ((D0 = F) \/ ((euclidean__axioms.BetS D0 F F) \/ ((euclidean__axioms.BetS F D0 F) \/ (euclidean__axioms.BetS F F D0)))))) -> ((~(euclidean__axioms.BetS D0 F F)) -> ((~(euclidean__axioms.BetS E F D0)) -> ((F = F) -> (euclidean__defs.Meet D0 C F B)))))))))))))))))))))))) with (x := D).
-----------------------------------------------intro H76.
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
exact H53.

----------------------------------------------- exact H35.
----------------------------------------------- exact H54.
----------------------------------------------- exact H58.
----------------------------------------------- exact H57.
----------------------------------------------- exact H56.
----------------------------------------------- exact H55.
----------------------------------------------- exact H59.
----------------------------------------------- exact H60.
----------------------------------------------- exact H62.
----------------------------------------------- exact H61.
----------------------------------------------- exact H70.
----------------------------------------------- exact H69.
----------------------------------------------- exact H68.
----------------------------------------------- exact H67.
----------------------------------------------- exact H66.
----------------------------------------------- exact H65.
----------------------------------------------- exact H64.
----------------------------------------------- exact H63.
----------------------------------------------- exact H74.
----------------------------------------------- exact H73.
----------------------------------------------- exact H72.
----------------------------------------------- exact H71.
----------------------------------------------- exact H75.

---------------------------------------------- exact H30.
---------------------------------------------- exact H.
---------------------------------------------- exact H1.
---------------------------------------------- exact H2.
---------------------------------------------- exact H43.
---------------------------------------------- exact H44.
---------------------------------------------- exact H5.
---------------------------------------------- exact H8.
---------------------------------------------- exact H11.
---------------------------------------------- exact H12.
---------------------------------------------- exact H14.
---------------------------------------------- exact H15.
---------------------------------------------- exact H16.
---------------------------------------------- exact H17.
---------------------------------------------- exact H18.
---------------------------------------------- exact H19.
---------------------------------------------- exact H20.
---------------------------------------------- exact H21.
---------------------------------------------- exact H26.
---------------------------------------------- exact H27.
---------------------------------------------- exact H28.
---------------------------------------------- exact H29.
---------------------------------------------- exact H36.
--------------------------------------------- assert (* Cut *) (euclidean__defs.Meet D C A B) as H55.
---------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.Col A0 D E) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.neq A0 D) -> ((euclidean__axioms.neq D A0) -> ((~(euclidean__axioms.EF A0 B C D E B C F)) -> ((~(euclidean__axioms.BetS A0 D F)) -> ((~(euclidean__axioms.BetS A0 D E)) -> ((euclidean__defs.Par B A0 D C) -> ((euclidean__defs.Par D C B A0) -> ((euclidean__defs.Par D A0 C B) -> ((euclidean__defs.PG D C B A0) -> ((~(euclidean__axioms.BetS E A0 D)) -> ((~(euclidean__axioms.BetS D A0 F)) -> (((A0 = D) \/ ((A0 = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D A0 F) \/ ((euclidean__axioms.BetS A0 D F) \/ (euclidean__axioms.BetS A0 F D)))))) -> (((A0 = D) \/ ((A0 = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A0 E) \/ ((euclidean__axioms.BetS A0 D E) \/ (euclidean__axioms.BetS A0 E D)))))) -> ((A0 = F) -> (euclidean__defs.Meet D C A0 B)))))))))))))))))))))))) with (x := A).
-----------------------------------------------intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
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
apply (@eq__ind__r euclidean__axioms.Point E (fun D0 => (euclidean__defs.PG F B C D0) -> ((euclidean__defs.Par F D0 B C) -> ((euclidean__defs.Par F B C D0) -> ((euclidean__axioms.Col F D0 F) -> ((euclidean__axioms.Col F D0 E) -> ((euclidean__defs.Par F B D0 C) -> ((euclidean__axioms.Cong F D0 B C) -> ((euclidean__axioms.neq F D0) -> ((euclidean__axioms.Cong F D0 E F) -> ((euclidean__defs.PG D0 C B F) -> ((euclidean__defs.Par D0 F C B) -> ((euclidean__defs.Par D0 C B F) -> ((euclidean__defs.Par B F D0 C) -> ((~(euclidean__axioms.BetS F D0 E)) -> ((~(euclidean__axioms.BetS F D0 F)) -> ((~(euclidean__axioms.EF F B C D0 E B C F)) -> ((euclidean__axioms.neq D0 F) -> (((F = D0) \/ ((F = E) \/ ((D0 = E) \/ ((euclidean__axioms.BetS D0 F E) \/ ((euclidean__axioms.BetS F D0 E) \/ (euclidean__axioms.BetS F E D0)))))) -> (((F = D0) \/ ((F = F) \/ ((D0 = F) \/ ((euclidean__axioms.BetS D0 F F) \/ ((euclidean__axioms.BetS F D0 F) \/ (euclidean__axioms.BetS F F D0)))))) -> ((~(euclidean__axioms.BetS D0 F F)) -> ((~(euclidean__axioms.BetS E F D0)) -> ((euclidean__defs.Meet D0 C F B) -> ((F = F) -> (euclidean__defs.Meet D0 C F B))))))))))))))))))))))))) with (x := D).
------------------------------------------------intro H77.
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
exact H98.

------------------------------------------------ exact H35.
------------------------------------------------ exact H55.
------------------------------------------------ exact H59.
------------------------------------------------ exact H58.
------------------------------------------------ exact H57.
------------------------------------------------ exact H56.
------------------------------------------------ exact H60.
------------------------------------------------ exact H61.
------------------------------------------------ exact H63.
------------------------------------------------ exact H62.
------------------------------------------------ exact H71.
------------------------------------------------ exact H70.
------------------------------------------------ exact H69.
------------------------------------------------ exact H68.
------------------------------------------------ exact H67.
------------------------------------------------ exact H66.
------------------------------------------------ exact H65.
------------------------------------------------ exact H64.
------------------------------------------------ exact H75.
------------------------------------------------ exact H74.
------------------------------------------------ exact H73.
------------------------------------------------ exact H72.
------------------------------------------------ exact H54.
------------------------------------------------ exact H76.

----------------------------------------------- exact H30.
----------------------------------------------- exact H.
----------------------------------------------- exact H1.
----------------------------------------------- exact H2.
----------------------------------------------- exact H43.
----------------------------------------------- exact H44.
----------------------------------------------- exact H5.
----------------------------------------------- exact H8.
----------------------------------------------- exact H11.
----------------------------------------------- exact H12.
----------------------------------------------- exact H14.
----------------------------------------------- exact H15.
----------------------------------------------- exact H16.
----------------------------------------------- exact H17.
----------------------------------------------- exact H18.
----------------------------------------------- exact H19.
----------------------------------------------- exact H20.
----------------------------------------------- exact H21.
----------------------------------------------- exact H26.
----------------------------------------------- exact H27.
----------------------------------------------- exact H28.
----------------------------------------------- exact H29.
----------------------------------------------- exact H36.
---------------------------------------------- assert (* Cut *) (euclidean__defs.Par D C A B) as H56.
----------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A B D C H5).
----------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet D C A B)) as H57.
------------------------------------------------ assert (exists U V u v X, (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H57 by exact H56.
assert (exists U V u v X, (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H57.
destruct __TmpHyp0 as [x H58].
destruct H58 as [x0 H59].
destruct H59 as [x1 H60].
destruct H60 as [x2 H61].
destruct H61 as [x3 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H83 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H83.
destruct __TmpHyp1 as [x4 H84].
destruct H84 as [x5 H85].
destruct H85 as [x6 H86].
destruct H86 as [x7 H87].
destruct H87 as [x8 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H109 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H109.
destruct __TmpHyp2 as [x9 H110].
destruct H110 as [x10 H111].
destruct H111 as [x11 H112].
destruct H112 as [x12 H113].
destruct H113 as [x13 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
assert (exists U V u v X, (euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col B E U) /\ ((euclidean__axioms.Col B E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B E F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H135 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col B E U) /\ ((euclidean__axioms.Col B E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B E F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H135.
destruct __TmpHyp3 as [x14 H136].
destruct H136 as [x15 H137].
destruct H137 as [x16 H138].
destruct H138 as [x17 H139].
destruct H139 as [x18 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
assert (exists U V u v X, (euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col D A U) /\ ((euclidean__axioms.Col D A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D A C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H161 by exact H20.
assert (exists U V u v X, (euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col D A U) /\ ((euclidean__axioms.Col D A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D A C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H161.
destruct __TmpHyp4 as [x19 H162].
destruct H162 as [x20 H163].
destruct H163 as [x21 H164].
destruct H164 as [x22 H165].
destruct H165 as [x23 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
assert (exists U V u v X, (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H187 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H187.
destruct __TmpHyp5 as [x24 H188].
destruct H188 as [x25 H189].
destruct H189 as [x26 H190].
destruct H190 as [x27 H191].
destruct H191 as [x28 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
destruct H198 as [H199 H200].
destruct H200 as [H201 H202].
destruct H202 as [H203 H204].
destruct H204 as [H205 H206].
destruct H206 as [H207 H208].
destruct H208 as [H209 H210].
destruct H210 as [H211 H212].
assert (exists U V u v X, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B A D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H213 by exact H18.
assert (exists U V u v X, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B A D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H213.
destruct __TmpHyp6 as [x29 H214].
destruct H214 as [x30 H215].
destruct H215 as [x31 H216].
destruct H216 as [x32 H217].
destruct H217 as [x33 H218].
destruct H218 as [H219 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
destruct H232 as [H233 H234].
destruct H234 as [H235 H236].
destruct H236 as [H237 H238].
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H239 by exact H7.
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H239.
destruct __TmpHyp7 as [x34 H240].
destruct H240 as [x35 H241].
destruct H241 as [x36 H242].
destruct H242 as [x37 H243].
destruct H243 as [x38 H244].
destruct H244 as [H245 H246].
destruct H246 as [H247 H248].
destruct H248 as [H249 H250].
destruct H250 as [H251 H252].
destruct H252 as [H253 H254].
destruct H254 as [H255 H256].
destruct H256 as [H257 H258].
destruct H258 as [H259 H260].
destruct H260 as [H261 H262].
destruct H262 as [H263 H264].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H265 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H265.
destruct __TmpHyp8 as [x39 H266].
destruct H266 as [x40 H267].
destruct H267 as [x41 H268].
destruct H268 as [x42 H269].
destruct H269 as [x43 H270].
destruct H270 as [H271 H272].
destruct H272 as [H273 H274].
destruct H274 as [H275 H276].
destruct H276 as [H277 H278].
destruct H278 as [H279 H280].
destruct H280 as [H281 H282].
destruct H282 as [H283 H284].
destruct H284 as [H285 H286].
destruct H286 as [H287 H288].
destruct H288 as [H289 H290].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H291 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp9 by exact H291.
destruct __TmpHyp9 as [x44 H292].
destruct H292 as [x45 H293].
destruct H293 as [x46 H294].
destruct H294 as [x47 H295].
destruct H295 as [x48 H296].
destruct H296 as [H297 H298].
destruct H298 as [H299 H300].
destruct H300 as [H301 H302].
destruct H302 as [H303 H304].
destruct H304 as [H305 H306].
destruct H306 as [H307 H308].
destruct H308 as [H309 H310].
destruct H310 as [H311 H312].
destruct H312 as [H313 H314].
destruct H314 as [H315 H316].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H317 by exact H42.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp10 by exact H317.
destruct __TmpHyp10 as [x49 H318].
destruct H318 as [x50 H319].
destruct H319 as [x51 H320].
destruct H320 as [x52 H321].
destruct H321 as [x53 H322].
destruct H322 as [H323 H324].
destruct H324 as [H325 H326].
destruct H326 as [H327 H328].
destruct H328 as [H329 H330].
destruct H330 as [H331 H332].
destruct H332 as [H333 H334].
destruct H334 as [H335 H336].
destruct H336 as [H337 H338].
destruct H338 as [H339 H340].
destruct H340 as [H341 H342].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H343 by exact H41.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp11 by exact H343.
destruct __TmpHyp11 as [x54 H344].
destruct H344 as [x55 H345].
destruct H345 as [x56 H346].
destruct H346 as [x57 H347].
destruct H347 as [x58 H348].
destruct H348 as [H349 H350].
destruct H350 as [H351 H352].
destruct H352 as [H353 H354].
destruct H354 as [H355 H356].
destruct H356 as [H357 H358].
destruct H358 as [H359 H360].
destruct H360 as [H361 H362].
destruct H362 as [H363 H364].
destruct H364 as [H365 H366].
destruct H366 as [H367 H368].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H369 by exact H44.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp12 by exact H369.
destruct __TmpHyp12 as [x59 H370].
destruct H370 as [x60 H371].
destruct H371 as [x61 H372].
destruct H372 as [x62 H373].
destruct H373 as [x63 H374].
destruct H374 as [H375 H376].
destruct H376 as [H377 H378].
destruct H378 as [H379 H380].
destruct H380 as [H381 H382].
destruct H382 as [H383 H384].
destruct H384 as [H385 H386].
destruct H386 as [H387 H388].
destruct H388 as [H389 H390].
destruct H390 as [H391 H392].
destruct H392 as [H393 H394].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H395 by exact H43.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp13 by exact H395.
destruct __TmpHyp13 as [x64 H396].
destruct H396 as [x65 H397].
destruct H397 as [x66 H398].
destruct H398 as [x67 H399].
destruct H399 as [x68 H400].
destruct H400 as [H401 H402].
destruct H402 as [H403 H404].
destruct H404 as [H405 H406].
destruct H406 as [H407 H408].
destruct H408 as [H409 H410].
destruct H410 as [H411 H412].
destruct H412 as [H413 H414].
destruct H414 as [H415 H416].
destruct H416 as [H417 H418].
destruct H418 as [H419 H420].
exact H79.
------------------------------------------------ apply (@H57 H55).
---------------------------------- exact H36.
--------------------------------- destruct H35 as [H36|H36].
---------------------------------- assert (* Cut *) (~(A = F)) as H37.
----------------------------------- intro H37.
assert (* Cut *) (euclidean__axioms.BetS E A D) as H38.
------------------------------------ destruct H4 as [H38 H39].
destruct H3 as [H40 H41].
apply (@euclidean__axioms.axiom__betweennesssymmetry D A E H36).
------------------------------------ apply (@H26 H38).
----------------------------------- exact H37.
---------------------------------- destruct H36 as [H37|H37].
----------------------------------- assert (* Cut *) (~(A = F)) as H38.
------------------------------------ intro H38.
apply (@H17 H37).
------------------------------------ exact H38.
----------------------------------- assert (* Cut *) (~(A = F)) as H38.
------------------------------------ intro H38.
assert (* Cut *) (euclidean__axioms.Cong A E A E) as H39.
------------------------------------- destruct H4 as [H39 H40].
destruct H3 as [H41 H42].
apply (@euclidean__axioms.cn__congruencereflexive A E).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F E A E) as H40.
-------------------------------------- destruct H4 as [H40 H41].
destruct H3 as [H42 H43].
apply (@eq__ind__r euclidean__axioms.Point F (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.Col A0 D E) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.neq A0 D) -> ((euclidean__axioms.neq D A0) -> ((~(euclidean__axioms.EF A0 B C D E B C F)) -> ((~(euclidean__axioms.BetS A0 D F)) -> ((~(euclidean__axioms.BetS A0 D E)) -> ((euclidean__defs.Par B A0 D C) -> ((euclidean__defs.Par D C B A0) -> ((euclidean__defs.Par D A0 C B) -> ((euclidean__defs.PG D C B A0) -> ((~(euclidean__axioms.BetS E A0 D)) -> ((~(euclidean__axioms.BetS D A0 F)) -> (((A0 = D) \/ ((A0 = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D A0 F) \/ ((euclidean__axioms.BetS A0 D F) \/ (euclidean__axioms.BetS A0 F D)))))) -> (((A0 = D) \/ ((A0 = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A0 E) \/ ((euclidean__axioms.BetS A0 D E) \/ (euclidean__axioms.BetS A0 E D)))))) -> ((euclidean__axioms.BetS A0 E D) -> ((A0 = F) -> ((euclidean__axioms.Cong A0 E A0 E) -> (euclidean__axioms.Cong F E A0 E)))))))))))))))))))))))))) with (x := A).
---------------------------------------intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
assert (F = F) as H68 by exact H66.
exact H67.

--------------------------------------- exact H30.
--------------------------------------- exact H.
--------------------------------------- exact H1.
--------------------------------------- exact H2.
--------------------------------------- exact H42.
--------------------------------------- exact H43.
--------------------------------------- exact H5.
--------------------------------------- exact H8.
--------------------------------------- exact H11.
--------------------------------------- exact H12.
--------------------------------------- exact H14.
--------------------------------------- exact H15.
--------------------------------------- exact H16.
--------------------------------------- exact H17.
--------------------------------------- exact H18.
--------------------------------------- exact H19.
--------------------------------------- exact H20.
--------------------------------------- exact H21.
--------------------------------------- exact H26.
--------------------------------------- exact H27.
--------------------------------------- exact H28.
--------------------------------------- exact H29.
--------------------------------------- exact H37.
--------------------------------------- exact H38.
--------------------------------------- exact H39.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A E F E) as H41.
--------------------------------------- destruct H4 as [H41 H42].
destruct H3 as [H43 H44].
apply (@eq__ind__r euclidean__axioms.Point F (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.Col A0 D E) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.neq A0 D) -> ((euclidean__axioms.neq D A0) -> ((~(euclidean__axioms.EF A0 B C D E B C F)) -> ((~(euclidean__axioms.BetS A0 D F)) -> ((~(euclidean__axioms.BetS A0 D E)) -> ((euclidean__defs.Par B A0 D C) -> ((euclidean__defs.Par D C B A0) -> ((euclidean__defs.Par D A0 C B) -> ((euclidean__defs.PG D C B A0) -> ((~(euclidean__axioms.BetS E A0 D)) -> ((~(euclidean__axioms.BetS D A0 F)) -> (((A0 = D) \/ ((A0 = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D A0 F) \/ ((euclidean__axioms.BetS A0 D F) \/ (euclidean__axioms.BetS A0 F D)))))) -> (((A0 = D) \/ ((A0 = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A0 E) \/ ((euclidean__axioms.BetS A0 D E) \/ (euclidean__axioms.BetS A0 E D)))))) -> ((euclidean__axioms.BetS A0 E D) -> ((A0 = F) -> ((euclidean__axioms.Cong A0 E A0 E) -> ((euclidean__axioms.Cong F E A0 E) -> (euclidean__axioms.Cong A0 E F E))))))))))))))))))))))))))) with (x := A).
----------------------------------------intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
assert (F = F) as H70 by exact H67.
exact H68.

---------------------------------------- exact H30.
---------------------------------------- exact H.
---------------------------------------- exact H1.
---------------------------------------- exact H2.
---------------------------------------- exact H43.
---------------------------------------- exact H44.
---------------------------------------- exact H5.
---------------------------------------- exact H8.
---------------------------------------- exact H11.
---------------------------------------- exact H12.
---------------------------------------- exact H14.
---------------------------------------- exact H15.
---------------------------------------- exact H16.
---------------------------------------- exact H17.
---------------------------------------- exact H18.
---------------------------------------- exact H19.
---------------------------------------- exact H20.
---------------------------------------- exact H21.
---------------------------------------- exact H26.
---------------------------------------- exact H27.
---------------------------------------- exact H28.
---------------------------------------- exact H29.
---------------------------------------- exact H37.
---------------------------------------- exact H38.
---------------------------------------- exact H39.
---------------------------------------- exact H40.
--------------------------------------- assert (* Cut *) (euclidean__defs.Lt F E A D) as H42.
---------------------------------------- exists E.
split.
----------------------------------------- exact H37.
----------------------------------------- exact H41.
---------------------------------------- assert (* Cut *) (euclidean__defs.Lt F E E F) as H43.
----------------------------------------- destruct H4 as [H43 H44].
destruct H3 as [H45 H46].
apply (@lemma__lessthancongruence.lemma__lessthancongruence F E A D E F H42 H11).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E F F E) as H44.
------------------------------------------ destruct H4 as [H44 H45].
destruct H3 as [H46 H47].
apply (@euclidean__axioms.cn__equalityreverse E F).
------------------------------------------ assert (* Cut *) (euclidean__defs.Lt F E F E) as H45.
------------------------------------------- destruct H4 as [H45 H46].
destruct H3 as [H47 H48].
apply (@lemma__lessthancongruence.lemma__lessthancongruence F E E F F E H43 H44).
------------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt F E F E)) as H46.
-------------------------------------------- destruct H4 as [H46 H47].
destruct H3 as [H48 H49].
apply (@lemma__trichotomy2.lemma__trichotomy2 F E F E H45).
-------------------------------------------- apply (@H46 H45).
------------------------------------ exact H38.
------------------------------ apply (@H32 H30).
---------------------------- assert (* Cut *) (~(D = F)) as H31.
----------------------------- intro H31.
assert (* Cut *) ((A = F) \/ ((A = E) \/ ((F = E) \/ ((euclidean__axioms.BetS D A E) \/ ((euclidean__axioms.BetS A D E) \/ (euclidean__axioms.BetS A E D)))))) as H32.
------------------------------ destruct H4 as [H32 H33].
destruct H3 as [H34 H35].
apply (@eq__ind__r euclidean__axioms.Point F (fun D0 => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.Col A D0 E) -> ((euclidean__axioms.Col A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.neq A D0) -> ((euclidean__axioms.neq D0 A) -> ((~(euclidean__axioms.EF A B C D0 E B C F)) -> ((~(euclidean__axioms.BetS A D0 F)) -> ((~(euclidean__axioms.BetS A D0 E)) -> ((euclidean__defs.Par B A D0 C) -> ((euclidean__defs.Par D0 C B A) -> ((euclidean__defs.Par D0 A C B) -> ((euclidean__defs.PG D0 C B A) -> ((~(euclidean__axioms.BetS E A D0)) -> ((~(euclidean__axioms.BetS D0 A F)) -> (((A = D0) \/ ((A = F) \/ ((D0 = F) \/ ((euclidean__axioms.BetS D0 A F) \/ ((euclidean__axioms.BetS A D0 F) \/ (euclidean__axioms.BetS A F D0)))))) -> (((A = D0) \/ ((A = E) \/ ((D0 = E) \/ ((euclidean__axioms.BetS D0 A E) \/ ((euclidean__axioms.BetS A D0 E) \/ (euclidean__axioms.BetS A E D0)))))) -> ((A = F) \/ ((A = E) \/ ((F = E) \/ ((euclidean__axioms.BetS D0 A E) \/ ((euclidean__axioms.BetS A D0 E) \/ (euclidean__axioms.BetS A E D0)))))))))))))))))))))))))))) with (x := D).
-------------------------------intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
exact H56.

------------------------------- exact H31.
------------------------------- exact H.
------------------------------- exact H1.
------------------------------- exact H2.
------------------------------- exact H34.
------------------------------- exact H35.
------------------------------- exact H5.
------------------------------- exact H8.
------------------------------- exact H11.
------------------------------- exact H12.
------------------------------- exact H14.
------------------------------- exact H15.
------------------------------- exact H16.
------------------------------- exact H17.
------------------------------- exact H18.
------------------------------- exact H19.
------------------------------- exact H20.
------------------------------- exact H21.
------------------------------- exact H26.
------------------------------- exact H27.
------------------------------- exact H28.
------------------------------- exact H29.
------------------------------ assert (* Cut *) (euclidean__axioms.neq D F) as H33.
------------------------------- assert ((A = F) \/ ((A = E) \/ ((F = E) \/ ((euclidean__axioms.BetS D A E) \/ ((euclidean__axioms.BetS A D E) \/ (euclidean__axioms.BetS A E D)))))) as H33 by exact H32.
assert ((A = F) \/ ((A = E) \/ ((F = E) \/ ((euclidean__axioms.BetS D A E) \/ ((euclidean__axioms.BetS A D E) \/ (euclidean__axioms.BetS A E D)))))) as __TmpHyp by exact H33.
destruct __TmpHyp as [H34|H34].
-------------------------------- assert (* Cut *) (~(D = F)) as H35.
--------------------------------- intro H35.
apply (@H30 H34).
--------------------------------- exact H35.
-------------------------------- destruct H34 as [H35|H35].
--------------------------------- assert (* Cut *) (~(D = F)) as H36.
---------------------------------- intro H36.
assert (* Cut *) (exists M, (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H37.
----------------------------------- destruct H4 as [H37 H38].
destruct H3 as [H39 H40].
apply (@lemma__diagonalsmeet.lemma__diagonalsmeet A B C D H).
----------------------------------- destruct H37 as [M H38].
destruct H38 as [H39 H40].
destruct H4 as [H41 H42].
destruct H3 as [H43 H44].
assert (* Cut *) (~(euclidean__axioms.Col A B C)) as H45.
------------------------------------ intro H45.
assert (* Cut *) (C = C) as H46.
------------------------------------- apply (@logic.eq__refl Point C).
------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D C) as H47.
-------------------------------------- right.
left.
exact H46.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq A B) as H48.
--------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H48 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H48.
destruct __TmpHyp0 as [x H49].
destruct H49 as [x0 H50].
destruct H50 as [x1 H51].
destruct H51 as [x2 H52].
destruct H52 as [x3 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H74 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H74.
destruct __TmpHyp1 as [x4 H75].
destruct H75 as [x5 H76].
destruct H76 as [x6 H77].
destruct H77 as [x7 H78].
destruct H78 as [x8 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
assert (exists U V u v X, (euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col B E U) /\ ((euclidean__axioms.Col B E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B E F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H100 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col B E U) /\ ((euclidean__axioms.Col B E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B E F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H100.
destruct __TmpHyp2 as [x9 H101].
destruct H101 as [x10 H102].
destruct H102 as [x11 H103].
destruct H103 as [x12 H104].
destruct H104 as [x13 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
assert (exists U V u v X, (euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col D A U) /\ ((euclidean__axioms.Col D A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D A C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H126 by exact H20.
assert (exists U V u v X, (euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col D A U) /\ ((euclidean__axioms.Col D A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D A C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H126.
destruct __TmpHyp3 as [x14 H127].
destruct H127 as [x15 H128].
destruct H128 as [x16 H129].
destruct H129 as [x17 H130].
destruct H130 as [x18 H131].
destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
assert (exists U V u v X, (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H152 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H152.
destruct __TmpHyp4 as [x19 H153].
destruct H153 as [x20 H154].
destruct H154 as [x21 H155].
destruct H155 as [x22 H156].
destruct H156 as [x23 H157].
destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
assert (exists U V u v X, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B A D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H178 by exact H18.
assert (exists U V u v X, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B A D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H178.
destruct __TmpHyp5 as [x24 H179].
destruct H179 as [x25 H180].
destruct H180 as [x26 H181].
destruct H181 as [x27 H182].
destruct H182 as [x28 H183].
destruct H183 as [H184 H185].
destruct H185 as [H186 H187].
destruct H187 as [H188 H189].
destruct H189 as [H190 H191].
destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
destruct H199 as [H200 H201].
destruct H201 as [H202 H203].
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H204 by exact H7.
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H204.
destruct __TmpHyp6 as [x29 H205].
destruct H205 as [x30 H206].
destruct H206 as [x31 H207].
destruct H207 as [x32 H208].
destruct H208 as [x33 H209].
destruct H209 as [H210 H211].
destruct H211 as [H212 H213].
destruct H213 as [H214 H215].
destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
destruct H219 as [H220 H221].
destruct H221 as [H222 H223].
destruct H223 as [H224 H225].
destruct H225 as [H226 H227].
destruct H227 as [H228 H229].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H230 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H230.
destruct __TmpHyp7 as [x34 H231].
destruct H231 as [x35 H232].
destruct H232 as [x36 H233].
destruct H233 as [x37 H234].
destruct H234 as [x38 H235].
destruct H235 as [H236 H237].
destruct H237 as [H238 H239].
destruct H239 as [H240 H241].
destruct H241 as [H242 H243].
destruct H243 as [H244 H245].
destruct H245 as [H246 H247].
destruct H247 as [H248 H249].
destruct H249 as [H250 H251].
destruct H251 as [H252 H253].
destruct H253 as [H254 H255].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H256 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H256.
destruct __TmpHyp8 as [x39 H257].
destruct H257 as [x40 H258].
destruct H258 as [x41 H259].
destruct H259 as [x42 H260].
destruct H260 as [x43 H261].
destruct H261 as [H262 H263].
destruct H263 as [H264 H265].
destruct H265 as [H266 H267].
destruct H267 as [H268 H269].
destruct H269 as [H270 H271].
destruct H271 as [H272 H273].
destruct H273 as [H274 H275].
destruct H275 as [H276 H277].
destruct H277 as [H278 H279].
destruct H279 as [H280 H281].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H282 by exact H42.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp9 by exact H282.
destruct __TmpHyp9 as [x44 H283].
destruct H283 as [x45 H284].
destruct H284 as [x46 H285].
destruct H285 as [x47 H286].
destruct H286 as [x48 H287].
destruct H287 as [H288 H289].
destruct H289 as [H290 H291].
destruct H291 as [H292 H293].
destruct H293 as [H294 H295].
destruct H295 as [H296 H297].
destruct H297 as [H298 H299].
destruct H299 as [H300 H301].
destruct H301 as [H302 H303].
destruct H303 as [H304 H305].
destruct H305 as [H306 H307].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H308 by exact H41.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp10 by exact H308.
destruct __TmpHyp10 as [x49 H309].
destruct H309 as [x50 H310].
destruct H310 as [x51 H311].
destruct H311 as [x52 H312].
destruct H312 as [x53 H313].
destruct H313 as [H314 H315].
destruct H315 as [H316 H317].
destruct H317 as [H318 H319].
destruct H319 as [H320 H321].
destruct H321 as [H322 H323].
destruct H323 as [H324 H325].
destruct H325 as [H326 H327].
destruct H327 as [H328 H329].
destruct H329 as [H330 H331].
destruct H331 as [H332 H333].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H334 by exact H44.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp11 by exact H334.
destruct __TmpHyp11 as [x54 H335].
destruct H335 as [x55 H336].
destruct H336 as [x56 H337].
destruct H337 as [x57 H338].
destruct H338 as [x58 H339].
destruct H339 as [H340 H341].
destruct H341 as [H342 H343].
destruct H343 as [H344 H345].
destruct H345 as [H346 H347].
destruct H347 as [H348 H349].
destruct H349 as [H350 H351].
destruct H351 as [H352 H353].
destruct H353 as [H354 H355].
destruct H355 as [H356 H357].
destruct H357 as [H358 H359].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H360 by exact H43.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp12 by exact H360.
destruct __TmpHyp12 as [x59 H361].
destruct H361 as [x60 H362].
destruct H362 as [x61 H363].
destruct H363 as [x62 H364].
destruct H364 as [x63 H365].
destruct H365 as [H366 H367].
destruct H367 as [H368 H369].
destruct H369 as [H370 H371].
destruct H371 as [H372 H373].
destruct H373 as [H374 H375].
destruct H375 as [H376 H377].
destruct H377 as [H378 H379].
destruct H379 as [H380 H381].
destruct H381 as [H382 H383].
destruct H383 as [H384 H385].
exact H366.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H49.
---------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H49 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H49.
destruct __TmpHyp0 as [x H50].
destruct H50 as [x0 H51].
destruct H51 as [x1 H52].
destruct H52 as [x2 H53].
destruct H53 as [x3 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H75 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H75.
destruct __TmpHyp1 as [x4 H76].
destruct H76 as [x5 H77].
destruct H77 as [x6 H78].
destruct H78 as [x7 H79].
destruct H79 as [x8 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
assert (exists U V u v X, (euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col B E U) /\ ((euclidean__axioms.Col B E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B E F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H101 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col B E U) /\ ((euclidean__axioms.Col B E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B E F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H101.
destruct __TmpHyp2 as [x9 H102].
destruct H102 as [x10 H103].
destruct H103 as [x11 H104].
destruct H104 as [x12 H105].
destruct H105 as [x13 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
assert (exists U V u v X, (euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col D A U) /\ ((euclidean__axioms.Col D A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D A C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H127 by exact H20.
assert (exists U V u v X, (euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col D A U) /\ ((euclidean__axioms.Col D A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D A C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H127.
destruct __TmpHyp3 as [x14 H128].
destruct H128 as [x15 H129].
destruct H129 as [x16 H130].
destruct H130 as [x17 H131].
destruct H131 as [x18 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
assert (exists U V u v X, (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H153 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H153.
destruct __TmpHyp4 as [x19 H154].
destruct H154 as [x20 H155].
destruct H155 as [x21 H156].
destruct H156 as [x22 H157].
destruct H157 as [x23 H158].
destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
assert (exists U V u v X, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B A D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H179 by exact H18.
assert (exists U V u v X, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B A D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H179.
destruct __TmpHyp5 as [x24 H180].
destruct H180 as [x25 H181].
destruct H181 as [x26 H182].
destruct H182 as [x27 H183].
destruct H183 as [x28 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
destruct H198 as [H199 H200].
destruct H200 as [H201 H202].
destruct H202 as [H203 H204].
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H205 by exact H7.
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H205.
destruct __TmpHyp6 as [x29 H206].
destruct H206 as [x30 H207].
destruct H207 as [x31 H208].
destruct H208 as [x32 H209].
destruct H209 as [x33 H210].
destruct H210 as [H211 H212].
destruct H212 as [H213 H214].
destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
destruct H218 as [H219 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H231 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H231.
destruct __TmpHyp7 as [x34 H232].
destruct H232 as [x35 H233].
destruct H233 as [x36 H234].
destruct H234 as [x37 H235].
destruct H235 as [x38 H236].
destruct H236 as [H237 H238].
destruct H238 as [H239 H240].
destruct H240 as [H241 H242].
destruct H242 as [H243 H244].
destruct H244 as [H245 H246].
destruct H246 as [H247 H248].
destruct H248 as [H249 H250].
destruct H250 as [H251 H252].
destruct H252 as [H253 H254].
destruct H254 as [H255 H256].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H257 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H257.
destruct __TmpHyp8 as [x39 H258].
destruct H258 as [x40 H259].
destruct H259 as [x41 H260].
destruct H260 as [x42 H261].
destruct H261 as [x43 H262].
destruct H262 as [H263 H264].
destruct H264 as [H265 H266].
destruct H266 as [H267 H268].
destruct H268 as [H269 H270].
destruct H270 as [H271 H272].
destruct H272 as [H273 H274].
destruct H274 as [H275 H276].
destruct H276 as [H277 H278].
destruct H278 as [H279 H280].
destruct H280 as [H281 H282].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H283 by exact H42.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp9 by exact H283.
destruct __TmpHyp9 as [x44 H284].
destruct H284 as [x45 H285].
destruct H285 as [x46 H286].
destruct H286 as [x47 H287].
destruct H287 as [x48 H288].
destruct H288 as [H289 H290].
destruct H290 as [H291 H292].
destruct H292 as [H293 H294].
destruct H294 as [H295 H296].
destruct H296 as [H297 H298].
destruct H298 as [H299 H300].
destruct H300 as [H301 H302].
destruct H302 as [H303 H304].
destruct H304 as [H305 H306].
destruct H306 as [H307 H308].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H309 by exact H41.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp10 by exact H309.
destruct __TmpHyp10 as [x49 H310].
destruct H310 as [x50 H311].
destruct H311 as [x51 H312].
destruct H312 as [x52 H313].
destruct H313 as [x53 H314].
destruct H314 as [H315 H316].
destruct H316 as [H317 H318].
destruct H318 as [H319 H320].
destruct H320 as [H321 H322].
destruct H322 as [H323 H324].
destruct H324 as [H325 H326].
destruct H326 as [H327 H328].
destruct H328 as [H329 H330].
destruct H330 as [H331 H332].
destruct H332 as [H333 H334].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H335 by exact H44.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp11 by exact H335.
destruct __TmpHyp11 as [x54 H336].
destruct H336 as [x55 H337].
destruct H337 as [x56 H338].
destruct H338 as [x57 H339].
destruct H339 as [x58 H340].
destruct H340 as [H341 H342].
destruct H342 as [H343 H344].
destruct H344 as [H345 H346].
destruct H346 as [H347 H348].
destruct H348 as [H349 H350].
destruct H350 as [H351 H352].
destruct H352 as [H353 H354].
destruct H354 as [H355 H356].
destruct H356 as [H357 H358].
destruct H358 as [H359 H360].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H361 by exact H43.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp12 by exact H361.
destruct __TmpHyp12 as [x59 H362].
destruct H362 as [x60 H363].
destruct H363 as [x61 H364].
destruct H364 as [x62 H365].
destruct H365 as [x63 H366].
destruct H366 as [H367 H368].
destruct H368 as [H369 H370].
destruct H370 as [H371 H372].
destruct H372 as [H373 H374].
destruct H374 as [H375 H376].
destruct H376 as [H377 H378].
destruct H378 as [H379 H380].
destruct H380 as [H381 H382].
destruct H382 as [H383 H384].
destruct H384 as [H385 H386].
exact H369.
---------------------------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H50.
----------------------------------------- exists C.
split.
------------------------------------------ exact H48.
------------------------------------------ split.
------------------------------------------- exact H49.
------------------------------------------- split.
-------------------------------------------- exact H45.
-------------------------------------------- exact H47.
----------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H51.
------------------------------------------ assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H51 by exact H24.
assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H51.
destruct __TmpHyp0 as [x H52].
destruct H52 as [x0 H53].
destruct H53 as [x1 H54].
destruct H54 as [x2 H55].
destruct H55 as [x3 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H77 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H77.
destruct __TmpHyp1 as [x4 H78].
destruct H78 as [x5 H79].
destruct H79 as [x6 H80].
destruct H80 as [x7 H81].
destruct H81 as [x8 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
assert (exists U V u v X, (euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col B E U) /\ ((euclidean__axioms.Col B E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B E F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H103 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col B E U) /\ ((euclidean__axioms.Col B E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B E F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H103.
destruct __TmpHyp2 as [x9 H104].
destruct H104 as [x10 H105].
destruct H105 as [x11 H106].
destruct H106 as [x12 H107].
destruct H107 as [x13 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
assert (exists U V u v X, (euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col D A U) /\ ((euclidean__axioms.Col D A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D A C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H129 by exact H20.
assert (exists U V u v X, (euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col D A U) /\ ((euclidean__axioms.Col D A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D A C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H129.
destruct __TmpHyp3 as [x14 H130].
destruct H130 as [x15 H131].
destruct H131 as [x16 H132].
destruct H132 as [x17 H133].
destruct H133 as [x18 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
assert (exists U V u v X, (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H155 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col D C U) /\ ((euclidean__axioms.Col D C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D C B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H155.
destruct __TmpHyp4 as [x19 H156].
destruct H156 as [x20 H157].
destruct H157 as [x21 H158].
destruct H158 as [x22 H159].
destruct H159 as [x23 H160].
destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
assert (exists U V u v X, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B A D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H181 by exact H18.
assert (exists U V u v X, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A U) /\ ((euclidean__axioms.Col B A V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B A D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H181.
destruct __TmpHyp5 as [x24 H182].
destruct H182 as [x25 H183].
destruct H183 as [x26 H184].
destruct H184 as [x27 H185].
destruct H185 as [x28 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
destruct H198 as [H199 H200].
destruct H200 as [H201 H202].
destruct H202 as [H203 H204].
destruct H204 as [H205 H206].
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H207 by exact H7.
assert (exists U V u v X, (euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col F C U) /\ ((euclidean__axioms.Col F C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F C E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H207.
destruct __TmpHyp6 as [x29 H208].
destruct H208 as [x30 H209].
destruct H209 as [x31 H210].
destruct H210 as [x32 H211].
destruct H211 as [x33 H212].
destruct H212 as [H213 H214].
destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
destruct H218 as [H219 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H233 by exact H6.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F C u) /\ ((euclidean__axioms.Col F C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B F C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H233.
destruct __TmpHyp7 as [x34 H234].
destruct H234 as [x35 H235].
destruct H235 as [x36 H236].
destruct H236 as [x37 H237].
destruct H237 as [x38 H238].
destruct H238 as [H239 H240].
destruct H240 as [H241 H242].
destruct H242 as [H243 H244].
destruct H244 as [H245 H246].
destruct H246 as [H247 H248].
destruct H248 as [H249 H250].
destruct H250 as [H251 H252].
destruct H252 as [H253 H254].
destruct H254 as [H255 H256].
destruct H256 as [H257 H258].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H259 by exact H5.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D C u) /\ ((euclidean__axioms.Col D C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B D C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H259.
destruct __TmpHyp8 as [x39 H260].
destruct H260 as [x40 H261].
destruct H261 as [x41 H262].
destruct H262 as [x42 H263].
destruct H263 as [x43 H264].
destruct H264 as [H265 H266].
destruct H266 as [H267 H268].
destruct H268 as [H269 H270].
destruct H270 as [H271 H272].
destruct H272 as [H273 H274].
destruct H274 as [H275 H276].
destruct H276 as [H277 H278].
destruct H278 as [H279 H280].
destruct H280 as [H281 H282].
destruct H282 as [H283 H284].
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H285 by exact H42.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp9 by exact H285.
destruct __TmpHyp9 as [x44 H286].
destruct H286 as [x45 H287].
destruct H287 as [x46 H288].
destruct H288 as [x47 H289].
destruct H289 as [x48 H290].
destruct H290 as [H291 H292].
destruct H292 as [H293 H294].
destruct H294 as [H295 H296].
destruct H296 as [H297 H298].
destruct H298 as [H299 H300].
destruct H300 as [H301 H302].
destruct H302 as [H303 H304].
destruct H304 as [H305 H306].
destruct H306 as [H307 H308].
destruct H308 as [H309 H310].
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H311 by exact H41.
assert (exists U V u v X, (euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C F u) /\ ((euclidean__axioms.Col C F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E B C F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp10 by exact H311.
destruct __TmpHyp10 as [x49 H312].
destruct H312 as [x50 H313].
destruct H313 as [x51 H314].
destruct H314 as [x52 H315].
destruct H315 as [x53 H316].
destruct H316 as [H317 H318].
destruct H318 as [H319 H320].
destruct H320 as [H321 H322].
destruct H322 as [H323 H324].
destruct H324 as [H325 H326].
destruct H326 as [H327 H328].
destruct H328 as [H329 H330].
destruct H330 as [H331 H332].
destruct H332 as [H333 H334].
destruct H334 as [H335 H336].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H337 by exact H44.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp11 by exact H337.
destruct __TmpHyp11 as [x54 H338].
destruct H338 as [x55 H339].
destruct H339 as [x56 H340].
destruct H340 as [x57 H341].
destruct H341 as [x58 H342].
destruct H342 as [H343 H344].
destruct H344 as [H345 H346].
destruct H346 as [H347 H348].
destruct H348 as [H349 H350].
destruct H350 as [H351 H352].
destruct H352 as [H353 H354].
destruct H354 as [H355 H356].
destruct H356 as [H357 H358].
destruct H358 as [H359 H360].
destruct H360 as [H361 H362].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H363 by exact H43.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp12 by exact H363.
destruct __TmpHyp12 as [x59 H364].
destruct H364 as [x60 H365].
destruct H365 as [x61 H366].
destruct H366 as [x62 H367].
destruct H367 as [x63 H368].
destruct H368 as [H369 H370].
destruct H370 as [H371 H372].
destruct H372 as [H373 H374].
destruct H374 as [H375 H376].
destruct H376 as [H377 H378].
destruct H378 as [H379 H380].
destruct H380 as [H381 H382].
destruct H382 as [H383 H384].
destruct H384 as [H385 H386].
destruct H386 as [H387 H388].
exact H385.
------------------------------------------ apply (@H51 H50).
------------------------------------ assert (* Cut *) (euclidean__axioms.EF A B C D A B C D) as H46.
------------------------------------- apply (@lemma__EFreflexive.lemma__EFreflexive A B C D M H39 H40).
--------------------------------------apply (@euclidean__tactics.nCol__notCol A B C H45).

------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E B C D) as H47.
-------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun D0 => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.Col A D0 E) -> ((euclidean__axioms.Col A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.neq A D0) -> ((euclidean__axioms.neq D0 A) -> ((~(euclidean__axioms.EF A B C D0 E B C F)) -> ((~(euclidean__axioms.BetS A D0 F)) -> ((~(euclidean__axioms.BetS A D0 E)) -> ((euclidean__defs.Par B A D0 C) -> ((euclidean__defs.Par D0 C B A) -> ((euclidean__defs.Par D0 A C B) -> ((euclidean__defs.PG D0 C B A) -> ((~(euclidean__axioms.BetS E A D0)) -> ((~(euclidean__axioms.BetS D0 A F)) -> (((A = D0) \/ ((A = F) \/ ((D0 = F) \/ ((euclidean__axioms.BetS D0 A F) \/ ((euclidean__axioms.BetS A D0 F) \/ (euclidean__axioms.BetS A F D0)))))) -> (((A = D0) \/ ((A = E) \/ ((D0 = E) \/ ((euclidean__axioms.BetS D0 A E) \/ ((euclidean__axioms.BetS A D0 E) \/ (euclidean__axioms.BetS A E D0)))))) -> ((D0 = F) -> ((euclidean__axioms.BetS B M D0) -> ((euclidean__axioms.EF A B C D0 A B C D0) -> (euclidean__axioms.EF A B C D0 E B C D0)))))))))))))))))))))))))) with (x := D).
---------------------------------------intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
apply (@eq__ind__r euclidean__axioms.Point E (fun A0 => (euclidean__defs.PG A0 B C F) -> ((euclidean__defs.Par A0 F B C) -> ((euclidean__defs.Par A0 B C F) -> ((euclidean__axioms.Col A0 F F) -> ((euclidean__axioms.Col A0 F E) -> ((euclidean__defs.Par A0 B F C) -> ((euclidean__axioms.Cong A0 F B C) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.Cong A0 F E F) -> ((euclidean__defs.PG F C B A0) -> ((euclidean__defs.Par F A0 C B) -> ((euclidean__defs.Par F C B A0) -> ((euclidean__defs.Par B A0 F C) -> ((~(euclidean__axioms.BetS A0 F E)) -> ((~(euclidean__axioms.BetS A0 F F)) -> ((~(euclidean__axioms.EF A0 B C F E B C F)) -> ((euclidean__axioms.neq F A0) -> (((A0 = F) \/ ((A0 = E) \/ ((F = E) \/ ((euclidean__axioms.BetS F A0 E) \/ ((euclidean__axioms.BetS A0 F E) \/ (euclidean__axioms.BetS A0 E F)))))) -> (((A0 = F) \/ ((A0 = F) \/ ((F = F) \/ ((euclidean__axioms.BetS F A0 F) \/ ((euclidean__axioms.BetS A0 F F) \/ (euclidean__axioms.BetS A0 F F)))))) -> ((~(euclidean__axioms.BetS F A0 F)) -> ((~(euclidean__axioms.BetS E A0 F)) -> ((~(A0 = F)) -> ((euclidean__axioms.BetS A0 M C) -> ((~(euclidean__axioms.Col A0 B C)) -> ((euclidean__axioms.EF A0 B C F A0 B C F) -> ((F = F) -> (euclidean__axioms.EF A0 B C F E B C F)))))))))))))))))))))))))))) with (x := A).
----------------------------------------intro H71.
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
exact H95.

---------------------------------------- exact H35.
---------------------------------------- exact H47.
---------------------------------------- exact H51.
---------------------------------------- exact H50.
---------------------------------------- exact H49.
---------------------------------------- exact H48.
---------------------------------------- exact H52.
---------------------------------------- exact H53.
---------------------------------------- exact H55.
---------------------------------------- exact H54.
---------------------------------------- exact H63.
---------------------------------------- exact H62.
---------------------------------------- exact H61.
---------------------------------------- exact H60.
---------------------------------------- exact H59.
---------------------------------------- exact H58.
---------------------------------------- exact H57.
---------------------------------------- exact H56.
---------------------------------------- exact H67.
---------------------------------------- exact H66.
---------------------------------------- exact H65.
---------------------------------------- exact H64.
---------------------------------------- exact H30.
---------------------------------------- exact H39.
---------------------------------------- exact H45.
---------------------------------------- exact H70.
---------------------------------------- exact H68.

--------------------------------------- exact H31.
--------------------------------------- exact H.
--------------------------------------- exact H1.
--------------------------------------- exact H2.
--------------------------------------- exact H43.
--------------------------------------- exact H44.
--------------------------------------- exact H5.
--------------------------------------- exact H8.
--------------------------------------- exact H11.
--------------------------------------- exact H12.
--------------------------------------- exact H14.
--------------------------------------- exact H15.
--------------------------------------- exact H16.
--------------------------------------- exact H17.
--------------------------------------- exact H18.
--------------------------------------- exact H19.
--------------------------------------- exact H20.
--------------------------------------- exact H21.
--------------------------------------- exact H26.
--------------------------------------- exact H27.
--------------------------------------- exact H28.
--------------------------------------- exact H29.
--------------------------------------- exact H36.
--------------------------------------- exact H40.
--------------------------------------- exact H46.
-------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E B C F) as H48.
--------------------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun D0 => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.Col A D0 E) -> ((euclidean__axioms.Col A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.neq A D0) -> ((euclidean__axioms.neq D0 A) -> ((~(euclidean__axioms.EF A B C D0 E B C F)) -> ((~(euclidean__axioms.BetS A D0 F)) -> ((~(euclidean__axioms.BetS A D0 E)) -> ((euclidean__defs.Par B A D0 C) -> ((euclidean__defs.Par D0 C B A) -> ((euclidean__defs.Par D0 A C B) -> ((euclidean__defs.PG D0 C B A) -> ((~(euclidean__axioms.BetS E A D0)) -> ((~(euclidean__axioms.BetS D0 A F)) -> (((A = D0) \/ ((A = F) \/ ((D0 = F) \/ ((euclidean__axioms.BetS D0 A F) \/ ((euclidean__axioms.BetS A D0 F) \/ (euclidean__axioms.BetS A F D0)))))) -> (((A = D0) \/ ((A = E) \/ ((D0 = E) \/ ((euclidean__axioms.BetS D0 A E) \/ ((euclidean__axioms.BetS A D0 E) \/ (euclidean__axioms.BetS A E D0)))))) -> ((D0 = F) -> ((euclidean__axioms.BetS B M D0) -> ((euclidean__axioms.EF A B C D0 A B C D0) -> ((euclidean__axioms.EF A B C D0 E B C D0) -> (euclidean__axioms.EF A B C D0 E B C F))))))))))))))))))))))))))) with (x := D).
----------------------------------------intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
apply (@eq__ind__r euclidean__axioms.Point E (fun A0 => (euclidean__defs.PG A0 B C F) -> ((euclidean__defs.Par A0 F B C) -> ((euclidean__defs.Par A0 B C F) -> ((euclidean__axioms.Col A0 F F) -> ((euclidean__axioms.Col A0 F E) -> ((euclidean__defs.Par A0 B F C) -> ((euclidean__axioms.Cong A0 F B C) -> ((euclidean__axioms.neq A0 F) -> ((euclidean__axioms.Cong A0 F E F) -> ((euclidean__defs.PG F C B A0) -> ((euclidean__defs.Par F A0 C B) -> ((euclidean__defs.Par F C B A0) -> ((euclidean__defs.Par B A0 F C) -> ((~(euclidean__axioms.BetS A0 F E)) -> ((~(euclidean__axioms.BetS A0 F F)) -> ((~(euclidean__axioms.EF A0 B C F E B C F)) -> ((euclidean__axioms.neq F A0) -> (((A0 = F) \/ ((A0 = E) \/ ((F = E) \/ ((euclidean__axioms.BetS F A0 E) \/ ((euclidean__axioms.BetS A0 F E) \/ (euclidean__axioms.BetS A0 E F)))))) -> (((A0 = F) \/ ((A0 = F) \/ ((F = F) \/ ((euclidean__axioms.BetS F A0 F) \/ ((euclidean__axioms.BetS A0 F F) \/ (euclidean__axioms.BetS A0 F F)))))) -> ((~(euclidean__axioms.BetS F A0 F)) -> ((~(euclidean__axioms.BetS E A0 F)) -> ((~(A0 = F)) -> ((euclidean__axioms.BetS A0 M C) -> ((~(euclidean__axioms.Col A0 B C)) -> ((euclidean__axioms.EF A0 B C F E B C F) -> ((euclidean__axioms.EF A0 B C F A0 B C F) -> ((F = F) -> (euclidean__axioms.EF A0 B C F E B C F))))))))))))))))))))))))))))) with (x := A).
-----------------------------------------intro H73.
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
exact H97.

----------------------------------------- exact H35.
----------------------------------------- exact H48.
----------------------------------------- exact H52.
----------------------------------------- exact H51.
----------------------------------------- exact H50.
----------------------------------------- exact H49.
----------------------------------------- exact H53.
----------------------------------------- exact H54.
----------------------------------------- exact H56.
----------------------------------------- exact H55.
----------------------------------------- exact H64.
----------------------------------------- exact H63.
----------------------------------------- exact H62.
----------------------------------------- exact H61.
----------------------------------------- exact H60.
----------------------------------------- exact H59.
----------------------------------------- exact H58.
----------------------------------------- exact H57.
----------------------------------------- exact H68.
----------------------------------------- exact H67.
----------------------------------------- exact H66.
----------------------------------------- exact H65.
----------------------------------------- exact H30.
----------------------------------------- exact H39.
----------------------------------------- exact H45.
----------------------------------------- exact H72.
----------------------------------------- exact H71.
----------------------------------------- exact H69.

---------------------------------------- exact H31.
---------------------------------------- exact H.
---------------------------------------- exact H1.
---------------------------------------- exact H2.
---------------------------------------- exact H43.
---------------------------------------- exact H44.
---------------------------------------- exact H5.
---------------------------------------- exact H8.
---------------------------------------- exact H11.
---------------------------------------- exact H12.
---------------------------------------- exact H14.
---------------------------------------- exact H15.
---------------------------------------- exact H16.
---------------------------------------- exact H17.
---------------------------------------- exact H18.
---------------------------------------- exact H19.
---------------------------------------- exact H20.
---------------------------------------- exact H21.
---------------------------------------- exact H26.
---------------------------------------- exact H27.
---------------------------------------- exact H28.
---------------------------------------- exact H29.
---------------------------------------- exact H36.
---------------------------------------- exact H40.
---------------------------------------- exact H46.
---------------------------------------- exact H47.
--------------------------------------- apply (@H15 H48).
---------------------------------- exact H36.
--------------------------------- destruct H35 as [H36|H36].
---------------------------------- assert (* Cut *) (~(D = F)) as H37.
----------------------------------- intro H37.
assert (* Cut *) (F = E) as H38.
------------------------------------ destruct H4 as [H38 H39].
destruct H3 as [H40 H41].
apply (@eq__ind__r euclidean__axioms.Point F (fun D0 => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.Col A D0 E) -> ((euclidean__axioms.Col A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.neq A D0) -> ((euclidean__axioms.neq D0 A) -> ((~(euclidean__axioms.EF A B C D0 E B C F)) -> ((~(euclidean__axioms.BetS A D0 F)) -> ((~(euclidean__axioms.BetS A D0 E)) -> ((euclidean__defs.Par B A D0 C) -> ((euclidean__defs.Par D0 C B A) -> ((euclidean__defs.Par D0 A C B) -> ((euclidean__defs.PG D0 C B A) -> ((~(euclidean__axioms.BetS E A D0)) -> ((~(euclidean__axioms.BetS D0 A F)) -> (((A = D0) \/ ((A = F) \/ ((D0 = F) \/ ((euclidean__axioms.BetS D0 A F) \/ ((euclidean__axioms.BetS A D0 F) \/ (euclidean__axioms.BetS A F D0)))))) -> (((A = D0) \/ ((A = E) \/ ((D0 = E) \/ ((euclidean__axioms.BetS D0 A E) \/ ((euclidean__axioms.BetS A D0 E) \/ (euclidean__axioms.BetS A E D0)))))) -> ((D0 = F) -> (F = E)))))))))))))))))))))))) with (x := D).
-------------------------------------intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
apply (@eq__ind__r euclidean__axioms.Point E (fun F0 => (euclidean__defs.PG A B C F0) -> ((euclidean__defs.PG E B C F0) -> ((euclidean__defs.Par A F0 B C) -> ((euclidean__defs.Par A B C F0) -> ((euclidean__axioms.Col A F0 F0) -> ((euclidean__axioms.Col A F0 E) -> ((euclidean__defs.Par E B C F0) -> ((euclidean__defs.Par E F0 B C) -> ((euclidean__defs.Par A B F0 C) -> ((euclidean__defs.Par E B F0 C) -> ((euclidean__defs.Par F0 C E B) -> ((euclidean__axioms.Cong A F0 B C) -> ((euclidean__axioms.Cong E F0 B C) -> ((euclidean__axioms.Cong B C E F0) -> ((euclidean__axioms.neq A F0) -> ((euclidean__axioms.Cong A F0 E F0) -> ((euclidean__axioms.neq E F0) -> ((euclidean__defs.PG F0 C B A) -> ((euclidean__defs.Par F0 A C B) -> ((euclidean__defs.Par F0 C B A) -> ((euclidean__defs.Par B A F0 C) -> ((~(euclidean__axioms.BetS A F0 E)) -> ((~(euclidean__axioms.BetS A F0 F0)) -> ((~(euclidean__axioms.EF A B C F0 E B C F0)) -> ((euclidean__axioms.neq F0 A) -> ((euclidean__defs.Par B E F0 C) -> ((euclidean__defs.Par F0 C B E) -> ((euclidean__defs.Par F0 E C B) -> ((euclidean__defs.PG F0 C B E) -> (((A = F0) \/ ((A = E) \/ ((F0 = E) \/ ((euclidean__axioms.BetS F0 A E) \/ ((euclidean__axioms.BetS A F0 E) \/ (euclidean__axioms.BetS A E F0)))))) -> (((A = F0) \/ ((A = F0) \/ ((F0 = F0) \/ ((euclidean__axioms.BetS F0 A F0) \/ ((euclidean__axioms.BetS A F0 F0) \/ (euclidean__axioms.BetS A F0 F0)))))) -> ((~(euclidean__axioms.BetS F0 A F0)) -> ((~(euclidean__axioms.BetS E A F0)) -> ((~(A = F0)) -> ((F0 = F0) -> (F0 = E))))))))))))))))))))))))))))))))))))) with (x := F).
--------------------------------------intro H64.
intro H65.
intro H66.
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
exact H98.

-------------------------------------- exact H36.
-------------------------------------- exact H42.
-------------------------------------- exact H0.
-------------------------------------- exact H46.
-------------------------------------- exact H45.
-------------------------------------- exact H44.
-------------------------------------- exact H43.
-------------------------------------- exact H38.
-------------------------------------- exact H39.
-------------------------------------- exact H47.
-------------------------------------- exact H6.
-------------------------------------- exact H7.
-------------------------------------- exact H48.
-------------------------------------- exact H9.
-------------------------------------- exact H10.
-------------------------------------- exact H50.
-------------------------------------- exact H49.
-------------------------------------- exact H13.
-------------------------------------- exact H58.
-------------------------------------- exact H57.
-------------------------------------- exact H56.
-------------------------------------- exact H55.
-------------------------------------- exact H54.
-------------------------------------- exact H53.
-------------------------------------- exact H52.
-------------------------------------- exact H51.
-------------------------------------- exact H22.
-------------------------------------- exact H23.
-------------------------------------- exact H24.
-------------------------------------- exact H25.
-------------------------------------- exact H62.
-------------------------------------- exact H61.
-------------------------------------- exact H60.
-------------------------------------- exact H59.
-------------------------------------- exact H30.
-------------------------------------- exact H63.

------------------------------------- exact H31.
------------------------------------- exact H.
------------------------------------- exact H1.
------------------------------------- exact H2.
------------------------------------- exact H40.
------------------------------------- exact H41.
------------------------------------- exact H5.
------------------------------------- exact H8.
------------------------------------- exact H11.
------------------------------------- exact H12.
------------------------------------- exact H14.
------------------------------------- exact H15.
------------------------------------- exact H16.
------------------------------------- exact H17.
------------------------------------- exact H18.
------------------------------------- exact H19.
------------------------------------- exact H20.
------------------------------------- exact H21.
------------------------------------- exact H26.
------------------------------------- exact H27.
------------------------------------- exact H28.
------------------------------------- exact H29.
------------------------------------- exact H37.
------------------------------------ assert (* Cut *) (E = F) as H39.
------------------------------------- destruct H4 as [H39 H40].
destruct H3 as [H41 H42].
apply (@eq__ind euclidean__axioms.Point D (fun F0 => (euclidean__defs.PG E B C F0) -> ((euclidean__axioms.Col A D F0) -> ((euclidean__defs.Par E B C F0) -> ((euclidean__defs.Par E F0 B C) -> ((euclidean__defs.Par E B F0 C) -> ((euclidean__defs.Par F0 C E B) -> ((euclidean__axioms.Cong E F0 B C) -> ((euclidean__axioms.Cong B C E F0) -> ((euclidean__axioms.Cong A D E F0) -> ((euclidean__axioms.neq E F0) -> ((~(euclidean__axioms.EF A B C D E B C F0)) -> ((~(euclidean__axioms.BetS A D F0)) -> ((euclidean__defs.Par B E F0 C) -> ((euclidean__defs.Par F0 C B E) -> ((euclidean__defs.Par F0 E C B) -> ((euclidean__defs.PG F0 C B E) -> ((~(euclidean__axioms.BetS D A F0)) -> (((A = D) \/ ((A = F0) \/ ((D = F0) \/ ((euclidean__axioms.BetS D A F0) \/ ((euclidean__axioms.BetS A D F0) \/ (euclidean__axioms.BetS A F0 D)))))) -> ((~(A = F0)) -> ((F0 = E) -> ((D = F0) -> ((F0 = E) -> (E = F0)))))))))))))))))))))))) with (y := F).
--------------------------------------intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
apply (@eq__ind__r euclidean__axioms.Point E (fun D0 => (euclidean__defs.PG A B C D0) -> ((euclidean__defs.PG E B C D0) -> ((euclidean__axioms.Col A D0 E) -> ((euclidean__axioms.Col A D0 D0) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par E D0 B C) -> ((euclidean__defs.Par E B C D0) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__defs.Par D0 C E B) -> ((euclidean__defs.Par E B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E D0) -> ((euclidean__axioms.Cong B C E D0) -> ((euclidean__axioms.Cong E D0 B C) -> ((euclidean__axioms.neq A D0) -> ((euclidean__axioms.neq E D0) -> ((euclidean__axioms.neq D0 A) -> ((~(euclidean__axioms.BetS A D0 D0)) -> ((~(euclidean__axioms.EF A B C D0 E B C D0)) -> ((~(euclidean__axioms.BetS A D0 E)) -> ((euclidean__defs.Par B A D0 C) -> ((euclidean__defs.Par D0 C B A) -> ((euclidean__defs.Par D0 A C B) -> ((euclidean__defs.PG D0 C B A) -> ((euclidean__defs.PG D0 C B E) -> ((euclidean__defs.Par D0 E C B) -> ((euclidean__defs.Par D0 C B E) -> ((euclidean__defs.Par B E D0 C) -> ((~(euclidean__axioms.BetS E A D0)) -> (((A = D0) \/ ((A = D0) \/ ((D0 = D0) \/ ((euclidean__axioms.BetS D0 A D0) \/ ((euclidean__axioms.BetS A D0 D0) \/ (euclidean__axioms.BetS A D0 D0)))))) -> ((~(euclidean__axioms.BetS D0 A D0)) -> (((A = D0) \/ ((A = E) \/ ((D0 = E) \/ ((euclidean__axioms.BetS D0 A E) \/ ((euclidean__axioms.BetS A D0 E) \/ (euclidean__axioms.BetS A E D0)))))) -> ((~(A = D0)) -> ((D0 = D0) -> ((D0 = E) -> (E = D0)))))))))))))))))))))))))))))))))))))) with (x := D).
---------------------------------------intro H65.
intro H66.
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
exact H100.

--------------------------------------- exact H62.
--------------------------------------- exact H.
--------------------------------------- exact H43.
--------------------------------------- exact H1.
--------------------------------------- exact H44.
--------------------------------------- exact H41.
--------------------------------------- exact H42.
--------------------------------------- exact H46.
--------------------------------------- exact H45.
--------------------------------------- exact H5.
--------------------------------------- exact H48.
--------------------------------------- exact H47.
--------------------------------------- exact H8.
--------------------------------------- exact H51.
--------------------------------------- exact H50.
--------------------------------------- exact H49.
--------------------------------------- exact H12.
--------------------------------------- exact H52.
--------------------------------------- exact H14.
--------------------------------------- exact H54.
--------------------------------------- exact H53.
--------------------------------------- exact H17.
--------------------------------------- exact H18.
--------------------------------------- exact H19.
--------------------------------------- exact H20.
--------------------------------------- exact H21.
--------------------------------------- exact H58.
--------------------------------------- exact H57.
--------------------------------------- exact H56.
--------------------------------------- exact H55.
--------------------------------------- exact H26.
--------------------------------------- exact H60.
--------------------------------------- exact H59.
--------------------------------------- exact H29.
--------------------------------------- exact H61.
--------------------------------------- exact H63.
--------------------------------------- exact H64.

-------------------------------------- exact H31.
-------------------------------------- exact H0.
-------------------------------------- exact H2.
-------------------------------------- exact H39.
-------------------------------------- exact H40.
-------------------------------------- exact H6.
-------------------------------------- exact H7.
-------------------------------------- exact H9.
-------------------------------------- exact H10.
-------------------------------------- exact H11.
-------------------------------------- exact H13.
-------------------------------------- exact H15.
-------------------------------------- exact H16.
-------------------------------------- exact H22.
-------------------------------------- exact H23.
-------------------------------------- exact H24.
-------------------------------------- exact H25.
-------------------------------------- exact H27.
-------------------------------------- exact H28.
-------------------------------------- exact H30.
-------------------------------------- exact H36.
-------------------------------------- exact H37.
-------------------------------------- exact H38.
------------------------------------- apply (@H13 H39).
----------------------------------- exact H37.
---------------------------------- destruct H36 as [H37|H37].
----------------------------------- assert (* Cut *) (~(D = F)) as H38.
------------------------------------ intro H38.
assert (* Cut *) (euclidean__axioms.BetS E A D) as H39.
------------------------------------- destruct H4 as [H39 H40].
destruct H3 as [H41 H42].
apply (@euclidean__axioms.axiom__betweennesssymmetry D A E H37).
------------------------------------- apply (@H26 H39).
------------------------------------ exact H38.
----------------------------------- destruct H37 as [H38|H38].
------------------------------------ assert (* Cut *) (~(D = F)) as H39.
------------------------------------- intro H39.
apply (@H17 H38).
------------------------------------- exact H39.
------------------------------------ assert (* Cut *) (~(D = F)) as H39.
------------------------------------- intro H39.
assert (* Cut *) (euclidean__axioms.BetS D E A) as H40.
-------------------------------------- destruct H4 as [H40 H41].
destruct H3 as [H42 H43].
apply (@euclidean__axioms.axiom__betweennesssymmetry A E D H38).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D E D E) as H41.
--------------------------------------- destruct H4 as [H41 H42].
destruct H3 as [H43 H44].
apply (@euclidean__axioms.cn__congruencereflexive D E).
--------------------------------------- assert (* Cut *) (euclidean__defs.Lt D E D A) as H42.
---------------------------------------- exists E.
split.
----------------------------------------- exact H40.
----------------------------------------- exact H41.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D E F E) as H43.
----------------------------------------- destruct H4 as [H43 H44].
destruct H3 as [H45 H46].
apply (@eq__ind__r euclidean__axioms.Point F (fun D0 => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.Col A D0 E) -> ((euclidean__axioms.Col A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.neq A D0) -> ((euclidean__axioms.neq D0 A) -> ((~(euclidean__axioms.EF A B C D0 E B C F)) -> ((~(euclidean__axioms.BetS A D0 F)) -> ((~(euclidean__axioms.BetS A D0 E)) -> ((euclidean__defs.Par B A D0 C) -> ((euclidean__defs.Par D0 C B A) -> ((euclidean__defs.Par D0 A C B) -> ((euclidean__defs.PG D0 C B A) -> ((~(euclidean__axioms.BetS E A D0)) -> ((~(euclidean__axioms.BetS D0 A F)) -> (((A = D0) \/ ((A = F) \/ ((D0 = F) \/ ((euclidean__axioms.BetS D0 A F) \/ ((euclidean__axioms.BetS A D0 F) \/ (euclidean__axioms.BetS A F D0)))))) -> (((A = D0) \/ ((A = E) \/ ((D0 = E) \/ ((euclidean__axioms.BetS D0 A E) \/ ((euclidean__axioms.BetS A D0 E) \/ (euclidean__axioms.BetS A E D0)))))) -> ((euclidean__axioms.BetS A E D0) -> ((D0 = F) -> ((euclidean__axioms.BetS D0 E A) -> ((euclidean__axioms.Cong D0 E D0 E) -> ((euclidean__defs.Lt D0 E D0 A) -> (euclidean__axioms.Cong D0 E F E)))))))))))))))))))))))))))) with (x := D).
------------------------------------------intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
assert (F = F) as H73 by exact H69.
exact H71.

------------------------------------------ exact H31.
------------------------------------------ exact H.
------------------------------------------ exact H1.
------------------------------------------ exact H2.
------------------------------------------ exact H45.
------------------------------------------ exact H46.
------------------------------------------ exact H5.
------------------------------------------ exact H8.
------------------------------------------ exact H11.
------------------------------------------ exact H12.
------------------------------------------ exact H14.
------------------------------------------ exact H15.
------------------------------------------ exact H16.
------------------------------------------ exact H17.
------------------------------------------ exact H18.
------------------------------------------ exact H19.
------------------------------------------ exact H20.
------------------------------------------ exact H21.
------------------------------------------ exact H26.
------------------------------------------ exact H27.
------------------------------------------ exact H28.
------------------------------------------ exact H29.
------------------------------------------ exact H38.
------------------------------------------ exact H39.
------------------------------------------ exact H40.
------------------------------------------ exact H41.
------------------------------------------ exact H42.
----------------------------------------- assert (* Cut *) (euclidean__defs.Lt F E D A) as H44.
------------------------------------------ destruct H4 as [H44 H45].
destruct H3 as [H46 H47].
apply (@eq__ind__r euclidean__axioms.Point F (fun D0 => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.Col A D0 E) -> ((euclidean__axioms.Col A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.neq A D0) -> ((euclidean__axioms.neq D0 A) -> ((~(euclidean__axioms.EF A B C D0 E B C F)) -> ((~(euclidean__axioms.BetS A D0 F)) -> ((~(euclidean__axioms.BetS A D0 E)) -> ((euclidean__defs.Par B A D0 C) -> ((euclidean__defs.Par D0 C B A) -> ((euclidean__defs.Par D0 A C B) -> ((euclidean__defs.PG D0 C B A) -> ((~(euclidean__axioms.BetS E A D0)) -> ((~(euclidean__axioms.BetS D0 A F)) -> (((A = D0) \/ ((A = F) \/ ((D0 = F) \/ ((euclidean__axioms.BetS D0 A F) \/ ((euclidean__axioms.BetS A D0 F) \/ (euclidean__axioms.BetS A F D0)))))) -> (((A = D0) \/ ((A = E) \/ ((D0 = E) \/ ((euclidean__axioms.BetS D0 A E) \/ ((euclidean__axioms.BetS A D0 E) \/ (euclidean__axioms.BetS A E D0)))))) -> ((euclidean__axioms.BetS A E D0) -> ((D0 = F) -> ((euclidean__axioms.BetS D0 E A) -> ((euclidean__axioms.Cong D0 E D0 E) -> ((euclidean__defs.Lt D0 E D0 A) -> ((euclidean__axioms.Cong D0 E F E) -> (euclidean__defs.Lt F E D0 A))))))))))))))))))))))))))))) with (x := D).
-------------------------------------------intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
assert (F = F) as H75 by exact H70.
exact H73.

------------------------------------------- exact H31.
------------------------------------------- exact H.
------------------------------------------- exact H1.
------------------------------------------- exact H2.
------------------------------------------- exact H46.
------------------------------------------- exact H47.
------------------------------------------- exact H5.
------------------------------------------- exact H8.
------------------------------------------- exact H11.
------------------------------------------- exact H12.
------------------------------------------- exact H14.
------------------------------------------- exact H15.
------------------------------------------- exact H16.
------------------------------------------- exact H17.
------------------------------------------- exact H18.
------------------------------------------- exact H19.
------------------------------------------- exact H20.
------------------------------------------- exact H21.
------------------------------------------- exact H26.
------------------------------------------- exact H27.
------------------------------------------- exact H28.
------------------------------------------- exact H29.
------------------------------------------- exact H38.
------------------------------------------- exact H39.
------------------------------------------- exact H40.
------------------------------------------- exact H41.
------------------------------------------- exact H42.
------------------------------------------- exact H43.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong F E E F) as H45.
------------------------------------------- destruct H4 as [H45 H46].
destruct H3 as [H47 H48].
apply (@euclidean__axioms.cn__equalityreverse F E).
------------------------------------------- assert (* Cut *) (euclidean__defs.Lt E F D A) as H46.
-------------------------------------------- destruct H4 as [H46 H47].
destruct H3 as [H48 H49].
apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 F E D A E F H44 H45).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D A A D) as H47.
--------------------------------------------- destruct H4 as [H47 H48].
destruct H3 as [H49 H50].
apply (@euclidean__axioms.cn__equalityreverse D A).
--------------------------------------------- assert (* Cut *) (euclidean__defs.Lt E F A D) as H48.
---------------------------------------------- destruct H4 as [H48 H49].
destruct H3 as [H50 H51].
apply (@lemma__lessthancongruence.lemma__lessthancongruence E F D A A D H46 H47).
---------------------------------------------- assert (* Cut *) (euclidean__defs.Lt E F E F) as H49.
----------------------------------------------- destruct H4 as [H49 H50].
destruct H3 as [H51 H52].
apply (@lemma__lessthancongruence.lemma__lessthancongruence E F A D E F H48 H11).
----------------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt E F E F)) as H50.
------------------------------------------------ destruct H4 as [H50 H51].
destruct H3 as [H52 H53].
apply (@lemma__trichotomy2.lemma__trichotomy2 E F E F H49).
------------------------------------------------ apply (@H50 H49).
------------------------------------- exact H39.
------------------------------- apply (@H33 H31).
----------------------------- assert (* Cut *) (euclidean__axioms.BetS A F D) as H32.
------------------------------ assert ((A = D) \/ ((A = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D A F) \/ ((euclidean__axioms.BetS A D F) \/ (euclidean__axioms.BetS A F D)))))) as H32 by exact H28.
assert ((A = D) \/ ((A = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D A F) \/ ((euclidean__axioms.BetS A D F) \/ (euclidean__axioms.BetS A F D)))))) as __TmpHyp by exact H32.
destruct __TmpHyp as [H33|H33].
------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A F D))) as H34.
-------------------------------- intro H34.
apply (@H12 H33).
-------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A F D)).
---------------------------------intro H35.
destruct H3 as [H36 H37].
destruct H4 as [H38 H39].
destruct H29 as [H40|H40].
---------------------------------- assert (* Cut *) (False) as H41.
----------------------------------- apply (@H12 H33).
----------------------------------- assert (* Cut *) (False) as H42.
------------------------------------ apply (@H34 H35).
------------------------------------ contradiction H42.
---------------------------------- destruct H40 as [H41|H41].
----------------------------------- assert (* Cut *) (False) as H42.
------------------------------------ apply (@H12 H33).
------------------------------------ assert (* Cut *) (False) as H43.
------------------------------------- apply (@H34 H35).
------------------------------------- contradiction H43.
----------------------------------- destruct H41 as [H42|H42].
------------------------------------ assert (* Cut *) (False) as H43.
------------------------------------- apply (@H12 H33).
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H34 H35).
-------------------------------------- contradiction H44.
------------------------------------ destruct H42 as [H43|H43].
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H12 H33).
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H34 H35).
--------------------------------------- contradiction H45.
------------------------------------- destruct H43 as [H44|H44].
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H12 H33).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H34 H35).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H17 H44).
----------------------------------------- contradiction H47.
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H12 H33).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H34 H35).
---------------------------------------- contradiction H46.

------------------------------- destruct H33 as [H34|H34].
-------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A F D))) as H35.
--------------------------------- intro H35.
apply (@H30 H34).
--------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A F D)).
----------------------------------intro H36.
destruct H3 as [H37 H38].
destruct H4 as [H39 H40].
destruct H29 as [H41|H41].
----------------------------------- assert (* Cut *) (False) as H42.
------------------------------------ apply (@H30 H34).
------------------------------------ assert (* Cut *) (False) as H43.
------------------------------------- apply (@H35 H36).
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H12 H41).
-------------------------------------- contradiction H44.
----------------------------------- destruct H41 as [H42|H42].
------------------------------------ assert (* Cut *) (False) as H43.
------------------------------------- apply (@H30 H34).
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H35 H36).
-------------------------------------- contradiction H44.
------------------------------------ destruct H42 as [H43|H43].
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H30 H34).
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H35 H36).
--------------------------------------- contradiction H45.
------------------------------------- destruct H43 as [H44|H44].
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H30 H34).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H35 H36).
---------------------------------------- contradiction H46.
-------------------------------------- destruct H44 as [H45|H45].
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H30 H34).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H35 H36).
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H17 H45).
------------------------------------------ contradiction H48.
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H30 H34).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H35 H36).
----------------------------------------- contradiction H47.

-------------------------------- destruct H34 as [H35|H35].
--------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A F D))) as H36.
---------------------------------- intro H36.
apply (@H31 H35).
---------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A F D)).
-----------------------------------intro H37.
destruct H3 as [H38 H39].
destruct H4 as [H40 H41].
destruct H29 as [H42|H42].
------------------------------------ assert (* Cut *) (False) as H43.
------------------------------------- apply (@H31 H35).
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H36 H37).
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H12 H42).
--------------------------------------- contradiction H45.
------------------------------------ destruct H42 as [H43|H43].
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H31 H35).
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H36 H37).
--------------------------------------- contradiction H45.
------------------------------------- destruct H43 as [H44|H44].
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H31 H35).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H36 H37).
---------------------------------------- contradiction H46.
-------------------------------------- destruct H44 as [H45|H45].
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H31 H35).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H36 H37).
----------------------------------------- contradiction H47.
--------------------------------------- destruct H45 as [H46|H46].
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H31 H35).
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H36 H37).
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H17 H46).
------------------------------------------- contradiction H49.
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H31 H35).
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H36 H37).
------------------------------------------ contradiction H48.

--------------------------------- destruct H35 as [H36|H36].
---------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A F D))) as H37.
----------------------------------- intro H37.
apply (@H27 H36).
----------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A F D)).
------------------------------------intro H38.
destruct H3 as [H39 H40].
destruct H4 as [H41 H42].
destruct H29 as [H43|H43].
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H27 H36).
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H37 H38).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H12 H43).
---------------------------------------- contradiction H46.
------------------------------------- destruct H43 as [H44|H44].
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H27 H36).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H37 H38).
---------------------------------------- contradiction H46.
-------------------------------------- destruct H44 as [H45|H45].
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H27 H36).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H37 H38).
----------------------------------------- contradiction H47.
--------------------------------------- destruct H45 as [H46|H46].
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H27 H36).
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H37 H38).
------------------------------------------ contradiction H48.
---------------------------------------- destruct H46 as [H47|H47].
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H27 H36).
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H37 H38).
------------------------------------------- assert (* Cut *) (False) as H50.
-------------------------------------------- apply (@H17 H47).
-------------------------------------------- contradiction H50.
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H27 H36).
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H37 H38).
------------------------------------------- contradiction H49.

---------------------------------- destruct H36 as [H37|H37].
----------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A F D))) as H38.
------------------------------------ intro H38.
apply (@H16 H37).
------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A F D)).
-------------------------------------intro H39.
destruct H3 as [H40 H41].
destruct H4 as [H42 H43].
destruct H29 as [H44|H44].
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H16 H37).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H38 H39).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H12 H44).
----------------------------------------- contradiction H47.
-------------------------------------- destruct H44 as [H45|H45].
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H16 H37).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H38 H39).
----------------------------------------- contradiction H47.
--------------------------------------- destruct H45 as [H46|H46].
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H16 H37).
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H38 H39).
------------------------------------------ contradiction H48.
---------------------------------------- destruct H46 as [H47|H47].
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H16 H37).
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H38 H39).
------------------------------------------- contradiction H49.
----------------------------------------- destruct H47 as [H48|H48].
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H16 H37).
------------------------------------------- assert (* Cut *) (False) as H50.
-------------------------------------------- apply (@H38 H39).
-------------------------------------------- assert (* Cut *) (False) as H51.
--------------------------------------------- apply (@H17 H48).
--------------------------------------------- contradiction H51.
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H16 H37).
------------------------------------------- assert (* Cut *) (False) as H50.
-------------------------------------------- apply (@H38 H39).
-------------------------------------------- contradiction H50.

----------------------------------- exact H37.
------------------------------ assert (* Cut *) (euclidean__axioms.BetS A E D) as H33.
------------------------------- assert ((A = D) \/ ((A = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A E) \/ ((euclidean__axioms.BetS A D E) \/ (euclidean__axioms.BetS A E D)))))) as H33 by exact H29.
assert ((A = D) \/ ((A = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D A E) \/ ((euclidean__axioms.BetS A D E) \/ (euclidean__axioms.BetS A E D)))))) as __TmpHyp by exact H33.
destruct __TmpHyp as [H34|H34].
-------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E D))) as H35.
--------------------------------- intro H35.
apply (@H12 H34).
--------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E D)).
----------------------------------intro H36.
destruct H3 as [H37 H38].
destruct H4 as [H39 H40].
destruct H28 as [H41|H41].
----------------------------------- assert (* Cut *) (False) as H42.
------------------------------------ apply (@H12 H34).
------------------------------------ assert (* Cut *) (False) as H43.
------------------------------------- apply (@H35 H36).
------------------------------------- contradiction H43.
----------------------------------- destruct H41 as [H42|H42].
------------------------------------ assert (* Cut *) (False) as H43.
------------------------------------- apply (@H12 H34).
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H35 H36).
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H30 H42).
--------------------------------------- contradiction H45.
------------------------------------ destruct H42 as [H43|H43].
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H12 H34).
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H35 H36).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H31 H43).
---------------------------------------- contradiction H46.
------------------------------------- destruct H43 as [H44|H44].
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H12 H34).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H35 H36).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H27 H44).
----------------------------------------- contradiction H47.
-------------------------------------- destruct H44 as [H45|H45].
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H12 H34).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H35 H36).
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H16 H45).
------------------------------------------ contradiction H48.
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H12 H34).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H35 H36).
----------------------------------------- contradiction H47.

-------------------------------- destruct H34 as [H35|H35].
--------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E D))) as H36.
---------------------------------- intro H36.
assert (* Cut *) (euclidean__axioms.Cong A F A F) as H37.
----------------------------------- destruct H4 as [H37 H38].
destruct H3 as [H39 H40].
apply (@euclidean__axioms.cn__congruencereflexive A F).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F E F) as H38.
------------------------------------ destruct H4 as [H38 H39].
destruct H3 as [H40 H41].
apply (@eq__ind__r euclidean__axioms.Point E (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.Col A0 D E) -> ((euclidean__axioms.Col A0 D F) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Par A0 D B C) -> ((euclidean__defs.Par A0 B D C) -> ((euclidean__axioms.Cong A0 D B C) -> ((euclidean__axioms.Cong A0 D E F) -> ((euclidean__axioms.neq A0 D) -> ((euclidean__axioms.neq D A0) -> ((~(euclidean__axioms.EF A0 B C D E B C F)) -> ((~(euclidean__axioms.BetS A0 D F)) -> ((~(euclidean__axioms.BetS A0 D E)) -> ((euclidean__defs.Par B A0 D C) -> ((euclidean__defs.Par D C B A0) -> ((euclidean__defs.Par D A0 C B) -> ((euclidean__defs.PG D C B A0) -> ((~(euclidean__axioms.BetS E A0 D)) -> ((~(euclidean__axioms.BetS D A0 F)) -> (((A0 = D) \/ ((A0 = F) \/ ((D = F) \/ ((euclidean__axioms.BetS D A0 F) \/ ((euclidean__axioms.BetS A0 D F) \/ (euclidean__axioms.BetS A0 F D)))))) -> ((~(A0 = F)) -> ((euclidean__axioms.BetS A0 F D) -> ((~(euclidean__axioms.BetS A0 E D)) -> ((euclidean__axioms.Cong A0 F A0 F) -> (euclidean__axioms.Cong A0 F E F)))))))))))))))))))))))))) with (x := A).
-------------------------------------intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
exact H65.

------------------------------------- exact H35.
------------------------------------- exact H.
------------------------------------- exact H1.
------------------------------------- exact H2.
------------------------------------- exact H40.
------------------------------------- exact H41.
------------------------------------- exact H5.
------------------------------------- exact H8.
------------------------------------- exact H11.
------------------------------------- exact H12.
------------------------------------- exact H14.
------------------------------------- exact H15.
------------------------------------- exact H16.
------------------------------------- exact H17.
------------------------------------- exact H18.
------------------------------------- exact H19.
------------------------------------- exact H20.
------------------------------------- exact H21.
------------------------------------- exact H26.
------------------------------------- exact H27.
------------------------------------- exact H28.
------------------------------------- exact H30.
------------------------------------- exact H32.
------------------------------------- exact H36.
------------------------------------- exact H37.
------------------------------------ assert (* Cut *) (euclidean__defs.Lt E F A D) as H39.
------------------------------------- exists F.
split.
-------------------------------------- exact H32.
-------------------------------------- exact H38.
------------------------------------- assert (* Cut *) (euclidean__defs.Lt E F E F) as H40.
-------------------------------------- destruct H4 as [H40 H41].
destruct H3 as [H42 H43].
apply (@lemma__lessthancongruence.lemma__lessthancongruence E F A D E F H39 H11).
-------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt E F E F)) as H41.
--------------------------------------- destruct H4 as [H41 H42].
destruct H3 as [H43 H44].
apply (@lemma__trichotomy2.lemma__trichotomy2 E F E F H40).
--------------------------------------- apply (@H41 H40).
---------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E D)).
-----------------------------------intro H37.
destruct H3 as [H38 H39].
destruct H4 as [H40 H41].
destruct H28 as [H42|H42].
------------------------------------ assert (* Cut *) (False) as H43.
------------------------------------- apply (@H36 H37).
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H12 H42).
-------------------------------------- contradiction H44.
------------------------------------ destruct H42 as [H43|H43].
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H36 H37).
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H30 H43).
--------------------------------------- contradiction H45.
------------------------------------- destruct H43 as [H44|H44].
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H36 H37).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H31 H44).
---------------------------------------- contradiction H46.
-------------------------------------- destruct H44 as [H45|H45].
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H36 H37).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H27 H45).
----------------------------------------- contradiction H47.
--------------------------------------- destruct H45 as [H46|H46].
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H36 H37).
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H16 H46).
------------------------------------------ contradiction H48.
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H36 H37).
----------------------------------------- contradiction H47.

--------------------------------- destruct H35 as [H36|H36].
---------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E D))) as H37.
----------------------------------- intro H37.
assert (* Cut *) (euclidean__axioms.BetS D F A) as H38.
------------------------------------ destruct H4 as [H38 H39].
destruct H3 as [H40 H41].
apply (@euclidean__axioms.axiom__betweennesssymmetry A F D H32).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong D F D F) as H39.
------------------------------------- destruct H4 as [H39 H40].
destruct H3 as [H41 H42].
apply (@euclidean__axioms.cn__congruencereflexive D F).
------------------------------------- assert (* Cut *) (euclidean__defs.Lt D F D A) as H40.
-------------------------------------- exists F.
split.
--------------------------------------- exact H38.
--------------------------------------- exact H39.
-------------------------------------- assert (* Cut *) (euclidean__defs.Lt E F D A) as H41.
--------------------------------------- destruct H4 as [H41 H42].
destruct H3 as [H43 H44].
apply (@eq__ind__r euclidean__axioms.Point E (fun D0 => (euclidean__defs.PG A B C D0) -> ((euclidean__axioms.Col A D0 E) -> ((euclidean__axioms.Col A D0 F) -> ((euclidean__defs.Par A B C D0) -> ((euclidean__defs.Par A D0 B C) -> ((euclidean__defs.Par A B D0 C) -> ((euclidean__axioms.Cong A D0 B C) -> ((euclidean__axioms.Cong A D0 E F) -> ((euclidean__axioms.neq A D0) -> ((euclidean__axioms.neq D0 A) -> ((~(euclidean__axioms.EF A B C D0 E B C F)) -> ((~(euclidean__axioms.BetS A D0 F)) -> ((~(euclidean__axioms.BetS A D0 E)) -> ((euclidean__defs.Par B A D0 C) -> ((euclidean__defs.Par D0 C B A) -> ((euclidean__defs.Par D0 A C B) -> ((euclidean__defs.PG D0 C B A) -> ((~(euclidean__axioms.BetS E A D0)) -> ((~(euclidean__axioms.BetS D0 A F)) -> (((A = D0) \/ ((A = F) \/ ((D0 = F) \/ ((euclidean__axioms.BetS D0 A F) \/ ((euclidean__axioms.BetS A D0 F) \/ (euclidean__axioms.BetS A F D0)))))) -> ((~(D0 = F)) -> ((euclidean__axioms.BetS A F D0) -> ((~(euclidean__axioms.BetS A E D0)) -> ((euclidean__axioms.BetS D0 F A) -> ((euclidean__axioms.Cong D0 F D0 F) -> ((euclidean__defs.Lt D0 F D0 A) -> (euclidean__defs.Lt E F D0 A)))))))))))))))))))))))))))) with (x := D).
----------------------------------------intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
exact H70.

---------------------------------------- exact H36.
---------------------------------------- exact H.
---------------------------------------- exact H1.
---------------------------------------- exact H2.
---------------------------------------- exact H43.
---------------------------------------- exact H44.
---------------------------------------- exact H5.
---------------------------------------- exact H8.
---------------------------------------- exact H11.
---------------------------------------- exact H12.
---------------------------------------- exact H14.
---------------------------------------- exact H15.
---------------------------------------- exact H16.
---------------------------------------- exact H17.
---------------------------------------- exact H18.
---------------------------------------- exact H19.
---------------------------------------- exact H20.
---------------------------------------- exact H21.
---------------------------------------- exact H26.
---------------------------------------- exact H27.
---------------------------------------- exact H28.
---------------------------------------- exact H31.
---------------------------------------- exact H32.
---------------------------------------- exact H37.
---------------------------------------- exact H38.
---------------------------------------- exact H39.
---------------------------------------- exact H40.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D A E F) as H42.
---------------------------------------- destruct H4 as [H42 H43].
destruct H3 as [H44 H45].
assert (* Cut *) ((euclidean__axioms.Cong D A F E) /\ ((euclidean__axioms.Cong D A E F) /\ (euclidean__axioms.Cong A D F E))) as H46.
----------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A D E F H11).
----------------------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H49.
---------------------------------------- assert (* Cut *) (euclidean__defs.Lt E F E F) as H43.
----------------------------------------- destruct H4 as [H43 H44].
destruct H3 as [H45 H46].
apply (@lemma__lessthancongruence.lemma__lessthancongruence E F D A E F H41 H42).
----------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt E F E F)) as H44.
------------------------------------------ destruct H4 as [H44 H45].
destruct H3 as [H46 H47].
apply (@lemma__trichotomy2.lemma__trichotomy2 E F E F H43).
------------------------------------------ apply (@H44 H43).
----------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E D)).
------------------------------------intro H38.
destruct H3 as [H39 H40].
destruct H4 as [H41 H42].
destruct H28 as [H43|H43].
------------------------------------- assert (* Cut *) (False) as H44.
-------------------------------------- apply (@H37 H38).
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H12 H43).
--------------------------------------- contradiction H45.
------------------------------------- destruct H43 as [H44|H44].
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H37 H38).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H30 H44).
---------------------------------------- contradiction H46.
-------------------------------------- destruct H44 as [H45|H45].
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H37 H38).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H31 H45).
----------------------------------------- contradiction H47.
--------------------------------------- destruct H45 as [H46|H46].
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H37 H38).
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H27 H46).
------------------------------------------ contradiction H48.
---------------------------------------- destruct H46 as [H47|H47].
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H37 H38).
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H16 H47).
------------------------------------------- contradiction H49.
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H37 H38).
------------------------------------------ contradiction H48.

---------------------------------- destruct H36 as [H37|H37].
----------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS A E D))) as H38.
------------------------------------ intro H38.
assert (* Cut *) (euclidean__axioms.BetS E A D) as H39.
------------------------------------- destruct H4 as [H39 H40].
destruct H3 as [H41 H42].
apply (@euclidean__axioms.axiom__betweennesssymmetry D A E H37).
------------------------------------- apply (@H26 H39).
------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E D)).
-------------------------------------intro H39.
destruct H3 as [H40 H41].
destruct H4 as [H42 H43].
destruct H28 as [H44|H44].
-------------------------------------- assert (* Cut *) (False) as H45.
--------------------------------------- apply (@H38 H39).
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H12 H44).
---------------------------------------- contradiction H46.
-------------------------------------- destruct H44 as [H45|H45].
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H38 H39).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H30 H45).
----------------------------------------- contradiction H47.
--------------------------------------- destruct H45 as [H46|H46].
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H38 H39).
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H31 H46).
------------------------------------------ contradiction H48.
---------------------------------------- destruct H46 as [H47|H47].
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H38 H39).
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H27 H47).
------------------------------------------- contradiction H49.
----------------------------------------- destruct H47 as [H48|H48].
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H38 H39).
------------------------------------------- assert (* Cut *) (False) as H50.
-------------------------------------------- apply (@H16 H48).
-------------------------------------------- contradiction H50.
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H38 H39).
------------------------------------------- contradiction H49.

----------------------------------- destruct H37 as [H38|H38].
------------------------------------ assert (* Cut *) (~(~(euclidean__axioms.BetS A E D))) as H39.
------------------------------------- intro H39.
apply (@H17 H38).
------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS A E D)).
--------------------------------------intro H40.
destruct H3 as [H41 H42].
destruct H4 as [H43 H44].
destruct H28 as [H45|H45].
--------------------------------------- assert (* Cut *) (False) as H46.
---------------------------------------- apply (@H17 H38).
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H39 H40).
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H12 H45).
------------------------------------------ contradiction H48.
--------------------------------------- destruct H45 as [H46|H46].
---------------------------------------- assert (* Cut *) (False) as H47.
----------------------------------------- apply (@H17 H38).
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H39 H40).
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H30 H46).
------------------------------------------- contradiction H49.
---------------------------------------- destruct H46 as [H47|H47].
----------------------------------------- assert (* Cut *) (False) as H48.
------------------------------------------ apply (@H17 H38).
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H39 H40).
------------------------------------------- assert (* Cut *) (False) as H50.
-------------------------------------------- apply (@H31 H47).
-------------------------------------------- contradiction H50.
----------------------------------------- destruct H47 as [H48|H48].
------------------------------------------ assert (* Cut *) (False) as H49.
------------------------------------------- apply (@H17 H38).
------------------------------------------- assert (* Cut *) (False) as H50.
-------------------------------------------- apply (@H39 H40).
-------------------------------------------- assert (* Cut *) (False) as H51.
--------------------------------------------- apply (@H27 H48).
--------------------------------------------- contradiction H51.
------------------------------------------ destruct H48 as [H49|H49].
------------------------------------------- assert (* Cut *) (False) as H50.
-------------------------------------------- apply (@H17 H38).
-------------------------------------------- assert (* Cut *) (False) as H51.
--------------------------------------------- apply (@H39 H40).
--------------------------------------------- assert (* Cut *) (False) as H52.
---------------------------------------------- apply (@H16 H49).
---------------------------------------------- contradiction H52.
------------------------------------------- assert (* Cut *) (False) as H50.
-------------------------------------------- apply (@H17 H38).
-------------------------------------------- assert (* Cut *) (False) as H51.
--------------------------------------------- apply (@H39 H40).
--------------------------------------------- contradiction H51.

------------------------------------ exact H38.
------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A E F)) as H34.
-------------------------------- intro H34.
assert (* Cut *) (euclidean__axioms.BetS E F D) as H35.
--------------------------------- destruct H4 as [H35 H36].
destruct H3 as [H37 H38].
apply (@lemma__3__6a.lemma__3__6a A E F D H34 H32).
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong E F E F) as H36.
---------------------------------- destruct H4 as [H36 H37].
destruct H3 as [H38 H39].
apply (@euclidean__axioms.cn__congruencereflexive E F).
---------------------------------- assert (* Cut *) (euclidean__defs.Lt E F E D) as H37.
----------------------------------- exists F.
split.
------------------------------------ exact H35.
------------------------------------ exact H36.
----------------------------------- assert (* Cut *) (euclidean__axioms.BetS D E A) as H38.
------------------------------------ destruct H4 as [H38 H39].
destruct H3 as [H40 H41].
apply (@euclidean__axioms.axiom__betweennesssymmetry A E D H33).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong D E D E) as H39.
------------------------------------- destruct H4 as [H39 H40].
destruct H3 as [H41 H42].
apply (@euclidean__axioms.cn__congruencereflexive D E).
------------------------------------- assert (* Cut *) (euclidean__defs.Lt D E D A) as H40.
-------------------------------------- exists E.
split.
--------------------------------------- exact H38.
--------------------------------------- exact H39.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E D D E) as H41.
--------------------------------------- destruct H4 as [H41 H42].
destruct H3 as [H43 H44].
apply (@euclidean__axioms.cn__equalityreverse E D).
--------------------------------------- assert (* Cut *) (euclidean__defs.Lt E F D E) as H42.
---------------------------------------- destruct H4 as [H42 H43].
destruct H3 as [H44 H45].
apply (@lemma__lessthancongruence.lemma__lessthancongruence E F E D D E H37 H41).
---------------------------------------- assert (* Cut *) (euclidean__defs.Lt E F D A) as H43.
----------------------------------------- destruct H4 as [H43 H44].
destruct H3 as [H45 H46].
apply (@lemma__lessthantransitive.lemma__lessthantransitive E F D E D A H42 H40).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D A A D) as H44.
------------------------------------------ destruct H4 as [H44 H45].
destruct H3 as [H46 H47].
apply (@euclidean__axioms.cn__equalityreverse D A).
------------------------------------------ assert (* Cut *) (euclidean__defs.Lt E F A D) as H45.
------------------------------------------- destruct H4 as [H45 H46].
destruct H3 as [H47 H48].
apply (@lemma__lessthancongruence.lemma__lessthancongruence E F D A A D H43 H44).
------------------------------------------- assert (* Cut *) (euclidean__defs.Lt E F E F) as H46.
-------------------------------------------- destruct H4 as [H46 H47].
destruct H3 as [H48 H49].
apply (@lemma__lessthancongruence.lemma__lessthancongruence E F A D E F H45 H11).
-------------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt E F E F)) as H47.
--------------------------------------------- destruct H4 as [H47 H48].
destruct H3 as [H49 H50].
apply (@lemma__trichotomy2.lemma__trichotomy2 E F E F H46).
--------------------------------------------- apply (@H47 H46).
-------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A F E)) as H35.
--------------------------------- intro H35.
assert (* Cut *) (euclidean__axioms.BetS F E D) as H36.
---------------------------------- destruct H4 as [H36 H37].
destruct H3 as [H38 H39].
apply (@lemma__3__6a.lemma__3__6a A F E D H35 H33).
---------------------------------- assert (* Cut *) (euclidean__axioms.Cong F E F E) as H37.
----------------------------------- destruct H4 as [H37 H38].
destruct H3 as [H39 H40].
apply (@euclidean__axioms.cn__congruencereflexive F E).
----------------------------------- assert (* Cut *) (euclidean__defs.Lt F E F D) as H38.
------------------------------------ exists E.
split.
------------------------------------- exact H36.
------------------------------------- exact H37.
------------------------------------ assert (* Cut *) (euclidean__axioms.BetS D F A) as H39.
------------------------------------- destruct H4 as [H39 H40].
destruct H3 as [H41 H42].
apply (@euclidean__axioms.axiom__betweennesssymmetry A F D H32).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D F D F) as H40.
-------------------------------------- destruct H4 as [H40 H41].
destruct H3 as [H42 H43].
apply (@euclidean__axioms.cn__congruencereflexive D F).
-------------------------------------- assert (* Cut *) (euclidean__defs.Lt D F D A) as H41.
--------------------------------------- exists F.
split.
---------------------------------------- exact H39.
---------------------------------------- exact H40.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F D D F) as H42.
---------------------------------------- destruct H4 as [H42 H43].
destruct H3 as [H44 H45].
apply (@euclidean__axioms.cn__equalityreverse F D).
---------------------------------------- assert (* Cut *) (euclidean__defs.Lt F E D F) as H43.
----------------------------------------- destruct H4 as [H43 H44].
destruct H3 as [H45 H46].
apply (@lemma__lessthancongruence.lemma__lessthancongruence F E F D D F H38 H42).
----------------------------------------- assert (* Cut *) (euclidean__defs.Lt F E D A) as H44.
------------------------------------------ destruct H4 as [H44 H45].
destruct H3 as [H46 H47].
apply (@lemma__lessthantransitive.lemma__lessthantransitive F E D F D A H43 H41).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong D A A D) as H45.
------------------------------------------- destruct H4 as [H45 H46].
destruct H3 as [H47 H48].
apply (@euclidean__axioms.cn__equalityreverse D A).
------------------------------------------- assert (* Cut *) (euclidean__defs.Lt F E A D) as H46.
-------------------------------------------- destruct H4 as [H46 H47].
destruct H3 as [H48 H49].
apply (@lemma__lessthancongruence.lemma__lessthancongruence F E D A A D H44 H45).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D F E) as H47.
--------------------------------------------- destruct H4 as [H47 H48].
destruct H3 as [H49 H50].
assert (* Cut *) ((euclidean__axioms.Cong D A F E) /\ ((euclidean__axioms.Cong D A E F) /\ (euclidean__axioms.Cong A D F E))) as H51.
---------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A D E F H11).
---------------------------------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H55.
--------------------------------------------- assert (* Cut *) (euclidean__defs.Lt F E F E) as H48.
---------------------------------------------- destruct H4 as [H48 H49].
destruct H3 as [H50 H51].
apply (@lemma__lessthancongruence.lemma__lessthancongruence F E A D F E H46 H47).
---------------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt F E F E)) as H49.
----------------------------------------------- destruct H4 as [H49 H50].
destruct H3 as [H51 H52].
apply (@lemma__trichotomy2.lemma__trichotomy2 F E F E H48).
----------------------------------------------- apply (@H49 H48).
--------------------------------- assert (* Cut *) (E = F) as H36.
---------------------------------- destruct H4 as [H36 H37].
destruct H3 as [H38 H39].
apply (@euclidean__axioms.axiom__connectivity A E F D H33 H32 H34 H35).
---------------------------------- apply (@H13 H36).
------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.EF A B C D E B C F)).
--------------intro H16.
destruct H3 as [H17 H18].
destruct H4 as [H19 H20].
assert (* Cut *) (False) as H21.
--------------- apply (@H15 H16).
--------------- contradiction H21.

Qed.
