Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__8__2.
Require Export lemma__8__7.
Require Export lemma__ABCequalsCBA.
Require Export lemma__Euclid4.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__PGflip.
Require Export lemma__angleaddition.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__collinearright.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__diagonalsbisect.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesideflip.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__righttogether.
Require Export lemma__samesidesymmetric.
Require Export lemma__squareparallelogram.
Require Export logic.
Require Export proposition__04.
Require Export proposition__34.
Require Export proposition__41.
Require Export proposition__47A.
Definition proposition__47B : forall A B C D E F G, (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.Per B A C) -> ((euclidean__defs.SQ A B F G) -> ((euclidean__axioms.TS G B A C) -> ((euclidean__defs.SQ B C E D) -> ((euclidean__axioms.TS D C B A) -> (exists X Y, (euclidean__defs.PG B X Y D) /\ ((euclidean__axioms.BetS B X C) /\ ((euclidean__defs.PG X C E Y) /\ ((euclidean__axioms.BetS D Y E) /\ ((euclidean__axioms.BetS Y X A) /\ ((euclidean__defs.Per D Y A) /\ (euclidean__axioms.EF A B F G B X Y D)))))))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
assert (* Cut *) (exists M L, (euclidean__defs.PG B M L D) /\ ((euclidean__axioms.BetS B M C) /\ ((euclidean__defs.PG M C E L) /\ ((euclidean__axioms.BetS D L E) /\ ((euclidean__axioms.BetS L M A) /\ (euclidean__defs.Per D L A)))))) as H5.
- apply (@proposition__47A.proposition__47A A B C D E H H0 H3 H4).
- destruct H5 as [M H6].
destruct H6 as [L H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
assert (exists N, (euclidean__axioms.BetS D N A) /\ ((euclidean__axioms.Col C B N) /\ (euclidean__axioms.nCol C B D))) as H18 by exact H4.
destruct H18 as [N H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
assert (* Cut *) (euclidean__defs.Per G A B) as H24.
-- destruct H3 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H1 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H42.
-- assert (* Cut *) (euclidean__axioms.BetS G A C) as H25.
--- assert (* Cut *) (forall A0 B0 C0 G0, (euclidean__defs.Per G0 A0 B0) -> ((euclidean__defs.Per B0 A0 C0) -> ((euclidean__axioms.TS G0 B0 A0 C0) -> (euclidean__axioms.BetS G0 A0 C0)))) as H25.
---- intro A0.
intro B0.
intro C0.
intro G0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.RT G0 A0 B0 B0 A0 C0) /\ (euclidean__axioms.BetS G0 A0 C0)) as __2.
----- apply (@lemma__righttogether.lemma__righttogether A0 B0 C0 G0 __ __0 __1).
----- destruct __2 as [__2 __3].
exact __3.
---- apply (@H25 A B C G H24 H0 H2).
--- assert (* Cut *) (euclidean__defs.Per A B F) as H26.
---- destruct H3 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H1 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H46.
---- assert (* Cut *) (euclidean__defs.Per F B A) as H27.
----- apply (@lemma__8__2.lemma__8__2 A B F H26).
----- assert (* Cut *) (euclidean__defs.Per D B C) as H28.
------ destruct H3 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H1 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H34.
------ assert (euclidean__axioms.nCol A B C) as H29 by exact H.
assert (* Cut *) (euclidean__defs.PG A B F G) as H30.
------- apply (@lemma__squareparallelogram.lemma__squareparallelogram A B F G H1).
------- assert (* Cut *) (euclidean__defs.Par A B F G) as H31.
-------- destruct H30 as [H31 H32].
destruct H12 as [H33 H34].
destruct H8 as [H35 H36].
exact H31.
-------- assert (* Cut *) (euclidean__defs.Par A B G F) as H32.
--------- assert (* Cut *) ((euclidean__defs.Par B A F G) /\ ((euclidean__defs.Par A B G F) /\ (euclidean__defs.Par B A G F))) as H32.
---------- apply (@lemma__parallelflip.lemma__parallelflip A B F G H31).
---------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H35.
--------- assert (* Cut *) (euclidean__defs.TP A B G F) as H33.
---------- apply (@lemma__paralleldef2B.lemma__paralleldef2B A B G F H32).
---------- assert (* Cut *) (euclidean__defs.OS G F A B) as H34.
----------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H39.
----------- assert (* Cut *) (euclidean__defs.OS F G A B) as H35.
------------ assert (* Cut *) ((euclidean__defs.OS F G A B) /\ ((euclidean__defs.OS G F B A) /\ (euclidean__defs.OS F G B A))) as H35.
------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric A B G F H34).
------------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H36.
------------ assert (* Cut *) (euclidean__axioms.TS G A B C) as H36.
------------- apply (@lemma__oppositesideflip.lemma__oppositesideflip B A G C H2).
------------- assert (* Cut *) (euclidean__axioms.TS F A B C) as H37.
-------------- apply (@lemma__planeseparation.lemma__planeseparation A B F G C H35 H36).
-------------- assert (exists a, (euclidean__axioms.BetS F a C) /\ ((euclidean__axioms.Col A B a) /\ (euclidean__axioms.nCol A B F))) as H38 by exact H37.
destruct H38 as [a H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
assert (* Cut *) (euclidean__axioms.Col B A a) as H44.
--------------- assert (* Cut *) ((euclidean__axioms.Col B A a) /\ ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A))))) as H44.
---------------- apply (@lemma__collinearorder.lemma__collinearorder A B a H42).
---------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H45.
--------------- assert (* Cut *) (euclidean__defs.Par A G B F) as H45.
---------------- destruct H30 as [H45 H46].
destruct H12 as [H47 H48].
destruct H8 as [H49 H50].
exact H46.
---------------- assert (* Cut *) (euclidean__defs.Par A G F B) as H46.
----------------- assert (* Cut *) ((euclidean__defs.Par G A B F) /\ ((euclidean__defs.Par A G F B) /\ (euclidean__defs.Par G A F B))) as H46.
------------------ apply (@lemma__parallelflip.lemma__parallelflip A G B F H45).
------------------ destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H49.
----------------- assert (* Cut *) (euclidean__axioms.Col G A C) as H47.
------------------ right.
right.
right.
right.
left.
exact H25.
------------------ assert (* Cut *) (euclidean__axioms.Col A G C) as H48.
------------------- assert (* Cut *) ((euclidean__axioms.Col A G C) /\ ((euclidean__axioms.Col A C G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G))))) as H48.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder G A C H47).
-------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H49.
------------------- assert (* Cut *) (euclidean__axioms.neq G C) as H49.
-------------------- assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G C))) as H49.
--------------------- apply (@lemma__betweennotequal.lemma__betweennotequal G A C H25).
--------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H53.
-------------------- assert (* Cut *) (euclidean__axioms.neq C G) as H50.
--------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G C H49).
--------------------- assert (* Cut *) (euclidean__defs.Par F B A G) as H51.
---------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A G F B H46).
---------------------- assert (* Cut *) (euclidean__defs.Par F B C G) as H52.
----------------------- apply (@lemma__collinearparallel.lemma__collinearparallel F B C A G H51 H48 H50).
----------------------- assert (* Cut *) (euclidean__defs.Par F B G C) as H53.
------------------------ assert (* Cut *) ((euclidean__defs.Par B F C G) /\ ((euclidean__defs.Par F B G C) /\ (euclidean__defs.Par B F G C))) as H53.
------------------------- apply (@lemma__parallelflip.lemma__parallelflip F B C G H52).
------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H56.
------------------------ assert (* Cut *) (~(euclidean__defs.Meet F B G C)) as H54.
------------------------- assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H54 by exact H53.
assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H54.
destruct __TmpHyp as [x H55].
destruct H55 as [x0 H56].
destruct H56 as [x1 H57].
destruct H57 as [x2 H58].
destruct H58 as [x3 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H80 by exact H52.
assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H80.
destruct __TmpHyp0 as [x4 H81].
destruct H81 as [x5 H82].
destruct H82 as [x6 H83].
destruct H83 as [x7 H84].
destruct H84 as [x8 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H106 by exact H51.
assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H106.
destruct __TmpHyp1 as [x9 H107].
destruct H107 as [x10 H108].
destruct H108 as [x11 H109].
destruct H109 as [x12 H110].
destruct H110 as [x13 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H132 by exact H46.
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H132.
destruct __TmpHyp2 as [x14 H133].
destruct H133 as [x15 H134].
destruct H134 as [x16 H135].
destruct H135 as [x17 H136].
destruct H136 as [x18 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H158 by exact H45.
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H158.
destruct __TmpHyp3 as [x19 H159].
destruct H159 as [x20 H160].
destruct H160 as [x21 H161].
destruct H161 as [x22 H162].
destruct H162 as [x23 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H184 by exact H32.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H184.
destruct __TmpHyp4 as [x24 H185].
destruct H185 as [x25 H186].
destruct H186 as [x26 H187].
destruct H187 as [x27 H188].
destruct H188 as [x28 H189].
destruct H189 as [H190 H191].
destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
destruct H199 as [H200 H201].
destruct H201 as [H202 H203].
destruct H203 as [H204 H205].
destruct H205 as [H206 H207].
destruct H207 as [H208 H209].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H210 by exact H31.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H210.
destruct __TmpHyp5 as [x29 H211].
destruct H211 as [x30 H212].
destruct H212 as [x31 H213].
destruct H213 as [x32 H214].
destruct H214 as [x33 H215].
destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
destruct H219 as [H220 H221].
destruct H221 as [H222 H223].
destruct H223 as [H224 H225].
destruct H225 as [H226 H227].
destruct H227 as [H228 H229].
destruct H229 as [H230 H231].
destruct H231 as [H232 H233].
destruct H233 as [H234 H235].
exact H76.
------------------------- assert (* Cut *) (euclidean__axioms.neq A C) as H55.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H55.
--------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct A B C H29).
--------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H60.
-------------------------- assert (* Cut *) (euclidean__axioms.nCol A B F) as H56.
--------------------------- assert (* Cut *) ((euclidean__axioms.nCol F B G) /\ ((euclidean__axioms.nCol F G C) /\ ((euclidean__axioms.nCol B G C) /\ (euclidean__axioms.nCol F B C)))) as H56.
---------------------------- apply (@lemma__parallelNC.lemma__parallelNC F B G C H53).
---------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H43.
--------------------------- assert (* Cut *) (euclidean__axioms.neq F A) as H57.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A)))))) as H57.
----------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct A B F H56).
----------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H67.
---------------------------- assert (* Cut *) (euclidean__axioms.neq F B) as H58.
----------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F A)))))) as H58.
------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct A B F H56).
------------------------------ destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H67.
----------------------------- assert (* Cut *) (B = B) as H59.
------------------------------ apply (@logic.eq__refl Point B).
------------------------------ assert (* Cut *) (euclidean__axioms.Col F B B) as H60.
------------------------------- right.
right.
left.
exact H59.
------------------------------- assert (* Cut *) (euclidean__axioms.BetS B a A) as H61.
-------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween F B G C B A a H60 H47 H58 H49 H58 H55 H54 H40 H44).
-------------------------------- assert (* Cut *) (euclidean__axioms.neq B a) as H62.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq a A) /\ ((euclidean__axioms.neq B a) /\ (euclidean__axioms.neq B A))) as H62.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B a A H61).
---------------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H65.
--------------------------------- assert (* Cut *) (euclidean__defs.Out B a A) as H63.
---------------------------------- apply (@lemma__ray4.lemma__ray4 B a A).
-----------------------------------right.
right.
exact H61.

----------------------------------- exact H62.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H64.
----------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric F B H58).
----------------------------------- assert (* Cut *) (F = F) as H65.
------------------------------------ apply (@logic.eq__refl Point F).
------------------------------------ assert (* Cut *) (euclidean__defs.Out B F F) as H66.
------------------------------------- apply (@lemma__ray4.lemma__ray4 B F F).
--------------------------------------right.
left.
exact H65.

-------------------------------------- exact H64.
------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B F) as H67.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F B G) /\ ((euclidean__axioms.nCol F G C) /\ ((euclidean__axioms.nCol B G C) /\ (euclidean__axioms.nCol F B C)))) as H67.
--------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC F B G C H53).
--------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H56.
-------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F B A) as H68.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A F) /\ ((euclidean__axioms.nCol B F A) /\ ((euclidean__axioms.nCol F A B) /\ ((euclidean__axioms.nCol A F B) /\ (euclidean__axioms.nCol F B A))))) as H68.
---------------------------------------- apply (@lemma__NCorder.lemma__NCorder A B F H67).
---------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H76.
--------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B A F B A) as H69.
---------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive F B A H68).
---------------------------------------- assert (* Cut *) (euclidean__defs.Out B A a) as H70.
----------------------------------------- apply (@lemma__ray5.lemma__ray5 B a A H63).
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B A F B a) as H71.
------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper F B A F B A F a H69 H66 H70).
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq B C) as H72.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H72.
-------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct A B C H29).
-------------------------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H75.
------------------------------------------- assert (* Cut *) (C = C) as H73.
-------------------------------------------- apply (@logic.eq__refl Point C).
-------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C C) as H74.
--------------------------------------------- apply (@lemma__ray4.lemma__ray4 B C C).
----------------------------------------------right.
left.
exact H73.

---------------------------------------------- exact H72.
--------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A B C) as H75.
---------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive A B C H29).
---------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C a B C) as H76.
----------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper A B C A B C a C H75 H70 H74).
----------------------------------------------- assert (* Cut *) (euclidean__defs.SumA F B A A B C F B C) as H77.
------------------------------------------------ exists a.
split.
------------------------------------------------- exact H71.
------------------------------------------------- split.
-------------------------------------------------- exact H76.
-------------------------------------------------- exact H40.
------------------------------------------------ assert (exists c, (euclidean__axioms.BetS D c A) /\ ((euclidean__axioms.Col C B c) /\ (euclidean__axioms.nCol C B D))) as H78 by exact H4.
destruct H78 as [c H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
assert (* Cut *) (euclidean__defs.PG B C E D) as H84.
------------------------------------------------- apply (@lemma__squareparallelogram.lemma__squareparallelogram B C E D H3).
------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D C E) as H85.
-------------------------------------------------- destruct H84 as [H85 H86].
destruct H30 as [H87 H88].
destruct H12 as [H89 H90].
destruct H8 as [H91 H92].
exact H86.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C E B D) as H86.
--------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric B D C E H85).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C E D B) as H87.
---------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par E C B D) /\ ((euclidean__defs.Par C E D B) /\ (euclidean__defs.Par E C D B))) as H87.
----------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip C E B D H86).
----------------------------------------------------- destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H90.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C c) as H88.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C c) /\ ((euclidean__axioms.Col B c C) /\ ((euclidean__axioms.Col c C B) /\ ((euclidean__axioms.Col C c B) /\ (euclidean__axioms.Col c B C))))) as H88.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder C B c H82).
------------------------------------------------------ destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H89.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B M C) as H89.
------------------------------------------------------ right.
right.
right.
right.
left.
exact H10.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C B M) as H90.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col B C M) /\ (euclidean__axioms.Col C M B))))) as H90.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B M C H89).
-------------------------------------------------------- destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
exact H95.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B c) as H91.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C M) /\ ((euclidean__axioms.Col B M C) /\ ((euclidean__axioms.Col M C B) /\ ((euclidean__axioms.Col C M B) /\ (euclidean__axioms.Col M B C))))) as H91.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C B M H90).
--------------------------------------------------------- destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
exact H82.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H92.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C)))))) as H92.
---------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct C B D H83).
---------------------------------------------------------- destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
exact H93.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B M c) as H93.
---------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col B M c).
-----------------------------------------------------------intro H93.
apply (@euclidean__tactics.Col__nCol__False B M c H93).
------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 C B M c H90 H91 H92).


---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D M L) as H94.
----------------------------------------------------------- destruct H84 as [H94 H95].
destruct H30 as [H96 H97].
destruct H12 as [H98 H99].
destruct H8 as [H100 H101].
exact H101.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L M A) as H95.
------------------------------------------------------------ right.
right.
right.
right.
left.
exact H16.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col M L A) as H96.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M L A) /\ ((euclidean__axioms.Col M A L) /\ ((euclidean__axioms.Col A L M) /\ ((euclidean__axioms.Col L A M) /\ (euclidean__axioms.Col A M L))))) as H96.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder L M A H95).
-------------------------------------------------------------- destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
exact H97.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L A) as H97.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A))) as H97.
--------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal L M A H16).
--------------------------------------------------------------- destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
exact H101.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A L) as H98.
--------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric L A H97).
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D A L) as H99.
---------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel B D A M L H94 H96 H98).
---------------------------------------------------------------- assert (B = B) as H100 by exact H59.
assert (* Cut *) (euclidean__defs.Par D B L A) as H101.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par D B A L) /\ ((euclidean__defs.Par B D L A) /\ (euclidean__defs.Par D B L A))) as H101.
------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip B D A L H99).
------------------------------------------------------------------ destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H105.
----------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet D B L A)) as H102.
------------------------------------------------------------------ assert (exists U V u v X, (euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L A) /\ ((euclidean__axioms.Col D B U) /\ ((euclidean__axioms.Col D B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col L A u) /\ ((euclidean__axioms.Col L A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H102 by exact H101.
assert (exists U V u v X, (euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L A) /\ ((euclidean__axioms.Col D B U) /\ ((euclidean__axioms.Col D B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col L A u) /\ ((euclidean__axioms.Col L A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet D B L A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H102.
destruct __TmpHyp as [x H103].
destruct H103 as [x0 H104].
destruct H104 as [x1 H105].
destruct H105 as [x2 H106].
destruct H106 as [x3 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
assert (exists U V u v X, (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A L) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A L u) /\ ((euclidean__axioms.Col A L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H128 by exact H99.
assert (exists U V u v X, (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A L) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A L u) /\ ((euclidean__axioms.Col A L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D A L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H128.
destruct __TmpHyp0 as [x4 H129].
destruct H129 as [x5 H130].
destruct H130 as [x6 H131].
destruct H131 as [x7 H132].
destruct H132 as [x8 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
assert (exists U V u v X, (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M L u) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H154 by exact H94.
assert (exists U V u v X, (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M L u) /\ ((euclidean__axioms.Col M L v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D M L)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H154.
destruct __TmpHyp1 as [x9 H155].
destruct H155 as [x10 H156].
destruct H156 as [x11 H157].
destruct H157 as [x12 H158].
destruct H158 as [x13 H159].
destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
assert (exists U V u v X, (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H180 by exact H87.
assert (exists U V u v X, (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col D B u) /\ ((euclidean__axioms.Col D B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E D B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H180.
destruct __TmpHyp2 as [x14 H181].
destruct H181 as [x15 H182].
destruct H182 as [x16 H183].
destruct H183 as [x17 H184].
destruct H184 as [x18 H185].
destruct H185 as [H186 H187].
destruct H187 as [H188 H189].
destruct H189 as [H190 H191].
destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
destruct H199 as [H200 H201].
destruct H201 as [H202 H203].
destruct H203 as [H204 H205].
assert (exists U V u v X, (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H206 by exact H86.
assert (exists U V u v X, (euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.Col C E U) /\ ((euclidean__axioms.Col C E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B D u) /\ ((euclidean__axioms.Col B D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C E B D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H206.
destruct __TmpHyp3 as [x19 H207].
destruct H207 as [x20 H208].
destruct H208 as [x21 H209].
destruct H209 as [x22 H210].
destruct H210 as [x23 H211].
destruct H211 as [H212 H213].
destruct H213 as [H214 H215].
destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
destruct H219 as [H220 H221].
destruct H221 as [H222 H223].
destruct H223 as [H224 H225].
destruct H225 as [H226 H227].
destruct H227 as [H228 H229].
destruct H229 as [H230 H231].
assert (exists U V u v X, (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H232 by exact H85.
assert (exists U V u v X, (euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.Col B D U) /\ ((euclidean__axioms.Col B D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C E u) /\ ((euclidean__axioms.Col C E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B D C E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H232.
destruct __TmpHyp4 as [x24 H233].
destruct H233 as [x25 H234].
destruct H234 as [x26 H235].
destruct H235 as [x27 H236].
destruct H236 as [x28 H237].
destruct H237 as [H238 H239].
destruct H239 as [H240 H241].
destruct H241 as [H242 H243].
destruct H243 as [H244 H245].
destruct H245 as [H246 H247].
destruct H247 as [H248 H249].
destruct H249 as [H250 H251].
destruct H251 as [H252 H253].
destruct H253 as [H254 H255].
destruct H255 as [H256 H257].
assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H258 by exact H53.
assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G C) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G C u) /\ ((euclidean__axioms.Col G C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B G C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H258.
destruct __TmpHyp5 as [x29 H259].
destruct H259 as [x30 H260].
destruct H260 as [x31 H261].
destruct H261 as [x32 H262].
destruct H262 as [x33 H263].
destruct H263 as [H264 H265].
destruct H265 as [H266 H267].
destruct H267 as [H268 H269].
destruct H269 as [H270 H271].
destruct H271 as [H272 H273].
destruct H273 as [H274 H275].
destruct H275 as [H276 H277].
destruct H277 as [H278 H279].
destruct H279 as [H280 H281].
destruct H281 as [H282 H283].
assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H284 by exact H52.
assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H284.
destruct __TmpHyp6 as [x34 H285].
destruct H285 as [x35 H286].
destruct H286 as [x36 H287].
destruct H287 as [x37 H288].
destruct H288 as [x38 H289].
destruct H289 as [H290 H291].
destruct H291 as [H292 H293].
destruct H293 as [H294 H295].
destruct H295 as [H296 H297].
destruct H297 as [H298 H299].
destruct H299 as [H300 H301].
destruct H301 as [H302 H303].
destruct H303 as [H304 H305].
destruct H305 as [H306 H307].
destruct H307 as [H308 H309].
assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H310 by exact H51.
assert (exists U V u v X, (euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col F B U) /\ ((euclidean__axioms.Col F B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F B A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H310.
destruct __TmpHyp7 as [x39 H311].
destruct H311 as [x40 H312].
destruct H312 as [x41 H313].
destruct H313 as [x42 H314].
destruct H314 as [x43 H315].
destruct H315 as [H316 H317].
destruct H317 as [H318 H319].
destruct H319 as [H320 H321].
destruct H321 as [H322 H323].
destruct H323 as [H324 H325].
destruct H325 as [H326 H327].
destruct H327 as [H328 H329].
destruct H329 as [H330 H331].
destruct H331 as [H332 H333].
destruct H333 as [H334 H335].
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H336 by exact H46.
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H336.
destruct __TmpHyp8 as [x44 H337].
destruct H337 as [x45 H338].
destruct H338 as [x46 H339].
destruct H339 as [x47 H340].
destruct H340 as [x48 H341].
destruct H341 as [H342 H343].
destruct H343 as [H344 H345].
destruct H345 as [H346 H347].
destruct H347 as [H348 H349].
destruct H349 as [H350 H351].
destruct H351 as [H352 H353].
destruct H353 as [H354 H355].
destruct H355 as [H356 H357].
destruct H357 as [H358 H359].
destruct H359 as [H360 H361].
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H362 by exact H45.
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B F u) /\ ((euclidean__axioms.Col B F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G B F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp9 by exact H362.
destruct __TmpHyp9 as [x49 H363].
destruct H363 as [x50 H364].
destruct H364 as [x51 H365].
destruct H365 as [x52 H366].
destruct H366 as [x53 H367].
destruct H367 as [H368 H369].
destruct H369 as [H370 H371].
destruct H371 as [H372 H373].
destruct H373 as [H374 H375].
destruct H375 as [H376 H377].
destruct H377 as [H378 H379].
destruct H379 as [H380 H381].
destruct H381 as [H382 H383].
destruct H383 as [H384 H385].
destruct H385 as [H386 H387].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H388 by exact H32.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G F u) /\ ((euclidean__axioms.Col G F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B G F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp10 by exact H388.
destruct __TmpHyp10 as [x54 H389].
destruct H389 as [x55 H390].
destruct H390 as [x56 H391].
destruct H391 as [x57 H392].
destruct H392 as [x58 H393].
destruct H393 as [H394 H395].
destruct H395 as [H396 H397].
destruct H397 as [H398 H399].
destruct H399 as [H400 H401].
destruct H401 as [H402 H403].
destruct H403 as [H404 H405].
destruct H405 as [H406 H407].
destruct H407 as [H408 H409].
destruct H409 as [H410 H411].
destruct H411 as [H412 H413].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H414 by exact H31.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F G u) /\ ((euclidean__axioms.Col F G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp11 by exact H414.
destruct __TmpHyp11 as [x59 H415].
destruct H415 as [x60 H416].
destruct H416 as [x61 H417].
destruct H417 as [x62 H418].
destruct H418 as [x63 H419].
destruct H419 as [H420 H421].
destruct H421 as [H422 H423].
destruct H423 as [H424 H425].
destruct H425 as [H426 H427].
destruct H427 as [H428 H429].
destruct H429 as [H430 H431].
destruct H431 as [H432 H433].
destruct H433 as [H434 H435].
destruct H435 as [H436 H437].
destruct H437 as [H438 H439].
exact H124.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B D L) as H103.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A L) /\ ((euclidean__axioms.nCol D A L) /\ (euclidean__axioms.nCol B D L)))) as H103.
-------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC B D A L H99).
-------------------------------------------------------------------- destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
exact H109.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H104.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq D L) /\ ((euclidean__axioms.neq B L) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq L D) /\ (euclidean__axioms.neq L B)))))) as H104.
--------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct B D L H103).
--------------------------------------------------------------------- destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
exact H111.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M A) as H105.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A))) as H105.
---------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal L M A H16).
---------------------------------------------------------------------- destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
exact H106.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L M) as H106.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L A))) as H106.
----------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal L M A H16).
----------------------------------------------------------------------- destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
exact H109.
---------------------------------------------------------------------- assert (* Cut *) (D = D) as H107.
----------------------------------------------------------------------- apply (@logic.eq__refl Point D).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B B) as H108.
------------------------------------------------------------------------ right.
right.
left.
exact H100.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS B c M) as H109.
------------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween D B L A B M c H108 H95 H104 H97 H104 H105 H102 H80 H93).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B c C) as H110.
-------------------------------------------------------------------------- apply (@lemma__3__6b.lemma__3__6b B c M C H109 H10).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D B A) as H111.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D B L) /\ ((euclidean__axioms.nCol D L A) /\ ((euclidean__axioms.nCol B L A) /\ (euclidean__axioms.nCol D B A)))) as H111.
---------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC D B L A H101).
---------------------------------------------------------------------------- destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
exact H117.
--------------------------------------------------------------------------- assert (* Cut *) (~(B = c)) as H112.
---------------------------------------------------------------------------- intro H112.
assert (* Cut *) (euclidean__axioms.Col D B c) as H113.
----------------------------------------------------------------------------- right.
right.
left.
exact H112.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D c A) as H114.
------------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H80.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col c D B) as H115.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B D c) /\ ((euclidean__axioms.Col B c D) /\ ((euclidean__axioms.Col c D B) /\ ((euclidean__axioms.Col D c B) /\ (euclidean__axioms.Col c B D))))) as H115.
-------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D B c H113).
-------------------------------------------------------------------------------- destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
exact H120.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col c D A) as H116.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col c D A) /\ ((euclidean__axioms.Col c A D) /\ ((euclidean__axioms.Col A D c) /\ ((euclidean__axioms.Col D A c) /\ (euclidean__axioms.Col A c D))))) as H116.
--------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D c A H114).
--------------------------------------------------------------------------------- destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
exact H117.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D c) as H117.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq c A) /\ ((euclidean__axioms.neq D c) /\ (euclidean__axioms.neq D A))) as H117.
---------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D c A H80).
---------------------------------------------------------------------------------- destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
exact H120.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq c D) as H118.
---------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D c H117).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B A) as H119.
----------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point c (fun B0 => (euclidean__axioms.Triangle A B0 C) -> ((euclidean__defs.Per B0 A C) -> ((euclidean__defs.SQ A B0 F G) -> ((euclidean__axioms.TS G B0 A C) -> ((euclidean__defs.SQ B0 C E D) -> ((euclidean__axioms.TS D C B0 A) -> ((euclidean__defs.PG B0 M L D) -> ((euclidean__axioms.BetS B0 M C) -> ((euclidean__axioms.Col C B0 N) -> ((euclidean__axioms.nCol C B0 D) -> ((euclidean__defs.Per G A B0) -> ((euclidean__defs.Per A B0 F) -> ((euclidean__defs.Per F B0 A) -> ((euclidean__defs.Per D B0 C) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__defs.PG A B0 F G) -> ((euclidean__defs.Par A B0 F G) -> ((euclidean__defs.Par A B0 G F) -> ((euclidean__defs.TP A B0 G F) -> ((euclidean__defs.OS G F A B0) -> ((euclidean__defs.OS F G A B0) -> ((euclidean__axioms.TS G A B0 C) -> ((euclidean__axioms.TS F A B0 C) -> ((euclidean__axioms.Col A B0 a) -> ((euclidean__axioms.nCol A B0 F) -> ((euclidean__axioms.Col B0 A a) -> ((euclidean__defs.Par A G B0 F) -> ((euclidean__defs.Par A G F B0) -> ((euclidean__defs.Par F B0 A G) -> ((euclidean__defs.Par F B0 C G) -> ((euclidean__defs.Par F B0 G C) -> ((~(euclidean__defs.Meet F B0 G C)) -> ((euclidean__axioms.nCol A B0 F) -> ((euclidean__axioms.neq F B0) -> ((B0 = B0) -> ((euclidean__axioms.Col F B0 B0) -> ((euclidean__axioms.BetS B0 a A) -> ((euclidean__axioms.neq B0 a) -> ((euclidean__defs.Out B0 a A) -> ((euclidean__axioms.neq B0 F) -> ((euclidean__defs.Out B0 F F) -> ((euclidean__axioms.nCol A B0 F) -> ((euclidean__axioms.nCol F B0 A) -> ((euclidean__defs.CongA F B0 A F B0 A) -> ((euclidean__defs.Out B0 A a) -> ((euclidean__defs.CongA F B0 A F B0 a) -> ((euclidean__axioms.neq B0 C) -> ((euclidean__defs.Out B0 C C) -> ((euclidean__defs.CongA A B0 C A B0 C) -> ((euclidean__defs.CongA A B0 C a B0 C) -> ((euclidean__defs.SumA F B0 A A B0 C F B0 C) -> ((euclidean__axioms.Col C B0 c) -> ((euclidean__axioms.nCol C B0 D) -> ((euclidean__defs.PG B0 C E D) -> ((euclidean__defs.Par B0 D C E) -> ((euclidean__defs.Par C E B0 D) -> ((euclidean__defs.Par C E D B0) -> ((euclidean__axioms.Col B0 C c) -> ((euclidean__axioms.Col B0 M C) -> ((euclidean__axioms.Col C B0 M) -> ((euclidean__axioms.Col C B0 c) -> ((euclidean__axioms.neq C B0) -> ((euclidean__axioms.Col B0 M c) -> ((euclidean__defs.Par B0 D M L) -> ((euclidean__defs.Par B0 D A L) -> ((B0 = B0) -> ((euclidean__defs.Par D B0 L A) -> ((~(euclidean__defs.Meet D B0 L A)) -> ((euclidean__axioms.nCol B0 D L) -> ((euclidean__axioms.neq D B0) -> ((euclidean__axioms.Col D B0 B0) -> ((euclidean__axioms.BetS B0 c M) -> ((euclidean__axioms.BetS B0 c C) -> ((euclidean__axioms.nCol D B0 A) -> ((euclidean__axioms.Col D B0 c) -> ((euclidean__axioms.Col c D B0) -> (euclidean__axioms.Col D B0 A)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with (x := B).
------------------------------------------------------------------------------------intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
intro H139.
intro H140.
intro H141.
intro H142.
intro H143.
intro H144.
intro H145.
intro H146.
intro H147.
intro H148.
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
intro H181.
intro H182.
intro H183.
intro H184.
intro H185.
intro H186.
intro H187.
intro H188.
intro H189.
intro H190.
intro H191.
intro H192.
intro H193.
intro H194.
exact H114.

------------------------------------------------------------------------------------ exact H112.
------------------------------------------------------------------------------------ exact H.
------------------------------------------------------------------------------------ exact H0.
------------------------------------------------------------------------------------ exact H1.
------------------------------------------------------------------------------------ exact H2.
------------------------------------------------------------------------------------ exact H3.
------------------------------------------------------------------------------------ exact H4.
------------------------------------------------------------------------------------ exact H8.
------------------------------------------------------------------------------------ exact H10.
------------------------------------------------------------------------------------ exact H22.
------------------------------------------------------------------------------------ exact H23.
------------------------------------------------------------------------------------ exact H24.
------------------------------------------------------------------------------------ exact H26.
------------------------------------------------------------------------------------ exact H27.
------------------------------------------------------------------------------------ exact H28.
------------------------------------------------------------------------------------ exact H29.
------------------------------------------------------------------------------------ exact H30.
------------------------------------------------------------------------------------ exact H31.
------------------------------------------------------------------------------------ exact H32.
------------------------------------------------------------------------------------ exact H33.
------------------------------------------------------------------------------------ exact H34.
------------------------------------------------------------------------------------ exact H35.
------------------------------------------------------------------------------------ exact H36.
------------------------------------------------------------------------------------ exact H37.
------------------------------------------------------------------------------------ exact H42.
------------------------------------------------------------------------------------ exact H43.
------------------------------------------------------------------------------------ exact H44.
------------------------------------------------------------------------------------ exact H45.
------------------------------------------------------------------------------------ exact H46.
------------------------------------------------------------------------------------ exact H51.
------------------------------------------------------------------------------------ exact H52.
------------------------------------------------------------------------------------ exact H53.
------------------------------------------------------------------------------------ exact H54.
------------------------------------------------------------------------------------ exact H56.
------------------------------------------------------------------------------------ exact H58.
------------------------------------------------------------------------------------ exact H59.
------------------------------------------------------------------------------------ exact H60.
------------------------------------------------------------------------------------ exact H61.
------------------------------------------------------------------------------------ exact H62.
------------------------------------------------------------------------------------ exact H63.
------------------------------------------------------------------------------------ exact H64.
------------------------------------------------------------------------------------ exact H66.
------------------------------------------------------------------------------------ exact H67.
------------------------------------------------------------------------------------ exact H68.
------------------------------------------------------------------------------------ exact H69.
------------------------------------------------------------------------------------ exact H70.
------------------------------------------------------------------------------------ exact H71.
------------------------------------------------------------------------------------ exact H72.
------------------------------------------------------------------------------------ exact H74.
------------------------------------------------------------------------------------ exact H75.
------------------------------------------------------------------------------------ exact H76.
------------------------------------------------------------------------------------ exact H77.
------------------------------------------------------------------------------------ exact H82.
------------------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------------------ exact H84.
------------------------------------------------------------------------------------ exact H85.
------------------------------------------------------------------------------------ exact H86.
------------------------------------------------------------------------------------ exact H87.
------------------------------------------------------------------------------------ exact H88.
------------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------------ exact H91.
------------------------------------------------------------------------------------ exact H92.
------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------ exact H99.
------------------------------------------------------------------------------------ exact H100.
------------------------------------------------------------------------------------ exact H101.
------------------------------------------------------------------------------------ exact H102.
------------------------------------------------------------------------------------ exact H103.
------------------------------------------------------------------------------------ exact H104.
------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------ exact H109.
------------------------------------------------------------------------------------ exact H110.
------------------------------------------------------------------------------------ exact H111.
------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------ exact H115.
----------------------------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False D B A H111 H119).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B c C) as H113.
----------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 B c C).
------------------------------------------------------------------------------right.
right.
exact H110.

------------------------------------------------------------------------------ exact H112.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C c) as H114.
------------------------------------------------------------------------------ apply (@lemma__ray5.lemma__ray5 B c C H113).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol C B A) as H115.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H115.
-------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder A B C H29).
-------------------------------------------------------------------------------- destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
exact H123.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B A C B A) as H116.
-------------------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive C B A H115).
-------------------------------------------------------------------------------- assert (* Cut *) (A = A) as H117.
--------------------------------------------------------------------------------- apply (@logic.eq__refl Point A).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H118.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C)))))) as H118.
----------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct C B A H115).
----------------------------------------------------------------------------------- destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
exact H121.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H119.
----------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 B A A).
------------------------------------------------------------------------------------right.
left.
exact H117.

------------------------------------------------------------------------------------ exact H118.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B A c B A) as H120.
------------------------------------------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper C B A C B A c A H116 H114 H119).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol C D B) as H121.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C E D) /\ ((euclidean__axioms.nCol C D B) /\ ((euclidean__axioms.nCol E D B) /\ (euclidean__axioms.nCol C E B)))) as H121.
-------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC C E D B H87).
-------------------------------------------------------------------------------------- destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H124.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D B C) as H122.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol D B C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol C B D) /\ (euclidean__axioms.nCol B D C))))) as H122.
--------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder C D B H121).
--------------------------------------------------------------------------------------- destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
exact H125.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B C D B C) as H123.
--------------------------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive D B C H122).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H124.
---------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D B H104).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B D D) as H125.
----------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 B D D).
------------------------------------------------------------------------------------------right.
left.
exact H107.

------------------------------------------------------------------------------------------ exact H124.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B C D B c) as H126.
------------------------------------------------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper D B C D B C D c H123 H125 H114).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.SumA D B C C B A D B A) as H127.
------------------------------------------------------------------------------------------- exists c.
split.
-------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------- exact H120.
--------------------------------------------------------------------------------------------- exact H80.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B A D B C) as H128.
-------------------------------------------------------------------------------------------- apply (@lemma__Euclid4.lemma__Euclid4 F B A D B C H27 H28).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C C B A) as H129.
--------------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A B C H29).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B C D B A) as H130.
---------------------------------------------------------------------------------------------- apply (@lemma__angleaddition.lemma__angleaddition F B A A B C F B C D B C C B A D B A H77 H128 H129 H127).
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B A F B C) as H131.
----------------------------------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric F B C D B A H130).
----------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C B F)) as H132.
------------------------------------------------------------------------------------------------ intro H132.
assert (* Cut *) (euclidean__axioms.Col F B C) as H133.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B C F) /\ ((euclidean__axioms.Col B F C) /\ ((euclidean__axioms.Col F C B) /\ ((euclidean__axioms.Col C F B) /\ (euclidean__axioms.Col F B C))))) as H133.
-------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C B F H132).
-------------------------------------------------------------------------------------------------- destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
exact H141.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per C B A) as H134.
-------------------------------------------------------------------------------------------------- apply (@lemma__collinearright.lemma__collinearright F B C A H27 H133 H92).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Per C B A)) as H135.
--------------------------------------------------------------------------------------------------- apply (@lemma__8__7.lemma__8__7 C A B H0).
--------------------------------------------------------------------------------------------------- apply (@H135 H134).
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol F B C) as H133.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C B F) as H133.
-------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol C B F H132).
-------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B C F) /\ ((euclidean__axioms.nCol B F C) /\ ((euclidean__axioms.nCol F C B) /\ ((euclidean__axioms.nCol C F B) /\ (euclidean__axioms.nCol F B C))))) as H134.
--------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder C B F H133).
--------------------------------------------------------------------------------------------------- destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
exact H142.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B C C B F) as H134.
-------------------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA F B C H133).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B A C B F) as H135.
--------------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive D B A F B C C B F H131 H134).
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B B F) as H136.
---------------------------------------------------------------------------------------------------- destruct H3 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H1 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
exact H150.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B F B) as H137.
----------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B A F B) /\ ((euclidean__axioms.Cong B A B F) /\ (euclidean__axioms.Cong A B F B))) as H137.
------------------------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip A B B F H136).
------------------------------------------------------------------------------------------------------ destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
exact H141.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F B A B) as H138.
------------------------------------------------------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric F A B B H137).
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B F B A) as H139.
------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B F B A) /\ ((euclidean__axioms.Cong B F A B) /\ (euclidean__axioms.Cong F B B A))) as H139.
-------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip F B A B H138).
-------------------------------------------------------------------------------------------------------- destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
exact H140.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B A B F) as H140.
-------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B B F A H139).
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C D B) as H141.
--------------------------------------------------------------------------------------------------------- destruct H3 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H1 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
exact H145.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D B B C) as H142.
---------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D B C B H141).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D B C) as H143.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B D C B) /\ ((euclidean__axioms.Cong B D B C) /\ (euclidean__axioms.Cong D B C B))) as H143.
------------------------------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip D B B C H142).
------------------------------------------------------------------------------------------------------------ destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
exact H146.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong D A C F) /\ ((euclidean__defs.CongA B D A B C F) /\ (euclidean__defs.CongA B A D B F C))) as H144.
------------------------------------------------------------------------------------------------------------ apply (@proposition__04.proposition__04 B D A B C F H143 H140 H135).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A D F C) as H145.
------------------------------------------------------------------------------------------------------------- destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
assert (* Cut *) ((euclidean__axioms.Cong A D F C) /\ ((euclidean__axioms.Cong A D C F) /\ (euclidean__axioms.Cong D A F C))) as H149.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip D A C F H145).
-------------------------------------------------------------------------------------------------------------- destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
exact H150.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B F C B A D) as H146.
-------------------------------------------------------------------------------------------------------------- destruct H144 as [H146 H147].
destruct H147 as [H148 H149].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric B A D B F C H149).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B A D) as H147.
--------------------------------------------------------------------------------------------------------------- destruct H144 as [H147 H148].
destruct H148 as [H149 H150].
apply (@euclidean__tactics.nCol__notCol B A D).
----------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col B A D).
-----------------------------------------------------------------------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC B F C B A D H146).


--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B D) as H148.
---------------------------------------------------------------------------------------------------------------- destruct H144 as [H148 H149].
destruct H149 as [H150 H151].
assert (* Cut *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B D A) /\ (euclidean__axioms.nCol D A B))))) as H152.
----------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder B A D H147).
----------------------------------------------------------------------------------------------------------------- destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
exact H153.
---------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.Triangle A B D) as H149 by exact H148.
assert (* Cut *) (euclidean__axioms.Cong__3 A B D F B C) as H150.
----------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------- exact H143.
------------------------------------------------------------------------------------------------------------------- exact H145.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B D F B C) as H151.
------------------------------------------------------------------------------------------------------------------ destruct H144 as [H151 H152].
destruct H152 as [H153 H154].
apply (@euclidean__axioms.axiom__congruentequal A B D F B C H150).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par B M L D) as H152.
------------------------------------------------------------------------------------------------------------------- destruct H144 as [H152 H153].
destruct H153 as [H154 H155].
destruct H84 as [H156 H157].
destruct H30 as [H158 H159].
destruct H12 as [H160 H161].
destruct H8 as [H162 H163].
exact H162.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B D M L) as H153.
-------------------------------------------------------------------------------------------------------------------- destruct H144 as [H153 H154].
destruct H154 as [H155 H156].
destruct H84 as [H157 H158].
destruct H30 as [H159 H160].
destruct H12 as [H161 H162].
destruct H8 as [H163 H164].
exact H94.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M L B D) as H154.
--------------------------------------------------------------------------------------------------------------------- destruct H144 as [H154 H155].
destruct H155 as [H156 H157].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric B D M L H153).
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M B D L) as H155.
---------------------------------------------------------------------------------------------------------------------- destruct H144 as [H155 H156].
destruct H156 as [H157 H158].
assert (* Cut *) ((euclidean__defs.Par M B L D) /\ ((euclidean__defs.Par B M D L) /\ (euclidean__defs.Par M B D L))) as H159.
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip B M L D H152).
----------------------------------------------------------------------------------------------------------------------- destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
exact H163.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG M B D L) as H156.
----------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------ exact H155.
------------------------------------------------------------------------------------------------------------------------ exact H154.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M L A) as H157.
------------------------------------------------------------------------------------------------------------------------ destruct H144 as [H157 H158].
destruct H158 as [H159 H160].
assert (* Cut *) ((euclidean__axioms.Col B D B) /\ ((euclidean__axioms.Col B B D) /\ ((euclidean__axioms.Col B D B) /\ ((euclidean__axioms.Col D B B) /\ (euclidean__axioms.Col B B D))))) as H161.
------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D B B H108).
------------------------------------------------------------------------------------------------------------------------- destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
exact H96.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET M B D A B D) as H158.
------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H158 H159].
destruct H159 as [H160 H161].
apply (@proposition__41.proposition__41 M B D L A H156 H157).
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG A B F G) as H159.
-------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H159 H160].
destruct H160 as [H161 H162].
exact H30.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG B A G F) as H160.
--------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H160 H161].
destruct H161 as [H162 H163].
apply (@lemma__PGflip.lemma__PGflip A B F G H159).
--------------------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.Col G A C) as H161 by exact H47.
assert (* Cut *) (euclidean__axioms.Col A G C) as H162.
---------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H162 H163].
destruct H163 as [H164 H165].
assert (* Cut *) ((euclidean__axioms.Col A G C) /\ ((euclidean__axioms.Col A C G) /\ ((euclidean__axioms.Col C G A) /\ ((euclidean__axioms.Col G C A) /\ (euclidean__axioms.Col C A G))))) as H166.
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G A C H161).
----------------------------------------------------------------------------------------------------------------------------- destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
exact H167.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B F C B F) as H163.
----------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H163 H164].
destruct H164 as [H165 H166].
apply (@proposition__41.proposition__41 A B F G C H159 H162).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B F F B C) as H164.
------------------------------------------------------------------------------------------------------------------------------ destruct H144 as [H164 H165].
destruct H165 as [H166 H167].
assert (* Cut *) ((euclidean__axioms.ET A B F B F C) /\ ((euclidean__axioms.ET A B F C F B) /\ ((euclidean__axioms.ET A B F B C F) /\ ((euclidean__axioms.ET A B F F B C) /\ (euclidean__axioms.ET A B F F C B))))) as H168.
------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation A B F C B F H163).
------------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
exact H175.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET F B C A B D) as H165.
------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H165 H166].
destruct H166 as [H167 H168].
apply (@euclidean__axioms.axiom__ETsymmetric A B D F B C H151).
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B F A B D) as H166.
-------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H166 H167].
destruct H167 as [H168 H169].
apply (@euclidean__axioms.axiom__ETtransitive A B F A B D F B C H164 H165).
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B D M B D) as H167.
--------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H167 H168].
destruct H168 as [H169 H170].
apply (@euclidean__axioms.axiom__ETsymmetric M B D A B D H158).
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B F M B D) as H168.
---------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H168 H169].
destruct H169 as [H170 H171].
apply (@euclidean__axioms.axiom__ETtransitive A B F M B D A B D H166 H167).
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 A B F F G A) as H169.
----------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H169 H170].
destruct H170 as [H171 H172].
assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H173.
------------------------------------------------------------------------------------------------------------------------------------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__34.proposition__34 A0 B0 C0 D0 __).
------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H174.
------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@H173 A0 B0 C0 D0 __).
-------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H175.
-------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@H174 A0 B0 C0 D0 __).
--------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H176.
--------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@H175 A0 B0 C0 D0 __).
---------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@H176 B F A G H160).
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B F F G A) as H170.
------------------------------------------------------------------------------------------------------------------------------------ destruct H144 as [H170 H171].
destruct H171 as [H172 H173].
apply (@euclidean__axioms.axiom__congruentequal A B F F G A H169).
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.PG B M L D) as H171.
------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H171 H172].
destruct H172 as [H173 H174].
exact H8.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong__3 M B D D L M) as H172.
-------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H172 H173].
destruct H173 as [H174 H175].
assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H176.
--------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__34.proposition__34 A0 B0 C0 D0 __).
---------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H177.
---------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
----------------------------------------------------------------------------------------------------------------------------------------- apply (@H176 A0 B0 C0 D0 __).
----------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H178.
----------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
------------------------------------------------------------------------------------------------------------------------------------------ apply (@H177 A0 B0 C0 D0 __).
------------------------------------------------------------------------------------------------------------------------------------------ destruct __0 as [__0 __1].
exact __1.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H179.
------------------------------------------------------------------------------------------------------------------------------------------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
------------------------------------------------------------------------------------------------------------------------------------------- apply (@H178 A0 B0 C0 D0 __).
------------------------------------------------------------------------------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------------------------------------------------------------------------------------------------ apply (@H179 B D M L H171).
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET M B D D L M) as H173.
--------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H173 H174].
destruct H174 as [H175 H176].
apply (@euclidean__axioms.axiom__congruentequal M B D D L M H172).
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F G A A B F) as H174.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H174 H175].
destruct H175 as [H176 H177].
apply (@euclidean__axioms.axiom__ETsymmetric A B F F G A H170).
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F G A A B D) as H175.
----------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H175 H176].
destruct H176 as [H177 H178].
apply (@euclidean__axioms.axiom__ETtransitive F G A A B D A B F H174 H166).
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F G A M B D) as H176.
------------------------------------------------------------------------------------------------------------------------------------------ destruct H144 as [H176 H177].
destruct H177 as [H178 H179].
apply (@euclidean__axioms.axiom__ETtransitive F G A M B D A B D H175 H167).
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET F G A D L M) as H177.
------------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H177 H178].
destruct H178 as [H179 H180].
apply (@euclidean__axioms.axiom__ETtransitive F G A D L M M B D H176 H173).
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F G A D M L) as H178.
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H178 H179].
destruct H179 as [H180 H181].
assert (* Cut *) ((euclidean__axioms.ET F G A L M D) /\ ((euclidean__axioms.ET F G A D M L) /\ ((euclidean__axioms.ET F G A L D M) /\ ((euclidean__axioms.ET F G A M L D) /\ (euclidean__axioms.ET F G A M D L))))) as H182.
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation F G A D L M H177).
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
exact H185.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D M L F G A) as H179.
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H179 H180].
destruct H180 as [H181 H182].
apply (@euclidean__axioms.axiom__ETsymmetric F G A D M L H178).
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D M L F A G) as H180.
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H180 H181].
destruct H181 as [H182 H183].
assert (* Cut *) ((euclidean__axioms.ET D M L G A F) /\ ((euclidean__axioms.ET D M L F A G) /\ ((euclidean__axioms.ET D M L G F A) /\ ((euclidean__axioms.ET D M L A G F) /\ (euclidean__axioms.ET D M L A F G))))) as H184.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation D M L F G A H179).
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
exact H187.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F A G D M L) as H181.
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H181 H182].
destruct H182 as [H183 H184].
apply (@euclidean__axioms.axiom__ETsymmetric D M L F A G H180).
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B F D M B) as H182.
------------------------------------------------------------------------------------------------------------------------------------------------ destruct H144 as [H182 H183].
destruct H183 as [H184 H185].
assert (* Cut *) ((euclidean__axioms.ET A B F B D M) /\ ((euclidean__axioms.ET A B F M D B) /\ ((euclidean__axioms.ET A B F B M D) /\ ((euclidean__axioms.ET A B F D B M) /\ (euclidean__axioms.ET A B F D M B))))) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation A B F M B D H168).
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
exact H194.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET D M B A B F) as H183.
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H183 H184].
destruct H184 as [H185 H186].
apply (@euclidean__axioms.axiom__ETsymmetric A B F D M B H182).
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D M B F A B) as H184.
-------------------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H184 H185].
destruct H185 as [H186 H187].
assert (* Cut *) ((euclidean__axioms.ET D M B B F A) /\ ((euclidean__axioms.ET D M B A F B) /\ ((euclidean__axioms.ET D M B B A F) /\ ((euclidean__axioms.ET D M B F B A) /\ (euclidean__axioms.ET D M B F A B))))) as H188.
--------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation D M B A B F H183).
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
exact H196.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F A B D M B) as H185.
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H185 H186].
destruct H186 as [H187 H188].
apply (@euclidean__axioms.axiom__ETsymmetric D M B F A B H184).
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists m, (euclidean__defs.Midpoint A m F) /\ (euclidean__defs.Midpoint B m G)) as H186.
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H144 as [H186 H187].
destruct H187 as [H188 H189].
apply (@lemma__diagonalsbisect.lemma__diagonalsbisect A B F G H159).
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [m H187].
destruct H187 as [H188 H189].
destruct H144 as [H190 H191].
destruct H191 as [H192 H193].
assert (* Cut *) (euclidean__axioms.BetS A m F) as H194.
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H189 as [H194 H195].
destruct H188 as [H196 H197].
exact H196.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B m G) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H189 as [H195 H196].
destruct H188 as [H197 H198].
exact H195.
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS F m A) as H196.
------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A m F H194).
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists n, (euclidean__defs.Midpoint B n L) /\ (euclidean__defs.Midpoint M n D)) as H197.
-------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__diagonalsbisect.lemma__diagonalsbisect B M L D H171).
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H197 as [n H198].
destruct H198 as [H199 H200].
assert (* Cut *) (euclidean__axioms.BetS B n L) as H201.
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H201 H202].
destruct H199 as [H203 H204].
destruct H189 as [H205 H206].
destruct H188 as [H207 H208].
exact H203.
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS M n D) as H202.
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H200 as [H202 H203].
destruct H199 as [H204 H205].
destruct H189 as [H206 H207].
destruct H188 as [H208 H209].
exact H202.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D n M) as H203.
----------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry M n D H202).
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M n D) as H204.
------------------------------------------------------------------------------------------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H202.
------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D M n) as H205.
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col n M D) /\ ((euclidean__axioms.Col n D M) /\ ((euclidean__axioms.Col D M n) /\ ((euclidean__axioms.Col M D n) /\ (euclidean__axioms.Col D n M))))) as H205.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder M n D H204).
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H205 as [H206 H207].
destruct H207 as [H208 H209].
destruct H209 as [H210 H211].
destruct H211 as [H212 H213].
exact H210.
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B M D) as H206.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B M L) /\ ((euclidean__axioms.nCol B L D) /\ ((euclidean__axioms.nCol M L D) /\ (euclidean__axioms.nCol B M D)))) as H206.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC B M L D H152).
--------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H206 as [H207 H208].
destruct H208 as [H209 H210].
destruct H210 as [H211 H212].
exact H212.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D M B) as H207.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol M B D) /\ ((euclidean__axioms.nCol M D B) /\ ((euclidean__axioms.nCol D B M) /\ ((euclidean__axioms.nCol B D M) /\ (euclidean__axioms.nCol D M B))))) as H207.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder B M D H206).
---------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H207 as [H208 H209].
destruct H209 as [H210 H211].
destruct H211 as [H212 H213].
destruct H213 as [H214 H215].
exact H215.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF F B A G D B M L) as H208.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__paste3 F A B G m D M B L n H185 H181 H195).
-----------------------------------------------------------------------------------------------------------------------------------------------------------------left.
exact H196.

----------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H201.
-----------------------------------------------------------------------------------------------------------------------------------------------------------------left.
exact H203.

---------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF F B A G B M L D) as H209.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF F B A G B M L D) /\ ((euclidean__axioms.EF F B A G L M B D) /\ ((euclidean__axioms.EF F B A G M L D B) /\ ((euclidean__axioms.EF F B A G B D L M) /\ ((euclidean__axioms.EF F B A G L D B M) /\ ((euclidean__axioms.EF F B A G M B D L) /\ (euclidean__axioms.EF F B A G D L M B))))))) as H209.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__EFpermutation F B A G D B M L H208).
------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H209 as [H210 H211].
destruct H211 as [H212 H213].
destruct H213 as [H214 H215].
destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
destruct H219 as [H220 H221].
exact H210.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B M L D F B A G) as H210.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__EFsymmetric F B A G B M L D H209).
------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.EF B M L D A B F G) as H211.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.EF B M L D B A G F) /\ ((euclidean__axioms.EF B M L D G A B F) /\ ((euclidean__axioms.EF B M L D A G F B) /\ ((euclidean__axioms.EF B M L D B F G A) /\ ((euclidean__axioms.EF B M L D G F B A) /\ ((euclidean__axioms.EF B M L D A B F G) /\ (euclidean__axioms.EF B M L D F G A B))))))) as H211.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation B M L D F B A G H210).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H211 as [H212 H213].
destruct H213 as [H214 H215].
destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
destruct H219 as [H220 H221].
destruct H221 as [H222 H223].
exact H222.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B F G B M L D) as H212.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric B M L D A B F G H211).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- exists M.
exists L.
split.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H171.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H10.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H12.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H14.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H16.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H17.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H212.
Qed.
