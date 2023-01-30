Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__NCdistinct.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__crisscross.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Definition lemma__30helper : forall A B E F G H, (euclidean__defs.Par A B E F) -> ((euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS E H F) -> ((~(euclidean__defs.CR A F G H)) -> (euclidean__defs.CR A E G H)))).
Proof.
intro A.
intro B.
intro E.
intro F.
intro G.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
assert (* Cut *) (euclidean__axioms.Col A G B) as H4.
- right.
right.
right.
right.
left.
exact H1.
- assert (* Cut *) (euclidean__axioms.Col E H F) as H5.
-- right.
right.
right.
right.
left.
exact H2.
-- assert (* Cut *) (euclidean__axioms.Col B A G) as H6.
--- assert (* Cut *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H6.
---- apply (@lemma__collinearorder.lemma__collinearorder A G B H4).
---- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H11.
--- assert (* Cut *) (euclidean__axioms.Col E F H) as H7.
---- assert (* Cut *) ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E))))) as H7.
----- apply (@lemma__collinearorder.lemma__collinearorder E H F H5).
----- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H14.
---- assert (* Cut *) (euclidean__axioms.neq H F) as H8.
----- assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H8.
------ apply (@lemma__betweennotequal.lemma__betweennotequal E H F H2).
------ destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H9.
----- assert (* Cut *) (euclidean__axioms.neq E H) as H9.
------ assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H9.
------- apply (@lemma__betweennotequal.lemma__betweennotequal E H F H2).
------- destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
exact H12.
------ assert (* Cut *) (euclidean__axioms.neq H E) as H10.
------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E H H9).
------- assert (* Cut *) (euclidean__axioms.neq F H) as H11.
-------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric H F H8).
-------- assert (* Cut *) (euclidean__axioms.neq A G) as H12.
--------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H12.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal A G B H1).
---------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H15.
--------- assert (* Cut *) (euclidean__axioms.neq G A) as H13.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A G H12).
---------- assert (* Cut *) (euclidean__defs.Par A B F E) as H14.
----------- assert (* Cut *) ((euclidean__defs.Par B A E F) /\ ((euclidean__defs.Par A B F E) /\ (euclidean__defs.Par B A F E))) as H14.
------------ apply (@lemma__parallelflip.lemma__parallelflip A B E F H0).
------------ destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H17.
----------- assert (* Cut *) (euclidean__axioms.Col F E H) as H15.
------------ assert (* Cut *) ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col F H E) /\ ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col E H F) /\ (euclidean__axioms.Col H F E))))) as H15.
------------- apply (@lemma__collinearorder.lemma__collinearorder E F H H7).
------------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H16.
------------ assert (* Cut *) (euclidean__defs.Par A B H E) as H16.
------------- apply (@lemma__collinearparallel.lemma__collinearparallel A B H F E H14 H15 H10).
------------- assert (* Cut *) (euclidean__defs.Par A B H F) as H17.
-------------- apply (@lemma__collinearparallel.lemma__collinearparallel A B H E F H0 H7 H8).
-------------- assert (* Cut *) (euclidean__defs.Par H F A B) as H18.
--------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A B H F H17).
--------------- assert (* Cut *) (euclidean__defs.Par H F B A) as H19.
---------------- assert (* Cut *) ((euclidean__defs.Par F H A B) /\ ((euclidean__defs.Par H F B A) /\ (euclidean__defs.Par F H B A))) as H19.
----------------- apply (@lemma__parallelflip.lemma__parallelflip H F A B H18).
----------------- destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H22.
---------------- assert (* Cut *) (euclidean__defs.Par H F G A) as H20.
----------------- apply (@lemma__collinearparallel.lemma__collinearparallel H F G B A H19 H6 H13).
----------------- assert (* Cut *) (euclidean__defs.Par H F A G) as H21.
------------------ assert (* Cut *) ((euclidean__defs.Par F H G A) /\ ((euclidean__defs.Par H F A G) /\ (euclidean__defs.Par F H A G))) as H21.
------------------- apply (@lemma__parallelflip.lemma__parallelflip H F G A H20).
------------------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H24.
------------------ assert (* Cut *) (euclidean__defs.Par A G H F) as H22.
------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric H F A G H21).
------------------- assert (* Cut *) (euclidean__defs.Par A G F H) as H23.
-------------------- assert (* Cut *) ((euclidean__defs.Par G A H F) /\ ((euclidean__defs.Par A G F H) /\ (euclidean__defs.Par G A F H))) as H23.
--------------------- apply (@lemma__parallelflip.lemma__parallelflip A G H F H22).
--------------------- destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H26.
-------------------- assert (* Cut *) (euclidean__defs.CR A H F G) as H24.
--------------------- apply (@lemma__crisscross.lemma__crisscross A F G H H23 H3).
--------------------- assert (exists M, (euclidean__axioms.BetS A M H) /\ (euclidean__axioms.BetS F M G)) as H25 by exact H24.
destruct H25 as [M H26].
destruct H26 as [H27 H28].
assert (* Cut *) (euclidean__axioms.neq A H) as H29.
---------------------- assert (* Cut *) ((euclidean__axioms.neq M H) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A H))) as H29.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A M H H27).
----------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H33.
---------------------- assert (* Cut *) (euclidean__axioms.neq F G) as H30.
----------------------- assert (* Cut *) ((euclidean__axioms.neq M G) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F G))) as H30.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal F M G H28).
------------------------ destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H34.
----------------------- assert (* Cut *) (euclidean__axioms.BetS G M F) as H31.
------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry F M G H28).
------------------------ assert (* Cut *) (euclidean__axioms.nCol A E F) as H32.
------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol A E F) /\ ((euclidean__axioms.nCol B E F) /\ (euclidean__axioms.nCol A B F)))) as H32.
-------------------------- apply (@lemma__parallelNC.lemma__parallelNC A B E F H0).
-------------------------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H35.
------------------------- assert (* Cut *) (euclidean__axioms.nCol F E A) as H33.
-------------------------- assert (* Cut *) ((euclidean__axioms.nCol E A F) /\ ((euclidean__axioms.nCol E F A) /\ ((euclidean__axioms.nCol F A E) /\ ((euclidean__axioms.nCol A F E) /\ (euclidean__axioms.nCol F E A))))) as H33.
--------------------------- apply (@lemma__NCorder.lemma__NCorder A E F H32).
--------------------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H41.
-------------------------- assert (* Cut *) (euclidean__axioms.BetS F H E) as H34.
--------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E H F H2).
--------------------------- assert (* Cut *) (exists p, (euclidean__axioms.BetS A p E) /\ (euclidean__axioms.BetS F M p)) as H35.
---------------------------- apply (@euclidean__axioms.postulate__Pasch__outer A F H M E H27 H34 H33).
---------------------------- destruct H35 as [p H36].
destruct H36 as [H37 H38].
assert (* Cut *) (euclidean__axioms.nCol A G H) as H39.
----------------------------- assert (* Cut *) ((euclidean__axioms.nCol A G F) /\ ((euclidean__axioms.nCol A F H) /\ ((euclidean__axioms.nCol G F H) /\ (euclidean__axioms.nCol A G H)))) as H39.
------------------------------ apply (@lemma__parallelNC.lemma__parallelNC A G F H H23).
------------------------------ destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H45.
----------------------------- assert (* Cut *) (euclidean__axioms.nCol A H G) as H40.
------------------------------ assert (* Cut *) ((euclidean__axioms.nCol G A H) /\ ((euclidean__axioms.nCol G H A) /\ ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A))))) as H40.
------------------------------- apply (@lemma__NCorder.lemma__NCorder A G H H39).
------------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H47.
------------------------------ assert (* Cut *) (euclidean__axioms.Col F M G) as H41.
------------------------------- right.
right.
right.
right.
left.
exact H28.
------------------------------- assert (* Cut *) (euclidean__axioms.Col F M p) as H42.
-------------------------------- right.
right.
right.
right.
left.
exact H38.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq F M) as H43.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq M p) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p))) as H43.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal F M p H38).
---------------------------------- destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H46.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col M G p) as H44.
---------------------------------- apply (@euclidean__tactics.not__nCol__Col M G p).
-----------------------------------intro H44.
apply (@euclidean__tactics.Col__nCol__False M G p H44).
------------------------------------apply (@lemma__collinear4.lemma__collinear4 F M G p H41 H42 H43).


---------------------------------- assert (* Cut *) (euclidean__axioms.Col M p G) as H45.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col G M p) /\ ((euclidean__axioms.Col G p M) /\ ((euclidean__axioms.Col p M G) /\ ((euclidean__axioms.Col M p G) /\ (euclidean__axioms.Col p G M))))) as H45.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder M G p H44).
------------------------------------ destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H52.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col M p F) as H46.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col M F p) /\ ((euclidean__axioms.Col M p F) /\ ((euclidean__axioms.Col p F M) /\ ((euclidean__axioms.Col F p M) /\ (euclidean__axioms.Col p M F))))) as H46.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F M p H42).
------------------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H49.
------------------------------------ assert (* Cut *) (euclidean__axioms.neq M p) as H47.
------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M p) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p))) as H47.
-------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal F M p H38).
-------------------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H48.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col p G F) as H48.
-------------------------------------- apply (@euclidean__tactics.not__nCol__Col p G F).
---------------------------------------intro H48.
apply (@euclidean__tactics.Col__nCol__False p G F H48).
----------------------------------------apply (@lemma__collinear4.lemma__collinear4 M p G F H45 H46 H47).


-------------------------------------- assert (* Cut *) (euclidean__axioms.Col G F p) as H49.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G p F) /\ ((euclidean__axioms.Col G F p) /\ ((euclidean__axioms.Col F p G) /\ ((euclidean__axioms.Col p F G) /\ (euclidean__axioms.Col F G p))))) as H49.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder p G F H48).
---------------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H52.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col H F E) as H50.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E F H) /\ ((euclidean__axioms.Col E H F) /\ ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F H E) /\ (euclidean__axioms.Col H E F))))) as H50.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F E H H15).
----------------------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H55.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq A B) as H51.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H51.
------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A G B H1).
------------------------------------------ destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H55.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq A G) as H52.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq M p) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F p))) as H52.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal F M p H38).
------------------------------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H12.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq E F) as H53.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H53.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E H F H2).
-------------------------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H57.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F E) as H54.
-------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E F H53).
-------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B H E)) as H55.
--------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H55 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H55.
destruct __TmpHyp as [x H56].
destruct H56 as [x0 H57].
destruct H57 as [x1 H58].
destruct H58 as [x2 H59].
destruct H59 as [x3 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H81 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H81.
destruct __TmpHyp0 as [x4 H82].
destruct H82 as [x5 H83].
destruct H83 as [x6 H84].
destruct H84 as [x7 H85].
destruct H85 as [x8 H86].
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
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H107 by exact H21.
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H107.
destruct __TmpHyp1 as [x9 H108].
destruct H108 as [x10 H109].
destruct H109 as [x11 H110].
destruct H110 as [x12 H111].
destruct H111 as [x13 H112].
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
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H133 by exact H20.
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H133.
destruct __TmpHyp2 as [x14 H134].
destruct H134 as [x15 H135].
destruct H135 as [x16 H136].
destruct H136 as [x17 H137].
destruct H137 as [x18 H138].
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
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H159 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H159.
destruct __TmpHyp3 as [x19 H160].
destruct H160 as [x20 H161].
destruct H161 as [x21 H162].
destruct H162 as [x22 H163].
destruct H163 as [x23 H164].
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
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H185 by exact H18.
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H185.
destruct __TmpHyp4 as [x24 H186].
destruct H186 as [x25 H187].
destruct H187 as [x26 H188].
destruct H188 as [x27 H189].
destruct H189 as [x28 H190].
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
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H211 by exact H17.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H211.
destruct __TmpHyp5 as [x29 H212].
destruct H212 as [x30 H213].
destruct H213 as [x31 H214].
destruct H214 as [x32 H215].
destruct H215 as [x33 H216].
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
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H237 by exact H16.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H237.
destruct __TmpHyp6 as [x34 H238].
destruct H238 as [x35 H239].
destruct H239 as [x36 H240].
destruct H240 as [x37 H241].
destruct H241 as [x38 H242].
destruct H242 as [H243 H244].
destruct H244 as [H245 H246].
destruct H246 as [H247 H248].
destruct H248 as [H249 H250].
destruct H250 as [H251 H252].
destruct H252 as [H253 H254].
destruct H254 as [H255 H256].
destruct H256 as [H257 H258].
destruct H258 as [H259 H260].
destruct H260 as [H261 H262].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H263 by exact H14.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H263.
destruct __TmpHyp7 as [x39 H264].
destruct H264 as [x40 H265].
destruct H265 as [x41 H266].
destruct H266 as [x42 H267].
destruct H267 as [x43 H268].
destruct H268 as [H269 H270].
destruct H270 as [H271 H272].
destruct H272 as [H273 H274].
destruct H274 as [H275 H276].
destruct H276 as [H277 H278].
destruct H278 as [H279 H280].
destruct H280 as [H281 H282].
destruct H282 as [H283 H284].
destruct H284 as [H285 H286].
destruct H286 as [H287 H288].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H289 by exact H0.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H289.
destruct __TmpHyp8 as [x44 H290].
destruct H290 as [x45 H291].
destruct H291 as [x46 H292].
destruct H292 as [x47 H293].
destruct H293 as [x48 H294].
destruct H294 as [H295 H296].
destruct H296 as [H297 H298].
destruct H298 as [H299 H300].
destruct H300 as [H301 H302].
destruct H302 as [H303 H304].
destruct H304 as [H305 H306].
destruct H306 as [H307 H308].
destruct H308 as [H309 H310].
destruct H310 as [H311 H312].
destruct H312 as [H313 H314].
exact H259.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G p F) as H56.
---------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween A B H E G F p H4 H50 H51 H10 H52 H54 H55 H37 H49).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F p G) as H57.
----------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry G p F H56).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS M p G) as H58.
------------------------------------------------ apply (@lemma__3__6a.lemma__3__6a F M p G H38 H57).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS G p M) as H59.
------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry M p G H58).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A G H) as H60.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A G F) /\ ((euclidean__axioms.nCol A F H) /\ ((euclidean__axioms.nCol G F H) /\ (euclidean__axioms.nCol A G H)))) as H60.
--------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC A G F H H23).
--------------------------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H39.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A H G) as H61.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G A H) /\ ((euclidean__axioms.nCol G H A) /\ ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A H G) /\ (euclidean__axioms.nCol H G A))))) as H61.
---------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder A G H H60).
---------------------------------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H68.
--------------------------------------------------- assert (* Cut *) (exists m, (euclidean__axioms.BetS G m H) /\ (euclidean__axioms.BetS A p m)) as H62.
---------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer G A M p H H59 H27 H61).
---------------------------------------------------- destruct H62 as [m H63].
destruct H63 as [H64 H65].
assert (* Cut *) (euclidean__axioms.Col A p m) as H66.
----------------------------------------------------- right.
right.
right.
right.
left.
exact H65.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A p E) as H67.
------------------------------------------------------ right.
right.
right.
right.
left.
exact H37.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A p) as H68.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq p m) /\ ((euclidean__axioms.neq A p) /\ (euclidean__axioms.neq A m))) as H68.
-------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A p m H65).
-------------------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H71.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p m E) as H69.
-------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col p m E).
---------------------------------------------------------intro H69.
apply (@euclidean__tactics.Col__nCol__False p m E H69).
----------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 A p m E H66 H67 H68).


-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col p m A) as H70.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col p A m) /\ ((euclidean__axioms.Col p m A) /\ ((euclidean__axioms.Col m A p) /\ ((euclidean__axioms.Col A m p) /\ (euclidean__axioms.Col m p A))))) as H70.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A p m H66).
---------------------------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H73.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq p m) as H71.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq p m) /\ ((euclidean__axioms.neq A p) /\ (euclidean__axioms.neq A m))) as H71.
----------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A p m H65).
----------------------------------------------------------- destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H72.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m E A) as H72.
----------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col m E A).
------------------------------------------------------------intro H72.
apply (@euclidean__tactics.Col__nCol__False m E A H72).
-------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 p m E A H69 H70 H71).


----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E m) as H73.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col E m A) /\ ((euclidean__axioms.Col E A m) /\ ((euclidean__axioms.Col A m E) /\ ((euclidean__axioms.Col m A E) /\ (euclidean__axioms.Col A E m))))) as H73.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder m E A H72).
------------------------------------------------------------- destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
exact H81.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A E) as H74.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A F)))))) as H74.
-------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct F E A H33).
-------------------------------------------------------------- destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
exact H83.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G H) as H75.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A H) /\ ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H A) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G A)))))) as H75.
--------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct A H G H61).
--------------------------------------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H84.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G B) as H76.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H76.
---------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A G B H1).
---------------------------------------------------------------- destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H77.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H77.
---------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G B H76).
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H F B G) as H78.
----------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel H F B A G H21 H4 H77).
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B G H F) as H79.
------------------------------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric H F B G H78).
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par G B F H) as H80.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par G B H F) /\ ((euclidean__defs.Par B G F H) /\ (euclidean__defs.Par G B F H))) as H80.
-------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip B G H F H79).
-------------------------------------------------------------------- destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
exact H84.
------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet G B F H)) as H81.
-------------------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col G B U) /\ ((euclidean__axioms.Col G B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H81 by exact H80.
assert (exists U V u v X, (euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col G B U) /\ ((euclidean__axioms.Col G B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet G B F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H81.
destruct __TmpHyp as [x H82].
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
assert (exists U V u v X, (euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col B G U) /\ ((euclidean__axioms.Col B G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H107 by exact H79.
assert (exists U V u v X, (euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col B G U) /\ ((euclidean__axioms.Col B G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet B G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H107.
destruct __TmpHyp0 as [x4 H108].
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
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B G u) /\ ((euclidean__axioms.Col B G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H133 by exact H78.
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B G u) /\ ((euclidean__axioms.Col B G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H133.
destruct __TmpHyp1 as [x9 H134].
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
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H159 by exact H23.
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq F H) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F H u) /\ ((euclidean__axioms.Col F H v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G F H)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H159.
destruct __TmpHyp2 as [x14 H160].
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
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H185 by exact H22.
assert (exists U V u v X, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A G U) /\ ((euclidean__axioms.Col A G V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A G H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H185.
destruct __TmpHyp3 as [x19 H186].
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
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H211 by exact H21.
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A G u) /\ ((euclidean__axioms.Col A G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H211.
destruct __TmpHyp4 as [x24 H212].
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
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H237 by exact H20.
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col G A u) /\ ((euclidean__axioms.Col G A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F G A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H237.
destruct __TmpHyp5 as [x29 H238].
destruct H238 as [x30 H239].
destruct H239 as [x31 H240].
destruct H240 as [x32 H241].
destruct H241 as [x33 H242].
destruct H242 as [H243 H244].
destruct H244 as [H245 H246].
destruct H246 as [H247 H248].
destruct H248 as [H249 H250].
destruct H250 as [H251 H252].
destruct H252 as [H253 H254].
destruct H254 as [H255 H256].
destruct H256 as [H257 H258].
destruct H258 as [H259 H260].
destruct H260 as [H261 H262].
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H263 by exact H19.
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H263.
destruct __TmpHyp6 as [x34 H264].
destruct H264 as [x35 H265].
destruct H265 as [x36 H266].
destruct H266 as [x37 H267].
destruct H267 as [x38 H268].
destruct H268 as [H269 H270].
destruct H270 as [H271 H272].
destruct H272 as [H273 H274].
destruct H274 as [H275 H276].
destruct H276 as [H277 H278].
destruct H278 as [H279 H280].
destruct H280 as [H281 H282].
destruct H282 as [H283 H284].
destruct H284 as [H285 H286].
destruct H286 as [H287 H288].
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H289 by exact H18.
assert (exists U V u v X, (euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col H F U) /\ ((euclidean__axioms.Col H F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H F A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H289.
destruct __TmpHyp7 as [x39 H290].
destruct H290 as [x40 H291].
destruct H291 as [x41 H292].
destruct H292 as [x42 H293].
destruct H293 as [x43 H294].
destruct H294 as [H295 H296].
destruct H296 as [H297 H298].
destruct H298 as [H299 H300].
destruct H300 as [H301 H302].
destruct H302 as [H303 H304].
destruct H304 as [H305 H306].
destruct H306 as [H307 H308].
destruct H308 as [H309 H310].
destruct H310 as [H311 H312].
destruct H312 as [H313 H314].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H315 by exact H17.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H F u) /\ ((euclidean__axioms.Col H F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp8 by exact H315.
destruct __TmpHyp8 as [x44 H316].
destruct H316 as [x45 H317].
destruct H317 as [x46 H318].
destruct H318 as [x47 H319].
destruct H319 as [x48 H320].
destruct H320 as [H321 H322].
destruct H322 as [H323 H324].
destruct H324 as [H325 H326].
destruct H326 as [H327 H328].
destruct H328 as [H329 H330].
destruct H330 as [H331 H332].
destruct H332 as [H333 H334].
destruct H334 as [H335 H336].
destruct H336 as [H337 H338].
destruct H338 as [H339 H340].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H341 by exact H16.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq H E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col H E u) /\ ((euclidean__axioms.Col H E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B H E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp9 by exact H341.
destruct __TmpHyp9 as [x49 H342].
destruct H342 as [x50 H343].
destruct H343 as [x51 H344].
destruct H344 as [x52 H345].
destruct H345 as [x53 H346].
destruct H346 as [H347 H348].
destruct H348 as [H349 H350].
destruct H350 as [H351 H352].
destruct H352 as [H353 H354].
destruct H354 as [H355 H356].
destruct H356 as [H357 H358].
destruct H358 as [H359 H360].
destruct H360 as [H361 H362].
destruct H362 as [H363 H364].
destruct H364 as [H365 H366].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H367 by exact H14.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F E u) /\ ((euclidean__axioms.Col F E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B F E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp10 by exact H367.
destruct __TmpHyp10 as [x54 H368].
destruct H368 as [x55 H369].
destruct H369 as [x56 H370].
destruct H370 as [x57 H371].
destruct H371 as [x58 H372].
destruct H372 as [H373 H374].
destruct H374 as [H375 H376].
destruct H376 as [H377 H378].
destruct H378 as [H379 H380].
destruct H380 as [H381 H382].
destruct H382 as [H383 H384].
destruct H384 as [H385 H386].
destruct H386 as [H387 H388].
destruct H388 as [H389 H390].
destruct H390 as [H391 H392].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H393 by exact H0.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp11 by exact H393.
destruct __TmpHyp11 as [x59 H394].
destruct H394 as [x60 H395].
destruct H395 as [x61 H396].
destruct H396 as [x62 H397].
destruct H397 as [x63 H398].
destruct H398 as [H399 H400].
destruct H400 as [H401 H402].
destruct H402 as [H403 H404].
destruct H404 as [H405 H406].
destruct H406 as [H407 H408].
destruct H408 as [H409 H410].
destruct H410 as [H411 H412].
destruct H412 as [H413 H414].
destruct H414 as [H415 H416].
destruct H416 as [H417 H418].
exact H103.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G A B) as H82.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B G A) /\ (euclidean__axioms.Col G A B))))) as H82.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A G H6).
---------------------------------------------------------------------- destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H90.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A m E) as H83.
---------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween G B F H A E m H82 H15 H76 H11 H13 H9 H81 H64 H73).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CR A E G H) as H84.
----------------------------------------------------------------------- exists m.
split.
------------------------------------------------------------------------ exact H83.
------------------------------------------------------------------------ exact H64.
----------------------------------------------------------------------- exact H84.
Qed.
