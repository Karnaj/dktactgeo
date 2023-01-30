Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__samesidesymmetric.
Require Export logic.
Definition lemma__parallelPasch : forall A B C D E, (euclidean__defs.PG A B C D) -> ((euclidean__axioms.BetS A D E) -> (exists X, (euclidean__axioms.BetS B X E) /\ (euclidean__axioms.BetS C X D))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
assert (* Cut *) (euclidean__defs.Par A B C D) as H1.
- destruct H as [H1 H2].
exact H1.
- assert (* Cut *) (euclidean__defs.Par A D B C) as H2.
-- destruct H as [H2 H3].
exact H3.
-- assert (* Cut *) (euclidean__defs.Par C D A B) as H3.
--- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A B C D H1).
--- assert (* Cut *) (euclidean__defs.TP C D A B) as H4.
---- apply (@lemma__paralleldef2B.lemma__paralleldef2B C D A B H3).
---- assert (* Cut *) (euclidean__defs.OS A B C D) as H5.
----- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
exact H10.
----- assert (* Cut *) (euclidean__defs.OS B A C D) as H6.
------ assert (* Cut *) ((euclidean__defs.OS B A C D) /\ ((euclidean__defs.OS A B D C) /\ (euclidean__defs.OS B A D C))) as H6.
------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric C D A B H5).
------- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
exact H7.
------ assert (* Cut *) (D = D) as H7.
------- apply (@logic.eq__refl Point D).
------- assert (* Cut *) (euclidean__axioms.neq A D) as H8.
-------- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H8.
--------- apply (@lemma__betweennotequal.lemma__betweennotequal A D E H0).
--------- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H11.
-------- assert (* Cut *) (euclidean__axioms.Col A D D) as H9.
--------- right.
right.
left.
exact H7.
--------- assert (* Cut *) (euclidean__axioms.Col A D E) as H10.
---------- right.
right.
right.
right.
left.
exact H0.
---------- assert (* Cut *) (euclidean__axioms.Col D D E) as H11.
----------- apply (@euclidean__tactics.not__nCol__Col D D E).
------------intro H11.
apply (@euclidean__tactics.Col__nCol__False D D E H11).
-------------apply (@lemma__collinear4.lemma__collinear4 A D D E H9 H10 H8).


----------- assert (* Cut *) (euclidean__axioms.Col E D D) as H12.
------------ assert (* Cut *) ((euclidean__axioms.Col D D E) /\ ((euclidean__axioms.Col D E D) /\ ((euclidean__axioms.Col E D D) /\ ((euclidean__axioms.Col D E D) /\ (euclidean__axioms.Col E D D))))) as H12.
------------- apply (@lemma__collinearorder.lemma__collinearorder D D E H11).
------------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H20.
------------ assert (* Cut *) (euclidean__axioms.Col C D D) as H13.
------------- right.
right.
left.
exact H7.
------------- assert (* Cut *) (euclidean__axioms.nCol A C D) as H14.
-------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H14.
--------------- apply (@lemma__parallelNC.lemma__parallelNC A B C D H1).
--------------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H17.
-------------- assert (* Cut *) (euclidean__axioms.nCol C D A) as H15.
--------------- assert (* Cut *) ((euclidean__axioms.nCol C A D) /\ ((euclidean__axioms.nCol C D A) /\ ((euclidean__axioms.nCol D A C) /\ ((euclidean__axioms.nCol A D C) /\ (euclidean__axioms.nCol D C A))))) as H15.
---------------- apply (@lemma__NCorder.lemma__NCorder A C D H14).
---------------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H18.
--------------- assert (* Cut *) (euclidean__axioms.TS A C D E) as H16.
---------------- exists D.
split.
----------------- exact H0.
----------------- split.
------------------ exact H13.
------------------ exact H15.
---------------- assert (* Cut *) (euclidean__axioms.TS B C D E) as H17.
----------------- apply (@lemma__planeseparation.lemma__planeseparation C D B A E H6 H16).
----------------- assert (exists H18, (euclidean__axioms.BetS B H18 E) /\ ((euclidean__axioms.Col C D H18) /\ (euclidean__axioms.nCol C D B))) as H18 by exact H17.
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
assert (* Cut *) (euclidean__axioms.BetS E H19 B) as H25.
------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry B H19 E H21).
------------------ assert (* Cut *) (euclidean__axioms.Col D C H19) as H26.
------------------- assert (* Cut *) ((euclidean__axioms.Col D C H19) /\ ((euclidean__axioms.Col D H19 C) /\ ((euclidean__axioms.Col H19 C D) /\ ((euclidean__axioms.Col C H19 D) /\ (euclidean__axioms.Col H19 D C))))) as H26.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder C D H19 H23).
-------------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H27.
------------------- assert (euclidean__axioms.neq A D) as H27 by exact H8.
assert (* Cut *) (~(euclidean__defs.Meet A D B C)) as H28.
-------------------- assert (exists U V u v X, (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H28 by exact H3.
assert (exists U V u v X, (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H28.
destruct __TmpHyp as [x H29].
destruct H29 as [x0 H30].
destruct H30 as [x1 H31].
destruct H31 as [x2 H32].
destruct H32 as [x3 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H54 by exact H2.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H54.
destruct __TmpHyp0 as [x4 H55].
destruct H55 as [x5 H56].
destruct H56 as [x6 H57].
destruct H57 as [x7 H58].
destruct H58 as [x8 H59].
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
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H80 by exact H1.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H80.
destruct __TmpHyp1 as [x9 H81].
destruct H81 as [x10 H82].
destruct H82 as [x11 H83].
destruct H83 as [x12 H84].
destruct H84 as [x13 H85].
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
exact H76.
-------------------- assert (* Cut *) (~(euclidean__defs.Meet E D C B)) as H29.
--------------------- intro H29.
assert (exists p, (euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col E D p) /\ (euclidean__axioms.Col C B p)))) as H30 by exact H29.
destruct H30 as [p H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
assert (* Cut *) (euclidean__axioms.neq B C) as H38.
---------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C B H34).
---------------------- assert (* Cut *) (euclidean__axioms.Col B C p) as H39.
----------------------- assert (* Cut *) ((euclidean__axioms.Col B C p) /\ ((euclidean__axioms.Col B p C) /\ ((euclidean__axioms.Col p C B) /\ ((euclidean__axioms.Col C p B) /\ (euclidean__axioms.Col p B C))))) as H39.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder C B p H37).
------------------------ destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H40.
----------------------- assert (* Cut *) (euclidean__axioms.Col E D A) as H40.
------------------------ assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H40.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder A D E H10).
------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H48.
------------------------ assert (* Cut *) (euclidean__axioms.Col D A p) as H41.
------------------------- apply (@euclidean__tactics.not__nCol__Col D A p).
--------------------------intro H41.
apply (@euclidean__tactics.Col__nCol__False D A p H41).
---------------------------apply (@lemma__collinear4.lemma__collinear4 E D A p H40 H36 H32).


------------------------- assert (* Cut *) (euclidean__axioms.Col A D p) as H42.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col A D p) /\ ((euclidean__axioms.Col A p D) /\ ((euclidean__axioms.Col p D A) /\ ((euclidean__axioms.Col D p A) /\ (euclidean__axioms.Col p A D))))) as H42.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder D A p H41).
--------------------------- destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H43.
-------------------------- assert (* Cut *) (euclidean__defs.Meet A D B C) as H43.
--------------------------- exists p.
split.
---------------------------- exact H27.
---------------------------- split.
----------------------------- exact H38.
----------------------------- split.
------------------------------ exact H42.
------------------------------ exact H39.
--------------------------- apply (@H28 H43).
--------------------- assert (* Cut *) (C = C) as H30.
---------------------- apply (@logic.eq__refl Point C).
---------------------- assert (* Cut *) (euclidean__axioms.neq D E) as H31.
----------------------- assert (* Cut *) ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A E))) as H31.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A D E H0).
------------------------ destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H32.
----------------------- assert (* Cut *) (euclidean__axioms.neq E D) as H32.
------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D E H31).
------------------------ assert (* Cut *) (euclidean__axioms.neq B C) as H33.
------------------------- assert (exists U V u v X, (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H33 by exact H3.
assert (exists U V u v X, (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H33.
destruct __TmpHyp as [x H34].
destruct H34 as [x0 H35].
destruct H35 as [x1 H36].
destruct H36 as [x2 H37].
destruct H37 as [x3 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H59 by exact H2.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H59.
destruct __TmpHyp0 as [x4 H60].
destruct H60 as [x5 H61].
destruct H61 as [x6 H62].
destruct H62 as [x7 H63].
destruct H63 as [x8 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H85 by exact H1.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H85.
destruct __TmpHyp1 as [x9 H86].
destruct H86 as [x10 H87].
destruct H87 as [x11 H88].
destruct H88 as [x12 H89].
destruct H89 as [x13 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
exact H67.
------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H34.
-------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B C H33).
-------------------------- assert (* Cut *) (euclidean__axioms.Col C C B) as H35.
--------------------------- left.
exact H30.
--------------------------- assert (* Cut *) (euclidean__axioms.BetS D H19 C) as H36.
---------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween E D C B D C H19 H12 H35 H32 H34 H32 H34 H29 H25 H26).
---------------------------- assert (* Cut *) (euclidean__axioms.BetS C H19 D) as H37.
----------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry D H19 C H36).
----------------------------- exists H19.
split.
------------------------------ exact H21.
------------------------------ exact H37.
Qed.
