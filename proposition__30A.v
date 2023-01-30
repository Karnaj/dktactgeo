Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7b.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__27.
Require Export proposition__29.
Definition proposition__30A : forall A B C D E F G H K, (euclidean__defs.Par A B E F) -> ((euclidean__defs.Par C D E F) -> ((euclidean__axioms.BetS G H K) -> ((euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS E H F) -> ((euclidean__axioms.BetS C K D) -> ((euclidean__axioms.TS A G H F) -> ((euclidean__axioms.TS F H K C) -> (euclidean__defs.Par A B C D)))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
intro K.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
intro H6.
intro H7.
assert (* Cut *) (euclidean__defs.Par E F C D) as H8.
- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric C D E F H1).
- assert (* Cut *) (euclidean__axioms.neq G H) as H9.
-- assert (* Cut *) ((euclidean__axioms.neq H K) /\ ((euclidean__axioms.neq G H) /\ (euclidean__axioms.neq G K))) as H9.
--- apply (@lemma__betweennotequal.lemma__betweennotequal G H K H2).
--- destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
exact H12.
-- assert (* Cut *) (euclidean__axioms.neq H G) as H10.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G H H9).
--- assert (* Cut *) (exists P, (euclidean__axioms.BetS H G P) /\ (euclidean__axioms.Cong G P G H)) as H11.
---- apply (@lemma__extension.lemma__extension H G G H H10 H9).
---- destruct H11 as [P H12].
destruct H12 as [H13 H14].
assert (* Cut *) (euclidean__axioms.BetS P G H) as H15.
----- apply (@euclidean__axioms.axiom__betweennesssymmetry H G P H13).
----- assert (* Cut *) (euclidean__axioms.BetS P G K) as H16.
------ apply (@lemma__3__7b.lemma__3__7b P G H K H15 H2).
------ assert (exists M, (euclidean__axioms.BetS A M F) /\ ((euclidean__axioms.Col G H M) /\ (euclidean__axioms.nCol G H A))) as H17 by exact H6.
destruct H17 as [M H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
assert (exists N, (euclidean__axioms.BetS F N C) /\ ((euclidean__axioms.Col H K N) /\ (euclidean__axioms.nCol H K F))) as H23 by exact H7.
destruct H23 as [N H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
assert (* Cut *) (~(euclidean__defs.Meet C D E F)) as H29.
------- assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H29 by exact H8.
assert (exists U V u v X, (euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col E F U) /\ ((euclidean__axioms.Col E F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E F C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H29.
destruct __TmpHyp as [x H30].
destruct H30 as [x0 H31].
destruct H31 as [x1 H32].
destruct H32 as [x2 H33].
destruct H33 as [x3 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
assert (exists U V u v X, (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H55 by exact H1.
assert (exists U V u v X, (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col C D U) /\ ((euclidean__axioms.Col C D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet C D E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H55.
destruct __TmpHyp0 as [x4 H56].
destruct H56 as [x5 H57].
destruct H57 as [x6 H58].
destruct H58 as [x7 H59].
destruct H59 as [x8 H60].
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
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H81 by exact H0.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E F u) /\ ((euclidean__axioms.Col E F v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B E F)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H81.
destruct __TmpHyp1 as [x9 H82].
destruct H82 as [x10 H83].
destruct H83 as [x11 H84].
destruct H84 as [x12 H85].
destruct H85 as [x13 H86].
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
exact H77.
------- assert (euclidean__axioms.nCol G H A) as H30 by exact H22.
assert (* Cut *) (euclidean__axioms.neq A G) as H31.
-------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H31.
--------- apply (@lemma__betweennotequal.lemma__betweennotequal A G B H3).
--------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H34.
-------- assert (* Cut *) (euclidean__axioms.neq G A) as H32.
--------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A G H31).
--------- assert (* Cut *) (euclidean__axioms.neq G H) as H33.
---------- assert (* Cut *) ((euclidean__axioms.neq N C) /\ ((euclidean__axioms.neq F N) /\ (euclidean__axioms.neq F C))) as H33.
----------- apply (@lemma__betweennotequal.lemma__betweennotequal F N C H25).
----------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H9.
---------- assert (* Cut *) (euclidean__axioms.nCol A G H) as H34.
----------- assert (* Cut *) ((euclidean__axioms.nCol H G A) /\ ((euclidean__axioms.nCol H A G) /\ ((euclidean__axioms.nCol A G H) /\ ((euclidean__axioms.nCol G A H) /\ (euclidean__axioms.nCol A H G))))) as H34.
------------ apply (@lemma__NCorder.lemma__NCorder G H A H30).
------------ destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H39.
----------- assert (* Cut *) (euclidean__defs.CongA A G H G H F) as H35.
------------ assert (* Cut *) ((euclidean__defs.Par A B E F) -> ((euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS E H F) -> ((euclidean__axioms.BetS P G H) -> ((euclidean__axioms.TS A G H F) -> (euclidean__defs.CongA A G H G H F)))))) as H35.
------------- intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.CongA A G H G H F) /\ ((euclidean__defs.CongA P G B G H F) /\ (euclidean__defs.RT B G H G H F))) as __4.
-------------- apply (@proposition__29.proposition__29 A B E F P G H __ __0 __1 __2 __3).
-------------- destruct __4 as [__4 __5].
exact __4.
------------- apply (@H35 H0 H3 H4 H15 H6).
------------ assert (* Cut *) (A = A) as H36.
------------- apply (@logic.eq__refl Point A).
------------- assert (* Cut *) (euclidean__defs.Out G A A) as H37.
-------------- apply (@lemma__ray4.lemma__ray4 G A A).
---------------right.
left.
exact H36.

--------------- exact H32.
-------------- assert (* Cut *) (euclidean__defs.Out G H K) as H38.
--------------- apply (@lemma__ray4.lemma__ray4 G H K).
----------------right.
right.
exact H2.

---------------- exact H33.
--------------- assert (* Cut *) (euclidean__defs.CongA A G H A G H) as H39.
---------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive A G H H34).
---------------- assert (* Cut *) (euclidean__defs.CongA A G H A G K) as H40.
----------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper A G H A G H A K H39 H37 H38).
----------------- assert (* Cut *) (euclidean__defs.CongA A G K A G H) as H41.
------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A G H A G K H40).
------------------ assert (* Cut *) (euclidean__defs.CongA A G K G H F) as H42.
------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A G K A G H G H F H41 H35).
------------------- assert (* Cut *) (euclidean__axioms.BetS C N F) as H43.
-------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry F N C H25).
-------------------- assert (* Cut *) (H = H) as H44.
--------------------- apply (@logic.eq__refl Point H).
--------------------- assert (* Cut *) (euclidean__axioms.nCol F H K) as H45.
---------------------- assert (* Cut *) ((euclidean__axioms.nCol K H F) /\ ((euclidean__axioms.nCol K F H) /\ ((euclidean__axioms.nCol F H K) /\ ((euclidean__axioms.nCol H F K) /\ (euclidean__axioms.nCol F K H))))) as H45.
----------------------- apply (@lemma__NCorder.lemma__NCorder H K F H28).
----------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H50.
---------------------- assert (* Cut *) (euclidean__axioms.Col E H F) as H46.
----------------------- right.
right.
right.
right.
left.
exact H4.
----------------------- assert (* Cut *) (euclidean__axioms.Col F H E) as H47.
------------------------ assert (* Cut *) ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col H F E) /\ ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col E F H) /\ (euclidean__axioms.Col F H E))))) as H47.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder E H F H46).
------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H55.
------------------------ assert (* Cut *) (euclidean__axioms.Col F H H) as H48.
------------------------- right.
right.
left.
exact H44.
------------------------- assert (* Cut *) (euclidean__axioms.neq E H) as H49.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H49.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E H F H4).
--------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H52.
-------------------------- assert (* Cut *) (euclidean__axioms.nCol E H K) as H50.
--------------------------- apply (@euclidean__tactics.nCol__notCol E H K).
----------------------------apply (@euclidean__tactics.nCol__not__Col E H K).
-----------------------------apply (@lemma__NChelper.lemma__NChelper F H K E H H45 H47 H48 H49).


--------------------------- assert (euclidean__axioms.Col E H F) as H51 by exact H46.
assert (* Cut *) (euclidean__axioms.Col E H H) as H52.
---------------------------- right.
right.
left.
exact H44.
---------------------------- assert (* Cut *) (euclidean__axioms.neq H F) as H53.
----------------------------- assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H53.
------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal E H F H4).
------------------------------ destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H54.
----------------------------- assert (* Cut *) (euclidean__axioms.neq F H) as H54.
------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric H F H53).
------------------------------ assert (euclidean__axioms.nCol F H K) as H55 by exact H45.
assert (* Cut *) (euclidean__axioms.nCol H K F) as H56.
------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H F K) /\ ((euclidean__axioms.nCol H K F) /\ ((euclidean__axioms.nCol K F H) /\ ((euclidean__axioms.nCol F K H) /\ (euclidean__axioms.nCol K H F))))) as H56.
-------------------------------- apply (@lemma__NCorder.lemma__NCorder F H K H55).
-------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H59.
------------------------------- assert (H = H) as H57 by exact H44.
assert (* Cut *) (euclidean__axioms.Col H K H) as H58.
-------------------------------- right.
left.
exact H57.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col K H N) as H59.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col K H N) /\ ((euclidean__axioms.Col K N H) /\ ((euclidean__axioms.Col N H K) /\ ((euclidean__axioms.Col H N K) /\ (euclidean__axioms.Col N K H))))) as H59.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H K N H27).
---------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H60.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col C K D) as H60.
---------------------------------- right.
right.
right.
right.
left.
exact H5.
---------------------------------- assert (euclidean__axioms.Col E H F) as H61 by exact H51.
assert (* Cut *) (euclidean__axioms.neq C K) as H62.
----------------------------------- assert (* Cut *) ((euclidean__axioms.neq K D) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D))) as H62.
------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal C K D H5).
------------------------------------ destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H65.
----------------------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H63.
------------------------------------ assert (* Cut *) ((euclidean__axioms.neq K D) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D))) as H63.
------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C K D H5).
------------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H67.
------------------------------------ assert (* Cut *) (euclidean__axioms.neq H F) as H64.
------------------------------------- assert (* Cut *) ((euclidean__axioms.neq N F) /\ ((euclidean__axioms.neq C N) /\ (euclidean__axioms.neq C F))) as H64.
-------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C N F H43).
-------------------------------------- destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H53.
------------------------------------- assert (* Cut *) (euclidean__axioms.neq E F) as H65.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H65.
--------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E H F H4).
--------------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H69.
-------------------------------------- assert (* Cut *) (euclidean__axioms.BetS K N H) as H66.
--------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween C D E F K H N H60 H61 H63 H65 H62 H64 H29 H43 H59).
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq N H) as H67.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.neq N H) /\ ((euclidean__axioms.neq K N) /\ (euclidean__axioms.neq K H))) as H67.
----------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal K N H H66).
----------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H68.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq H N) as H68.
----------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric N H H67).
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H N F) as H69.
------------------------------------------ apply (@euclidean__tactics.nCol__notCol H N F).
-------------------------------------------apply (@euclidean__tactics.nCol__not__Col H N F).
--------------------------------------------apply (@lemma__NChelper.lemma__NChelper H K F H N H56 H58 H27 H68).


------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol F N H) as H70.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol N H F) /\ ((euclidean__axioms.nCol N F H) /\ ((euclidean__axioms.nCol F H N) /\ ((euclidean__axioms.nCol H F N) /\ (euclidean__axioms.nCol F N H))))) as H70.
-------------------------------------------- apply (@lemma__NCorder.lemma__NCorder H N F H69).
-------------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H78.
------------------------------------------- assert (euclidean__axioms.BetS F N C) as H71 by exact H25.
assert (* Cut *) (euclidean__axioms.Col F N C) as H72.
-------------------------------------------- right.
right.
right.
right.
left.
exact H71.
-------------------------------------------- assert (* Cut *) (N = N) as H73.
--------------------------------------------- apply (@logic.eq__refl Point N).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F N N) as H74.
---------------------------------------------- right.
right.
left.
exact H73.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C N) as H75.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq N F) /\ ((euclidean__axioms.neq C N) /\ (euclidean__axioms.neq C F))) as H75.
------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal C N F H43).
------------------------------------------------ destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H78.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C N H) as H76.
------------------------------------------------ apply (@euclidean__tactics.nCol__notCol C N H).
-------------------------------------------------apply (@euclidean__tactics.nCol__not__Col C N H).
--------------------------------------------------apply (@lemma__NChelper.lemma__NChelper F N H C N H70 H72 H74 H75).


------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol H N C) as H77.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol N C H) /\ ((euclidean__axioms.nCol N H C) /\ ((euclidean__axioms.nCol H C N) /\ ((euclidean__axioms.nCol C H N) /\ (euclidean__axioms.nCol H N C))))) as H77.
-------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder C N H H76).
-------------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H85.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS H N K) as H78.
-------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry K N H H66).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H N K) as H79.
--------------------------------------------------- right.
right.
right.
right.
left.
exact H78.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H N H) as H80.
---------------------------------------------------- right.
left.
exact H57.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H K) as H81.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq N K) /\ ((euclidean__axioms.neq H N) /\ (euclidean__axioms.neq H K))) as H81.
------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal H N K H78).
------------------------------------------------------ destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H85.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H K C) as H82.
------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol H K C).
-------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col H K C).
--------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper H N C H K H77 H80 H79 H81).


------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol H K E) as H83.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H E K) /\ ((euclidean__axioms.nCol H K E) /\ ((euclidean__axioms.nCol K E H) /\ ((euclidean__axioms.nCol E K H) /\ (euclidean__axioms.nCol K H E))))) as H83.
-------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder E H K H50).
-------------------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H86.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS E C H K) as H84.
-------------------------------------------------------- exists F.
exists H.
exists N.
split.
--------------------------------------------------------- exact H58.
--------------------------------------------------------- split.
---------------------------------------------------------- exact H27.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H4.
----------------------------------------------------------- split.
------------------------------------------------------------ exact H43.
------------------------------------------------------------ split.
------------------------------------------------------------- exact H83.
------------------------------------------------------------- exact H82.
-------------------------------------------------------- assert (* Cut *) (K = K) as H85.
--------------------------------------------------------- apply (@logic.eq__refl Point K).
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H K K) as H86.
---------------------------------------------------------- right.
right.
left.
exact H85.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C H K D) as H87.
----------------------------------------------------------- exists K.
split.
------------------------------------------------------------ exact H5.
------------------------------------------------------------ split.
------------------------------------------------------------- exact H86.
------------------------------------------------------------- exact H82.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS E H K D) as H88.
------------------------------------------------------------ apply (@lemma__planeseparation.lemma__planeseparation H K E C D H84 H87).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA G H F H K D) as H89.
------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0 E0 G0 H89, (euclidean__defs.Par A0 B0 C0 D0) -> ((euclidean__axioms.BetS A0 G0 B0) -> ((euclidean__axioms.BetS C0 H89 D0) -> ((euclidean__axioms.BetS E0 G0 H89) -> ((euclidean__axioms.TS A0 G0 H89 D0) -> ((euclidean__defs.CongA E0 G0 B0 G0 H89 D0) /\ (euclidean__defs.RT B0 G0 H89 G0 H89 D0))))))) as H89.
-------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro E0.
intro G0.
intro H89.
intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.CongA A0 G0 H89 G0 H89 D0) /\ ((euclidean__defs.CongA E0 G0 B0 G0 H89 D0) /\ (euclidean__defs.RT B0 G0 H89 G0 H89 D0))) as __4.
--------------------------------------------------------------- apply (@proposition__29.proposition__29 A0 B0 C0 D0 E0 G0 H89 __ __0 __1 __2 __3).
--------------------------------------------------------------- destruct __4 as [__4 __5].
exact __5.
-------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0 E0 G0 H90, (euclidean__defs.Par A0 B0 C0 D0) -> ((euclidean__axioms.BetS A0 G0 B0) -> ((euclidean__axioms.BetS C0 H90 D0) -> ((euclidean__axioms.BetS E0 G0 H90) -> ((euclidean__axioms.TS A0 G0 H90 D0) -> (euclidean__defs.CongA E0 G0 B0 G0 H90 D0)))))) as H90.
--------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro E0.
intro G0.
intro H90.
intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.CongA E0 G0 B0 G0 H90 D0) /\ (euclidean__defs.RT B0 G0 H90 G0 H90 D0)) as __4.
---------------------------------------------------------------- apply (@H89 A0 B0 C0 D0 E0 G0 H90 __ __0 __1 __2 __3).
---------------------------------------------------------------- destruct __4 as [__4 __5].
exact __4.
--------------------------------------------------------------- apply (@H90 E F C D G H K H8 H4 H5 H2 H88).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C K H) as H90.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol K H C) /\ ((euclidean__axioms.nCol K C H) /\ ((euclidean__axioms.nCol C H K) /\ ((euclidean__axioms.nCol H C K) /\ (euclidean__axioms.nCol C K H))))) as H90.
--------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder H K C H82).
--------------------------------------------------------------- destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
exact H98.
-------------------------------------------------------------- assert (euclidean__axioms.Col C K D) as H91 by exact H60.
assert (K = K) as H92 by exact H85.
assert (* Cut *) (euclidean__axioms.Col C K K) as H93.
--------------------------------------------------------------- right.
right.
left.
exact H92.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq K D) as H94.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq K D) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C D))) as H94.
----------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C K D H5).
----------------------------------------------------------------- destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
exact H95.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D K) as H95.
----------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric K D H94).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D K H) as H96.
------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol D K H).
-------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col D K H).
--------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper C K H D K H90 H91 H93 H95).


------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol H K D) as H97.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol K D H) /\ ((euclidean__axioms.nCol K H D) /\ ((euclidean__axioms.nCol H D K) /\ ((euclidean__axioms.nCol D H K) /\ (euclidean__axioms.nCol H K D))))) as H97.
-------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder D K H H96).
-------------------------------------------------------------------- destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H105.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H K D H K D) as H98.
-------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive H K D H97).
-------------------------------------------------------------------- assert (* Cut *) (D = D) as H99.
--------------------------------------------------------------------- apply (@logic.eq__refl Point D).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out K D D) as H100.
---------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 K D D).
-----------------------------------------------------------------------right.
left.
exact H99.

----------------------------------------------------------------------- exact H94.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS K H G) as H101.
----------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry G H K H2).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq K H) as H102.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G))) as H102.
------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal K H G H101).
------------------------------------------------------------------------- destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
exact H105.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out K H G) as H103.
------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 K H G).
--------------------------------------------------------------------------right.
right.
exact H101.

-------------------------------------------------------------------------- exact H102.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H K D G K D) as H104.
-------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper H K D H K D G D H98 H103 H100).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G H F G K D) as H105.
--------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive G H F H K D G K D H89 H104).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A G K G K D) as H106.
---------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A G K G H F G K D H42 H105).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H K) as H107.
----------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H2.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G H) as H108.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G))) as H108.
------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal K H G H101).
------------------------------------------------------------------------------- destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
exact H33.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H M K) as H109.
------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col H M K).
--------------------------------------------------------------------------------intro H109.
apply (@euclidean__tactics.Col__nCol__False H M K H109).
---------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 G H M K H21 H107 H108).


------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H K M) as H110.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M H K) /\ ((euclidean__axioms.Col M K H) /\ ((euclidean__axioms.Col K H M) /\ ((euclidean__axioms.Col H K M) /\ (euclidean__axioms.Col K M H))))) as H110.
--------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H M K H109).
--------------------------------------------------------------------------------- destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
exact H117.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H K G) as H111.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H G K) /\ ((euclidean__axioms.Col H K G) /\ ((euclidean__axioms.Col K G H) /\ ((euclidean__axioms.Col G K H) /\ (euclidean__axioms.Col K H G))))) as H111.
---------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G H K H107).
---------------------------------------------------------------------------------- destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
exact H114.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H K) as H112.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H G) /\ ((euclidean__axioms.neq K H) /\ (euclidean__axioms.neq K G))) as H112.
----------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal K H G H101).
----------------------------------------------------------------------------------- destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
exact H81.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K M G) as H113.
----------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col K M G).
------------------------------------------------------------------------------------intro H113.
apply (@euclidean__tactics.Col__nCol__False K M G H113).
-------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 H K M G H110 H111 H112).


----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G K M) as H114.
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col M K G) /\ ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G K M) /\ ((euclidean__axioms.Col K G M) /\ (euclidean__axioms.Col G M K))))) as H114.
------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder K M G H113).
------------------------------------------------------------------------------------- destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
exact H119.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H K G) as H115.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col K M G) /\ ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G))))) as H115.
-------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G K M H114).
-------------------------------------------------------------------------------------- destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
exact H111.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K N G) as H116.
-------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col K N G).
---------------------------------------------------------------------------------------intro H116.
apply (@euclidean__tactics.Col__nCol__False K N G H116).
----------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 H K N G H27 H115 H112).


-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G K N) as H117.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col N K G) /\ ((euclidean__axioms.Col N G K) /\ ((euclidean__axioms.Col G K N) /\ ((euclidean__axioms.Col K G N) /\ (euclidean__axioms.Col G N K))))) as H117.
---------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder K N G H116).
---------------------------------------------------------------------------------------- destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
exact H122.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A G K) as H118.
---------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol A G K).
-----------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col A G K).
------------------------------------------------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC A G H A G K H40).


---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G K A) as H119.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G A K) /\ ((euclidean__axioms.nCol G K A) /\ ((euclidean__axioms.nCol K A G) /\ ((euclidean__axioms.nCol A K G) /\ (euclidean__axioms.nCol K G A))))) as H119.
------------------------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder A G K H118).
------------------------------------------------------------------------------------------ destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H122.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H K C) as H120.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol K G A) /\ ((euclidean__axioms.nCol K A G) /\ ((euclidean__axioms.nCol A G K) /\ ((euclidean__axioms.nCol G A K) /\ (euclidean__axioms.nCol A K G))))) as H120.
------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder G K A H119).
------------------------------------------------------------------------------------------- destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
exact H82.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H K G) as H121.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K G N) /\ ((euclidean__axioms.Col K N G) /\ ((euclidean__axioms.Col N G K) /\ ((euclidean__axioms.Col G N K) /\ (euclidean__axioms.Col N K G))))) as H121.
-------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G K N H117).
-------------------------------------------------------------------------------------------- destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
exact H115.
------------------------------------------------------------------------------------------- assert (euclidean__axioms.Col H K K) as H122 by exact H86.
assert (* Cut *) (euclidean__axioms.neq G K) as H123.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G K) /\ ((euclidean__axioms.neq P G) /\ (euclidean__axioms.neq P K))) as H123.
--------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal P G K H16).
--------------------------------------------------------------------------------------------- destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H124.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G K C) as H124.
--------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol G K C).
----------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col G K C).
-----------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper H K C G K H120 H121 H122 H123).


--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A C G K) as H125.
---------------------------------------------------------------------------------------------- exists F.
exists M.
exists N.
split.
----------------------------------------------------------------------------------------------- exact H114.
----------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------- exact H19.
------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------- exact H43.
-------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------- exact H119.
--------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G K K) as H126.
----------------------------------------------------------------------------------------------- right.
right.
left.
exact H92.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C G K D) as H127.
------------------------------------------------------------------------------------------------ exists K.
split.
------------------------------------------------------------------------------------------------- exact H5.
------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------- exact H126.
-------------------------------------------------------------------------------------------------- exact H124.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS A G K D) as H128.
------------------------------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation G K A C D H125 H127).
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H129.
-------------------------------------------------------------------------------------------------- apply (@proposition__27.proposition__27 A B C D G K H3 H5 H106 H128).
-------------------------------------------------------------------------------------------------- exact H129.
Qed.
