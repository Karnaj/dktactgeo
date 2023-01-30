Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__29.
Definition proposition__29C : forall B D E G H, (euclidean__defs.Par G B H D) -> ((euclidean__defs.OS B D G H) -> ((euclidean__axioms.BetS E G H) -> ((euclidean__defs.CongA E G B G H D) /\ (euclidean__defs.RT B G H G H D)))).
Proof.
intro B.
intro D.
intro E.
intro G.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.nCol G B H) as H3.
- assert (* Cut *) ((euclidean__axioms.nCol G B H) /\ ((euclidean__axioms.nCol G H D) /\ ((euclidean__axioms.nCol B H D) /\ (euclidean__axioms.nCol G B D)))) as H3.
-- apply (@lemma__parallelNC.lemma__parallelNC G B H D H0).
-- destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
exact H4.
- assert (* Cut *) (~(G = B)) as H4.
-- intro H4.
assert (* Cut *) (euclidean__axioms.Col G B H) as H5.
--- left.
exact H4.
--- apply (@euclidean__tactics.Col__nCol__False G B H H3 H5).
-- assert (* Cut *) (euclidean__axioms.neq B G) as H5.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G B H4).
--- assert (* Cut *) (exists A, (euclidean__axioms.BetS B G A) /\ (euclidean__axioms.Cong G A B G)) as H6.
---- apply (@lemma__extension.lemma__extension B G B G H5 H5).
---- destruct H6 as [A H7].
destruct H7 as [H8 H9].
assert (* Cut *) (euclidean__axioms.BetS A G B) as H10.
----- apply (@euclidean__axioms.axiom__betweennesssymmetry B G A H8).
----- assert (* Cut *) (euclidean__axioms.neq A B) as H11.
------ assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H11.
------- apply (@lemma__betweennotequal.lemma__betweennotequal A G B H10).
------- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H15.
------ assert (* Cut *) (euclidean__axioms.Col A B G) as H12.
------- right.
right.
right.
right.
right.
exact H10.
------- assert (* Cut *) (euclidean__axioms.Col G B A) as H13.
-------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H13.
--------- apply (@lemma__collinearorder.lemma__collinearorder A B G H12).
--------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H21.
-------- assert (* Cut *) (euclidean__defs.Par H D G B) as H14.
--------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric G B H D H0).
--------- assert (* Cut *) (euclidean__defs.Par H D A B) as H15.
---------- apply (@lemma__collinearparallel.lemma__collinearparallel H D A G B H14 H13 H11).
---------- assert (* Cut *) (euclidean__defs.Par H D B A) as H16.
----------- assert (* Cut *) ((euclidean__defs.Par D H A B) /\ ((euclidean__defs.Par H D B A) /\ (euclidean__defs.Par D H B A))) as H16.
------------ apply (@lemma__parallelflip.lemma__parallelflip H D A B H15).
------------ destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H19.
----------- assert (* Cut *) (euclidean__axioms.Col B A G) as H17.
------------ assert (* Cut *) ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col G A B) /\ (euclidean__axioms.Col A B G))))) as H17.
------------- apply (@lemma__collinearorder.lemma__collinearorder G B A H13).
------------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H20.
------------ assert (* Cut *) (euclidean__axioms.neq G A) as H18.
------------- assert (* Cut *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B G) /\ (euclidean__axioms.neq B A))) as H18.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal B G A H8).
-------------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H19.
------------- assert (* Cut *) (euclidean__defs.Par H D G A) as H19.
-------------- apply (@lemma__collinearparallel.lemma__collinearparallel H D G B A H16 H17 H18).
-------------- assert (* Cut *) (euclidean__defs.Par H D A G) as H20.
--------------- assert (* Cut *) ((euclidean__defs.Par D H G A) /\ ((euclidean__defs.Par H D A G) /\ (euclidean__defs.Par D H A G))) as H20.
---------------- apply (@lemma__parallelflip.lemma__parallelflip H D G A H19).
---------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H23.
--------------- assert (* Cut *) (euclidean__defs.Par A G H D) as H21.
---------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric H D A G H20).
---------------- assert (exists a g h d m, (euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H D) /\ ((euclidean__axioms.Col A G a) /\ ((euclidean__axioms.Col A G g) /\ ((euclidean__axioms.neq a g) /\ ((euclidean__axioms.Col H D h) /\ ((euclidean__axioms.Col H D d) /\ ((euclidean__axioms.neq h d) /\ ((~(euclidean__defs.Meet A G H D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS h m g))))))))))) as H22 by exact H21.
destruct H22 as [a H23].
destruct H23 as [g H24].
destruct H24 as [h H25].
destruct H25 as [d H26].
destruct H26 as [m H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
assert (* Cut *) (euclidean__axioms.neq D H) as H48.
----------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric H D H30).
----------------- assert (* Cut *) (exists C, (euclidean__axioms.BetS D H C) /\ (euclidean__axioms.Cong H C D H)) as H49.
------------------ apply (@lemma__extension.lemma__extension D H D H H48 H48).
------------------ destruct H49 as [C H50].
destruct H50 as [H51 H52].
assert (* Cut *) (euclidean__axioms.BetS H G E) as H53.
------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E G H H2).
------------------- assert (* Cut *) (euclidean__axioms.neq A B) as H54.
-------------------- assert (* Cut *) ((euclidean__axioms.neq G E) /\ ((euclidean__axioms.neq H G) /\ (euclidean__axioms.neq H E))) as H54.
--------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H G E H53).
--------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H11.
-------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H55.
--------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H54).
--------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H56.
---------------------- assert (* Cut *) ((euclidean__axioms.neq H C) /\ ((euclidean__axioms.neq D H) /\ (euclidean__axioms.neq D C))) as H56.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D H C H51).
----------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H60.
---------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H57.
----------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D C H56).
----------------------- assert (* Cut *) (euclidean__axioms.Col A G B) as H58.
------------------------ right.
right.
right.
right.
left.
exact H10.
------------------------ assert (* Cut *) (euclidean__axioms.Col G A B) as H59.
------------------------- assert (* Cut *) ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col G B A) /\ ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col B G A))))) as H59.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder A G B H58).
-------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H60.
------------------------- assert (* Cut *) (euclidean__axioms.Col G A a) as H60.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col G A a) /\ ((euclidean__axioms.Col G a A) /\ ((euclidean__axioms.Col a A G) /\ ((euclidean__axioms.Col A a G) /\ (euclidean__axioms.Col a G A))))) as H60.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder A G a H32).
--------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H61.
-------------------------- assert (euclidean__axioms.neq G A) as H61 by exact H18.
assert (* Cut *) (euclidean__axioms.Col A B a) as H62.
--------------------------- apply (@euclidean__tactics.not__nCol__Col A B a).
----------------------------intro H62.
apply (@euclidean__tactics.Col__nCol__False A B a H62).
-----------------------------apply (@lemma__collinear4.lemma__collinear4 G A B a H59 H60 H61).


--------------------------- assert (* Cut *) (euclidean__axioms.Col G A g) as H63.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col G A g) /\ ((euclidean__axioms.Col G g A) /\ ((euclidean__axioms.Col g A G) /\ ((euclidean__axioms.Col A g G) /\ (euclidean__axioms.Col g G A))))) as H63.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder A G g H34).
----------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H64.
---------------------------- assert (* Cut *) (euclidean__axioms.Col A B g) as H64.
----------------------------- apply (@euclidean__tactics.not__nCol__Col A B g).
------------------------------intro H64.
apply (@euclidean__tactics.Col__nCol__False A B g H64).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 G A B g H59 H63 H61).


----------------------------- assert (* Cut *) (euclidean__axioms.Col D H C) as H65.
------------------------------ right.
right.
right.
right.
left.
exact H51.
------------------------------ assert (* Cut *) (euclidean__axioms.Col H D C) as H66.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col H D C) /\ ((euclidean__axioms.Col H C D) /\ ((euclidean__axioms.Col C D H) /\ ((euclidean__axioms.Col D C H) /\ (euclidean__axioms.Col C H D))))) as H66.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D H C H65).
-------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H67.
------------------------------- assert (* Cut *) (euclidean__axioms.Col D C h) as H67.
-------------------------------- apply (@euclidean__tactics.not__nCol__Col D C h).
---------------------------------intro H67.
apply (@euclidean__tactics.Col__nCol__False D C h H67).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 H D C h H66 H38 H30).


-------------------------------- assert (* Cut *) (euclidean__axioms.Col C D h) as H68.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col C D h) /\ ((euclidean__axioms.Col C h D) /\ ((euclidean__axioms.Col h D C) /\ ((euclidean__axioms.Col D h C) /\ (euclidean__axioms.Col h C D))))) as H68.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D C h H67).
---------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H69.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col D d C) as H69.
---------------------------------- apply (@euclidean__tactics.not__nCol__Col D d C).
-----------------------------------intro H69.
apply (@euclidean__tactics.Col__nCol__False D d C H69).
------------------------------------apply (@lemma__collinear4.lemma__collinear4 H D d C H40 H66 H30).


---------------------------------- assert (* Cut *) (euclidean__axioms.Col C D d) as H70.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col d D C) /\ ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.Col D C d) /\ (euclidean__axioms.Col C d D))))) as H70.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder D d C H69).
------------------------------------ destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H75.
----------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H71.
------------------------------------ intro H71.
assert (exists M, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.Col C D M)))) as H72 by exact H71.
destruct H72 as [M H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
assert (* Cut *) (euclidean__axioms.Col B A G) as H80.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C M) /\ ((euclidean__axioms.Col D M C) /\ ((euclidean__axioms.Col M C D) /\ ((euclidean__axioms.Col C M D) /\ (euclidean__axioms.Col M D C))))) as H80.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D M H79).
-------------------------------------- destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H17.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A M) as H81.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A M) /\ ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A M B) /\ (euclidean__axioms.Col M B A))))) as H81.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B M H78).
--------------------------------------- destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H82.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col A G M) as H82.
--------------------------------------- apply (@euclidean__tactics.not__nCol__Col A G M).
----------------------------------------intro H82.
apply (@euclidean__tactics.Col__nCol__False A G M H82).
-----------------------------------------apply (@lemma__collinear4.lemma__collinear4 B A G M H80 H81 H55).


--------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D H) as H83.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D H C) /\ ((euclidean__axioms.Col D C H) /\ ((euclidean__axioms.Col C H D) /\ ((euclidean__axioms.Col H C D) /\ (euclidean__axioms.Col C D H))))) as H83.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H D C H66).
----------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H91.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col D H M) as H84.
----------------------------------------- apply (@euclidean__tactics.not__nCol__Col D H M).
------------------------------------------intro H84.
apply (@euclidean__tactics.Col__nCol__False D H M H84).
-------------------------------------------apply (@lemma__collinear4.lemma__collinear4 C D H M H83 H79 H76).


----------------------------------------- assert (* Cut *) (euclidean__axioms.Col H D M) as H85.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col H D M) /\ ((euclidean__axioms.Col H M D) /\ ((euclidean__axioms.Col M D H) /\ ((euclidean__axioms.Col D M H) /\ (euclidean__axioms.Col M H D))))) as H85.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D H M H84).
------------------------------------------- destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
exact H86.
------------------------------------------ assert (* Cut *) (euclidean__defs.Meet A G H D) as H86.
------------------------------------------- exists M.
split.
-------------------------------------------- exact H28.
-------------------------------------------- split.
--------------------------------------------- exact H30.
--------------------------------------------- split.
---------------------------------------------- exact H82.
---------------------------------------------- exact H85.
------------------------------------------- apply (@H44 H86).
------------------------------------ assert (* Cut *) (euclidean__defs.Par A B C D) as H72.
------------------------------------- exists a.
exists g.
exists h.
exists d.
exists m.
split.
-------------------------------------- exact H54.
-------------------------------------- split.
--------------------------------------- exact H57.
--------------------------------------- split.
---------------------------------------- exact H62.
---------------------------------------- split.
----------------------------------------- exact H64.
----------------------------------------- split.
------------------------------------------ exact H36.
------------------------------------------ split.
------------------------------------------- exact H68.
------------------------------------------- split.
-------------------------------------------- exact H70.
-------------------------------------------- split.
--------------------------------------------- exact H42.
--------------------------------------------- split.
---------------------------------------------- exact H71.
---------------------------------------------- split.
----------------------------------------------- exact H46.
----------------------------------------------- exact H47.
------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C H D) as H73.
-------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry D H C H51).
-------------------------------------- assert (euclidean__axioms.BetS E G H) as H74 by exact H2.
assert (* Cut *) (G = G) as H75.
--------------------------------------- apply (@logic.eq__refl Point G).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H G) as H76.
---------------------------------------- right.
left.
exact H75.
---------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G B H) as H77.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H77.
------------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC A B C D H72).
------------------------------------------ destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H3.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G H B) as H78.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol B G H) /\ ((euclidean__axioms.nCol B H G) /\ ((euclidean__axioms.nCol H G B) /\ ((euclidean__axioms.nCol G H B) /\ (euclidean__axioms.nCol H B G))))) as H78.
------------------------------------------- apply (@lemma__NCorder.lemma__NCorder G B H H77).
------------------------------------------- destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
exact H85.
------------------------------------------ assert (* Cut *) (euclidean__defs.OS D B G H) as H79.
------------------------------------------- assert (* Cut *) ((euclidean__defs.OS D B G H) /\ ((euclidean__defs.OS B D H G) /\ (euclidean__defs.OS D B H G))) as H79.
-------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric G H B D H1).
-------------------------------------------- destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H80.
------------------------------------------- assert (* Cut *) (euclidean__axioms.TS B G H A) as H80.
-------------------------------------------- exists G.
split.
--------------------------------------------- exact H8.
--------------------------------------------- split.
---------------------------------------------- exact H76.
---------------------------------------------- exact H78.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.TS D G H A) as H81.
--------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation G H D B A H79 H80).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.TS A G H D) as H82.
---------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric G H D A H81).
---------------------------------------------- assert (* Cut *) ((euclidean__defs.CongA A G H G H D) /\ ((euclidean__defs.CongA E G B G H D) /\ (euclidean__defs.RT B G H G H D))) as H83.
----------------------------------------------- apply (@proposition__29.proposition__29 A B C D E G H H72 H10 H73 H74 H82).
----------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CongA E G B G H D) /\ (euclidean__defs.RT B G H G H D))).
------------------------------------------------intro H84.
destruct H3 as [H85 H86].
destruct H77 as [H87 H88].
destruct H78 as [H89 H90].
destruct H83 as [H91 H92].
destruct H86 as [H93 H94].
destruct H88 as [H95 H96].
destruct H90 as [H97 H98].
destruct H92 as [H99 H100].
destruct H94 as [H101 H102].
destruct H96 as [H103 H104].
destruct H98 as [H105 H106].
destruct H102 as [H107 H108].
destruct H104 as [H109 H110].
destruct H106 as [H111 H112].
destruct H108 as [H113 H114].
destruct H110 as [H115 H116].
destruct H112 as [H117 H118].
assert (* Cut *) ((euclidean__defs.CongA E G B G H D) -> ((euclidean__defs.RT B G H G H D) -> False)) as H119.
------------------------------------------------- intro H119.
intro H120.
apply (@H84).
--------------------------------------------------split.
--------------------------------------------------- exact H119.
--------------------------------------------------- exact H120.

------------------------------------------------- assert (* Cut *) ((euclidean__defs.RT B G H G H D) -> False) as H120.
-------------------------------------------------- apply (@H119 H99).
-------------------------------------------------- assert (* Cut *) (False) as H121.
--------------------------------------------------- apply (@H120 H100).
--------------------------------------------------- contradiction H121.

Qed.
