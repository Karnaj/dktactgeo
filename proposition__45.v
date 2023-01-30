Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7b.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__Playfair.
Require Export lemma__RTcongruence.
Require Export lemma__RTsymmetric.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__diagonalsmeet.
Require Export lemma__equalanglesNC.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__samesidecollinear.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__10.
Require Export proposition__14.
Require Export proposition__29C.
Require Export proposition__30.
Require Export proposition__42B.
Require Export proposition__44.
Definition proposition__45 : forall A B C D E J K N O R S, (euclidean__axioms.nCol J E N) -> ((euclidean__axioms.nCol A B D) -> ((euclidean__axioms.nCol C B D) -> ((euclidean__axioms.BetS A O C) -> ((euclidean__axioms.BetS B O D) -> ((euclidean__axioms.neq R K) -> ((euclidean__axioms.nCol K R S) -> (exists X Z U, (euclidean__defs.PG X K Z U) /\ ((euclidean__defs.CongA X K Z J E N) /\ ((euclidean__axioms.EF X K Z U A B C D) /\ ((euclidean__defs.Out K R Z) /\ (euclidean__defs.OS X S K Z))))))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro J.
intro K.
intro N.
intro O.
intro R.
intro S.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
assert (* Cut *) (euclidean__axioms.neq B D) as H6.
- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C)))))) as H6.
-- apply (@lemma__NCdistinct.lemma__NCdistinct C B D H1).
-- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H9.
- assert (* Cut *) (exists m, (euclidean__axioms.BetS B m D) /\ (euclidean__axioms.Cong m B m D)) as H7.
-- apply (@proposition__10.proposition__10 B D H6).
-- destruct H7 as [m H8].
destruct H8 as [H9 H10].
assert (* Cut *) (euclidean__axioms.Cong B m m D) as H11.
--- assert (* Cut *) ((euclidean__axioms.Cong B m D m) /\ ((euclidean__axioms.Cong B m m D) /\ (euclidean__axioms.Cong m B D m))) as H11.
---- apply (@lemma__congruenceflip.lemma__congruenceflip m B m D H10).
---- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H14.
--- assert (* Cut *) (euclidean__defs.Midpoint B m D) as H12.
---- split.
----- exact H9.
----- exact H11.
---- assert (* Cut *) (euclidean__axioms.neq B m) as H13.
----- assert (* Cut *) ((euclidean__axioms.neq m D) /\ ((euclidean__axioms.neq B m) /\ (euclidean__axioms.neq B D))) as H13.
------ apply (@lemma__betweennotequal.lemma__betweennotequal B m D H9).
------ destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H16.
----- assert (* Cut *) (exists P, (euclidean__axioms.BetS R K P) /\ (euclidean__axioms.Cong K P B m)) as H14.
------ apply (@lemma__extension.lemma__extension R K B m H4 H13).
------ destruct H14 as [P H15].
destruct H15 as [H16 H17].
assert (euclidean__axioms.Triangle A B D) as H18 by exact H0.
assert (* Cut *) (euclidean__axioms.neq K P) as H19.
------- assert (* Cut *) ((euclidean__axioms.neq K P) /\ ((euclidean__axioms.neq R K) /\ (euclidean__axioms.neq R P))) as H19.
-------- apply (@lemma__betweennotequal.lemma__betweennotequal R K P H16).
-------- destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H20.
------- assert (* Cut *) (euclidean__axioms.neq P K) as H20.
-------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric K P H19).
-------- assert (* Cut *) (exists H21, (euclidean__axioms.BetS P K H21) /\ (euclidean__axioms.Cong K H21 P K)) as H21.
--------- apply (@lemma__extension.lemma__extension P K P K H20 H20).
--------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
assert (* Cut *) (euclidean__axioms.Cong P K K H22) as H26.
---------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric P K H22 K H25).
---------- assert (* Cut *) (euclidean__defs.Midpoint P K H22) as H27.
----------- split.
------------ exact H24.
------------ exact H26.
----------- assert (* Cut *) (euclidean__axioms.Cong P K B m) as H28.
------------ assert (* Cut *) ((euclidean__axioms.Cong P K m B) /\ ((euclidean__axioms.Cong P K B m) /\ (euclidean__axioms.Cong K P m B))) as H28.
------------- apply (@lemma__congruenceflip.lemma__congruenceflip K P B m H17).
------------- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H31.
------------ assert (* Cut *) (euclidean__axioms.Cong K H22 B m) as H29.
------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive K H22 P K B m H25 H28).
------------- assert (* Cut *) (euclidean__axioms.Cong B m m D) as H30.
-------------- assert (* Cut *) ((euclidean__axioms.Cong H22 K m B) /\ ((euclidean__axioms.Cong H22 K B m) /\ (euclidean__axioms.Cong K H22 m B))) as H30.
--------------- apply (@lemma__congruenceflip.lemma__congruenceflip K H22 B m H29).
--------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H11.
-------------- assert (* Cut *) (euclidean__axioms.Cong K H22 m D) as H31.
--------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive K H22 B m m D H29 H30).
--------------- assert (* Cut *) (euclidean__axioms.BetS P K R) as H32.
---------------- apply (@euclidean__axioms.axiom__betweennesssymmetry R K P H16).
---------------- assert (* Cut *) (euclidean__axioms.Col P K H22) as H33.
----------------- right.
right.
right.
right.
left.
exact H24.
----------------- assert (* Cut *) (euclidean__axioms.Col P K R) as H34.
------------------ right.
right.
right.
right.
left.
exact H32.
------------------ assert (* Cut *) (euclidean__axioms.neq P K) as H35.
------------------- assert (* Cut *) ((euclidean__axioms.neq K R) /\ ((euclidean__axioms.neq P K) /\ (euclidean__axioms.neq P R))) as H35.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal P K R H32).
-------------------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H38.
------------------- assert (* Cut *) (euclidean__axioms.Col K H22 R) as H36.
-------------------- apply (@euclidean__tactics.not__nCol__Col K H22 R).
---------------------intro H36.
apply (@euclidean__tactics.Col__nCol__False K H22 R H36).
----------------------apply (@lemma__collinear4.lemma__collinear4 P K H22 R H33 H34 H35).


-------------------- assert (* Cut *) (euclidean__axioms.Col R K H22) as H37.
--------------------- assert (* Cut *) ((euclidean__axioms.Col H22 K R) /\ ((euclidean__axioms.Col H22 R K) /\ ((euclidean__axioms.Col R K H22) /\ ((euclidean__axioms.Col K R H22) /\ (euclidean__axioms.Col R H22 K))))) as H37.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder K H22 R H36).
---------------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H42.
--------------------- assert (* Cut *) (euclidean__axioms.nCol R K S) as H38.
---------------------- assert (* Cut *) ((euclidean__axioms.nCol R K S) /\ ((euclidean__axioms.nCol R S K) /\ ((euclidean__axioms.nCol S K R) /\ ((euclidean__axioms.nCol K S R) /\ (euclidean__axioms.nCol S R K))))) as H38.
----------------------- apply (@lemma__NCorder.lemma__NCorder K R S H5).
----------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H39.
---------------------- assert (* Cut *) (K = K) as H39.
----------------------- apply (@logic.eq__refl Point K).
----------------------- assert (* Cut *) (euclidean__axioms.Col R K K) as H40.
------------------------ right.
right.
left.
exact H39.
------------------------ assert (* Cut *) (euclidean__axioms.neq K H22) as H41.
------------------------- assert (* Cut *) ((euclidean__axioms.neq K H22) /\ ((euclidean__axioms.neq P K) /\ (euclidean__axioms.neq P H22))) as H41.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal P K H22 H24).
-------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H42.
------------------------- assert (* Cut *) (euclidean__axioms.neq H22 K) as H42.
-------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric K H22 H41).
-------------------------- assert (* Cut *) (euclidean__axioms.nCol H22 K S) as H43.
--------------------------- apply (@euclidean__tactics.nCol__notCol H22 K S).
----------------------------apply (@euclidean__tactics.nCol__not__Col H22 K S).
-----------------------------apply (@lemma__NChelper.lemma__NChelper R K S H22 K H38 H37 H40 H42).


--------------------------- assert (* Cut *) (euclidean__axioms.nCol S K H22) as H44.
---------------------------- assert (* Cut *) ((euclidean__axioms.nCol K H22 S) /\ ((euclidean__axioms.nCol K S H22) /\ ((euclidean__axioms.nCol S H22 K) /\ ((euclidean__axioms.nCol H22 S K) /\ (euclidean__axioms.nCol S K H22))))) as H44.
----------------------------- apply (@lemma__NCorder.lemma__NCorder H22 K S H43).
----------------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H52.
---------------------------- assert (* Cut *) (exists F G, (euclidean__defs.PG F K H22 G) /\ ((euclidean__axioms.EF A B m D F K H22 G) /\ ((euclidean__defs.CongA H22 K F J E N) /\ (euclidean__defs.OS S F K H22)))) as H45.
----------------------------- apply (@proposition__42B.proposition__42B P H22 E K J N S A B D m H18 H12 H H27 H31 H44).
----------------------------- destruct H45 as [F H46].
destruct H46 as [G H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
assert (* Cut *) (euclidean__axioms.nCol D B C) as H54.
------------------------------ assert (* Cut *) ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol D C B) /\ ((euclidean__axioms.nCol C D B) /\ (euclidean__axioms.nCol D B C))))) as H54.
------------------------------- apply (@lemma__NCorder.lemma__NCorder C B D H1).
------------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H62.
------------------------------ assert (euclidean__axioms.Triangle D B C) as H55 by exact H54.
assert (* Cut *) (euclidean__defs.Par F K H22 G) as H56.
------------------------------- destruct H48 as [H56 H57].
exact H56.
------------------------------- assert (* Cut *) (euclidean__axioms.nCol K H22 G) as H57.
-------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F K H22) /\ ((euclidean__axioms.nCol F H22 G) /\ ((euclidean__axioms.nCol K H22 G) /\ (euclidean__axioms.nCol F K G)))) as H57.
--------------------------------- apply (@lemma__parallelNC.lemma__parallelNC F K H22 G H56).
--------------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H62.
-------------------------------- assert (* Cut *) (euclidean__axioms.nCol H22 G K) as H58.
--------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H22 K G) /\ ((euclidean__axioms.nCol H22 G K) /\ ((euclidean__axioms.nCol G K H22) /\ ((euclidean__axioms.nCol K G H22) /\ (euclidean__axioms.nCol G H22 K))))) as H58.
---------------------------------- apply (@lemma__NCorder.lemma__NCorder K H22 G H57).
---------------------------------- destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H61.
--------------------------------- assert (* Cut *) (euclidean__axioms.nCol G H22 K) as H59.
---------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G H22 K) /\ ((euclidean__axioms.nCol G K H22) /\ ((euclidean__axioms.nCol K H22 G) /\ ((euclidean__axioms.nCol H22 K G) /\ (euclidean__axioms.nCol K G H22))))) as H59.
----------------------------------- apply (@lemma__NCorder.lemma__NCorder H22 G K H58).
----------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H60.
---------------------------------- assert (* Cut *) (exists M L e, (euclidean__defs.PG G H22 M L) /\ ((euclidean__defs.CongA G H22 M J E N) /\ ((euclidean__axioms.EF D B e C G H22 M L) /\ ((euclidean__defs.Midpoint B e C) /\ (euclidean__axioms.TS M G H22 K))))) as H60.
----------------------------------- apply (@proposition__44.proposition__44 G H22 E J N K D B C H55 H H59).
----------------------------------- destruct H60 as [M H61].
destruct H61 as [L H62].
destruct H62 as [e H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
assert (* Cut *) (euclidean__axioms.BetS B e C) as H72.
------------------------------------ destruct H70 as [H72 H73].
destruct H27 as [H74 H75].
destruct H12 as [H76 H77].
exact H72.
------------------------------------ assert (* Cut *) (euclidean__defs.CongA J E N G H22 M) as H73.
------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric G H22 M J E N H66).
------------------------------------- assert (* Cut *) (euclidean__defs.CongA H22 K F G H22 M) as H74.
-------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive H22 K F J E N G H22 M H52 H73).
-------------------------------------- assert (* Cut *) (euclidean__defs.Par F K H22 G) as H75.
--------------------------------------- destruct H64 as [H75 H76].
destruct H48 as [H77 H78].
exact H56.
--------------------------------------- assert (* Cut *) (euclidean__defs.Par K F H22 G) as H76.
---------------------------------------- assert (* Cut *) ((euclidean__defs.Par K F H22 G) /\ ((euclidean__defs.Par F K G H22) /\ (euclidean__defs.Par K F G H22))) as H76.
----------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip F K H22 G H75).
----------------------------------------- destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H77.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq H22 K) as H77.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G H22) /\ ((euclidean__axioms.neq H22 K) /\ ((euclidean__axioms.neq G K) /\ ((euclidean__axioms.neq H22 G) /\ ((euclidean__axioms.neq K H22) /\ (euclidean__axioms.neq K G)))))) as H77.
------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct G H22 K H59).
------------------------------------------ destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
exact H80.
----------------------------------------- assert (* Cut *) (exists s, (euclidean__axioms.BetS H22 K s) /\ (euclidean__axioms.Cong K s H22 K)) as H78.
------------------------------------------ apply (@lemma__extension.lemma__extension H22 K H22 K H77 H77).
------------------------------------------ destruct H78 as [s H79].
destruct H79 as [H80 H81].
assert (* Cut *) (euclidean__defs.Par F G K H22) as H82.
------------------------------------------- destruct H64 as [H82 H83].
destruct H48 as [H84 H85].
exact H85.
------------------------------------------- assert (* Cut *) (euclidean__defs.Par K H22 F G) as H83.
-------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric F G K H22 H82).
-------------------------------------------- assert (* Cut *) (euclidean__defs.TP K H22 F G) as H84.
--------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B K H22 F G H83).
--------------------------------------------- assert (* Cut *) (euclidean__defs.OS F G K H22) as H85.
---------------------------------------------- destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H90.
---------------------------------------------- assert (* Cut *) (euclidean__defs.RT F K H22 K H22 G) as H86.
----------------------------------------------- assert (* Cut *) (forall B0 D0 E0 G0 H86, (euclidean__defs.Par G0 B0 H86 D0) -> ((euclidean__defs.OS B0 D0 G0 H86) -> ((euclidean__axioms.BetS E0 G0 H86) -> (euclidean__defs.RT B0 G0 H86 G0 H86 D0)))) as H86.
------------------------------------------------ intro B0.
intro D0.
intro E0.
intro G0.
intro H86.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA E0 G0 B0 G0 H86 D0) /\ (euclidean__defs.RT B0 G0 H86 G0 H86 D0)) as __2.
------------------------------------------------- apply (@proposition__29C.proposition__29C B0 D0 E0 G0 H86 __ __0 __1).
------------------------------------------------- destruct __2 as [__2 __3].
exact __3.
------------------------------------------------ apply (@H86 F G P K H22 H76 H85 H24).
----------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G H22 M H22 K F) as H87.
------------------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric H22 K F G H22 M H74).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol H22 K F) as H88.
------------------------------------------------- apply (@euclidean__tactics.nCol__notCol H22 K F).
--------------------------------------------------apply (@euclidean__tactics.nCol__not__Col H22 K F).
---------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC G H22 M H22 K F H87).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F K H22) as H89.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol K H22 F) /\ ((euclidean__axioms.nCol K F H22) /\ ((euclidean__axioms.nCol F H22 K) /\ ((euclidean__axioms.nCol H22 F K) /\ (euclidean__axioms.nCol F K H22))))) as H89.
--------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder H22 K F H88).
--------------------------------------------------- destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
exact H97.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F K H22 H22 K F) as H90.
--------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA F K H22 H89).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F K H22 G H22 M) as H91.
---------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive F K H22 H22 K F G H22 M H90 H74).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.RT G H22 M K H22 G) as H92.
----------------------------------------------------- apply (@lemma__RTcongruence.lemma__RTcongruence F K H22 K H22 G G H22 M H86 H91).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.RT K H22 G G H22 M) as H93.
------------------------------------------------------ apply (@lemma__RTsymmetric.lemma__RTsymmetric G H22 M K H22 G H92).
------------------------------------------------------ assert (* Cut *) (G = G) as H94.
------------------------------------------------------- apply (@logic.eq__refl Point G).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H22 G) as H95.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G H22) /\ ((euclidean__axioms.neq H22 K) /\ ((euclidean__axioms.neq G K) /\ ((euclidean__axioms.neq H22 G) /\ ((euclidean__axioms.neq K H22) /\ (euclidean__axioms.neq K G)))))) as H95.
--------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct G H22 K H59).
--------------------------------------------------------- destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H102.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out H22 G G) as H96.
--------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 H22 G G).
----------------------------------------------------------right.
left.
exact H94.

---------------------------------------------------------- exact H95.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS K H22 M) as H97.
---------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0 E0, (euclidean__defs.RT A0 B0 C0 D0 B0 E0) -> ((euclidean__defs.Out B0 C0 D0) -> ((euclidean__axioms.TS E0 D0 B0 A0) -> (euclidean__axioms.BetS A0 B0 E0)))) as H97.
----------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro E0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.Supp A0 B0 C0 D0 E0) /\ (euclidean__axioms.BetS A0 B0 E0)) as __2.
------------------------------------------------------------ apply (@proposition__14.proposition__14 A0 B0 C0 D0 E0 __ __0 __1).
------------------------------------------------------------ destruct __2 as [__2 __3].
exact __3.
----------------------------------------------------------- apply (@H97 K H22 G G M H93 H96 H71).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F K) as H98.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F K) /\ ((euclidean__axioms.neq K H22) /\ ((euclidean__axioms.neq F H22) /\ ((euclidean__axioms.neq K F) /\ ((euclidean__axioms.neq H22 K) /\ (euclidean__axioms.neq H22 F)))))) as H98.
------------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct F K H22 H89).
------------------------------------------------------------ destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
exact H99.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G H22 M) as H99.
------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol G H22 M).
-------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col G H22 M).
--------------------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC F K H22 G H22 M H91).


------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq G H22) as H100.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G H22) /\ ((euclidean__axioms.neq H22 M) /\ ((euclidean__axioms.neq G M) /\ ((euclidean__axioms.neq H22 G) /\ ((euclidean__axioms.neq M H22) /\ (euclidean__axioms.neq M G)))))) as H100.
-------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct G H22 M H99).
-------------------------------------------------------------- destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
exact H101.
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G H22 M L) as H101.
-------------------------------------------------------------- destruct H64 as [H101 H102].
destruct H48 as [H103 H104].
exact H101.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H22 M L) as H102.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G H22 M) /\ ((euclidean__axioms.nCol G M L) /\ ((euclidean__axioms.nCol H22 M L) /\ (euclidean__axioms.nCol G H22 L)))) as H102.
---------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC G H22 M L H101).
---------------------------------------------------------------- destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
exact H107.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L M) as H103.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H22 M) /\ ((euclidean__axioms.neq M L) /\ ((euclidean__axioms.neq H22 L) /\ ((euclidean__axioms.neq M H22) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L H22)))))) as H103.
----------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct H22 M L H102).
----------------------------------------------------------------- destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
exact H112.
---------------------------------------------------------------- assert (K = K) as H104 by exact H39.
assert (* Cut *) (H22 = H22) as H105.
----------------------------------------------------------------- apply (@logic.eq__refl Point H22).
----------------------------------------------------------------- assert (* Cut *) (M = M) as H106.
------------------------------------------------------------------ apply (@logic.eq__refl Point M).
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col F K K) as H107.
------------------------------------------------------------------- right.
right.
left.
exact H104.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H22 H22) as H108.
-------------------------------------------------------------------- right.
right.
left.
exact H105.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L M M) as H109.
--------------------------------------------------------------------- right.
right.
left.
exact H106.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F K G H22) as H110.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par F K H22 G) /\ ((euclidean__defs.Par K F G H22) /\ (euclidean__defs.Par F K G H22))) as H110.
----------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip K F H22 G H76).
----------------------------------------------------------------------- destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
exact H114.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M L G H22) as H111.
----------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric G H22 M L H101).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par L M G H22) as H112.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par L M G H22) /\ ((euclidean__defs.Par M L H22 G) /\ (euclidean__defs.Par L M H22 G))) as H112.
------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip M L G H22 H111).
------------------------------------------------------------------------- destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
exact H113.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par F K L M) as H113.
------------------------------------------------------------------------- apply (@proposition__30.proposition__30 F K L M G H22 K H22 M H110 H112 H97 H107 H108 H109 H98 H100 H103).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F K M L) as H114.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par K F L M) /\ ((euclidean__defs.Par F K M L) /\ (euclidean__defs.Par K F M L))) as H114.
--------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip F K L M H113).
--------------------------------------------------------------------------- destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
exact H117.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F G K H22) as H115.
--------------------------------------------------------------------------- destruct H64 as [H115 H116].
destruct H48 as [H117 H118].
exact H82.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G L H22 M) as H116.
---------------------------------------------------------------------------- destruct H64 as [H116 H117].
destruct H48 as [H118 H119].
exact H117.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F G H22 K) as H117.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par G F K H22) /\ ((euclidean__defs.Par F G H22 K) /\ (euclidean__defs.Par G F H22 K))) as H117.
------------------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip F G K H22 H115).
------------------------------------------------------------------------------ destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
exact H120.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K H22 M) as H118.
------------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H97.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H22 K M) as H119.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H22 K M) /\ ((euclidean__axioms.Col H22 M K) /\ ((euclidean__axioms.Col M K H22) /\ ((euclidean__axioms.Col K M H22) /\ (euclidean__axioms.Col M H22 K))))) as H119.
-------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder K H22 M H118).
-------------------------------------------------------------------------------- destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H120.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq K M) as H120.
-------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H22 M) /\ ((euclidean__axioms.neq K H22) /\ (euclidean__axioms.neq K M))) as H120.
--------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal K H22 M H97).
--------------------------------------------------------------------------------- destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
exact H124.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M K) as H121.
--------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric K M H120).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F G M K) as H122.
---------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel F G M H22 K H117 H119 H121).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H22 M K) as H123.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K H22 M) /\ ((euclidean__axioms.Col K M H22) /\ ((euclidean__axioms.Col M H22 K) /\ ((euclidean__axioms.Col H22 M K) /\ (euclidean__axioms.Col M K H22))))) as H123.
------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder H22 K M H119).
------------------------------------------------------------------------------------ destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
exact H130.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G L K M) as H124.
------------------------------------------------------------------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel G L K H22 M H116 H123 H120).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par G L M K) as H125.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par L G K M) /\ ((euclidean__defs.Par G L M K) /\ (euclidean__defs.Par L G M K))) as H125.
-------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip G L K M H124).
-------------------------------------------------------------------------------------- destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
exact H128.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M K G L) as H126.
-------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric G L M K H125).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M K F G) as H127.
--------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric F G M K H122).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M K G F) as H128.
---------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par K M F G) /\ ((euclidean__defs.Par M K G F) /\ (euclidean__defs.Par K M G F))) as H128.
----------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip M K F G H127).
----------------------------------------------------------------------------------------- destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
exact H131.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G L F) as H129.
----------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col G L F).
------------------------------------------------------------------------------------------intro H129.
apply (@euclidean__tactics.Col__nCol__False G L F H129).
-------------------------------------------------------------------------------------------apply (@lemma__Playfair.lemma__Playfair M K G L F H126 H128).


----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G F L) as H130.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col L G F) /\ ((euclidean__axioms.Col L F G) /\ ((euclidean__axioms.Col F G L) /\ ((euclidean__axioms.Col G F L) /\ (euclidean__axioms.Col F L G))))) as H130.
------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G L F H129).
------------------------------------------------------------------------------------------- destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
exact H137.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol F L M) as H131.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F K L) /\ ((euclidean__axioms.nCol F L M) /\ ((euclidean__axioms.nCol K L M) /\ (euclidean__axioms.nCol F K M)))) as H131.
-------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC F K L M H113).
-------------------------------------------------------------------------------------------- destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
exact H134.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L F) as H132.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F L) /\ ((euclidean__axioms.neq L M) /\ ((euclidean__axioms.neq F M) /\ ((euclidean__axioms.neq L F) /\ ((euclidean__axioms.neq M L) /\ (euclidean__axioms.neq M F)))))) as H132.
--------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct F L M H131).
--------------------------------------------------------------------------------------------- destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
exact H139.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M K L F) as H133.
--------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel M K L G F H128 H130 H132).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par L F M K) as H134.
---------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric M K L F H133).
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F L K M) as H135.
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par F L M K) /\ ((euclidean__defs.Par L F K M) /\ (euclidean__defs.Par F L K M))) as H135.
------------------------------------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip L F M K H134).
------------------------------------------------------------------------------------------------ destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
exact H139.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG F K M L) as H136.
------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------- exact H114.
------------------------------------------------------------------------------------------------- exact H135.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol F K H22) as H137.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F L K) /\ ((euclidean__axioms.nCol F K M) /\ ((euclidean__axioms.nCol L K M) /\ (euclidean__axioms.nCol F L M)))) as H137.
-------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC F L K M H135).
-------------------------------------------------------------------------------------------------- destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
exact H89.
------------------------------------------------------------------------------------------------- assert (euclidean__defs.CongA F K H22 H22 K F) as H138 by exact H90.
assert (* Cut *) (euclidean__defs.CongA F K H22 J E N) as H139.
-------------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive F K H22 H22 K F J E N H138 H52).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq K H22) as H140.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H22 M) /\ ((euclidean__axioms.neq K H22) /\ (euclidean__axioms.neq K M))) as H140.
---------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal K H22 M H97).
---------------------------------------------------------------------------------------------------- destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
exact H143.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out K H22 M) as H141.
---------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 K H22 M).
-----------------------------------------------------------------------------------------------------right.
right.
exact H97.

----------------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out K M H22) as H142.
----------------------------------------------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 K H22 M H141).
----------------------------------------------------------------------------------------------------- assert (* Cut *) (F = F) as H143.
------------------------------------------------------------------------------------------------------ apply (@logic.eq__refl Point F).
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq K F) as H144.
------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F K) /\ ((euclidean__axioms.neq K H22) /\ ((euclidean__axioms.neq F H22) /\ ((euclidean__axioms.neq K F) /\ ((euclidean__axioms.neq H22 K) /\ (euclidean__axioms.neq H22 F)))))) as H144.
-------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct F K H22 H137).
-------------------------------------------------------------------------------------------------------- destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
exact H151.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out K F F) as H145.
-------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 K F F).
---------------------------------------------------------------------------------------------------------right.
left.
exact H143.

--------------------------------------------------------------------------------------------------------- exact H144.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F K M) as H146.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F L K) /\ ((euclidean__axioms.nCol F K M) /\ ((euclidean__axioms.nCol L K M) /\ (euclidean__axioms.nCol F L M)))) as H146.
---------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC F L K M H135).
---------------------------------------------------------------------------------------------------------- destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
exact H149.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F K M F K M) as H147.
---------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive F K M H146).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F K M F K H22) as H148.
----------------------------------------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper F K M F K M F H22 H147 H145 H142).
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F K M J E N) as H149.
------------------------------------------------------------------------------------------------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive F K M F K H22 J E N H148 H139).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B O D) as H150.
------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H3.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B D O) as H151.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col O B D) /\ ((euclidean__axioms.Col O D B) /\ ((euclidean__axioms.Col D B O) /\ ((euclidean__axioms.Col B D O) /\ (euclidean__axioms.Col D O B))))) as H151.
--------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B O D H150).
--------------------------------------------------------------------------------------------------------------- destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
exact H158.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B D A) as H152.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H152.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder A B D H18).
---------------------------------------------------------------------------------------------------------------- destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
exact H155.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS A B D C) as H153.
---------------------------------------------------------------------------------------------------------------- exists O.
split.
----------------------------------------------------------------------------------------------------------------- exact H2.
----------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------ exact H151.
------------------------------------------------------------------------------------------------------------------ exact H152.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G H22 L M) as H154.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par H22 G M L) /\ ((euclidean__defs.Par G H22 L M) /\ (euclidean__defs.Par H22 G L M))) as H154.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip G H22 M L H101).
------------------------------------------------------------------------------------------------------------------ destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
exact H157.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP G H22 L M) as H155.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__paralleldef2B.lemma__paralleldef2B G H22 L M H154).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS L M G H22) as H156.
------------------------------------------------------------------------------------------------------------------- destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
destruct H84 as [H162 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
exact H161.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F K G H22) as H157.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par H22 G L M) /\ ((euclidean__defs.Par G H22 M L) /\ (euclidean__defs.Par H22 G M L))) as H157.
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip G H22 L M H154).
--------------------------------------------------------------------------------------------------------------------- destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
exact H110.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G H22 F K) as H158.
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric F K G H22 H157).
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP G H22 F K) as H159.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B G H22 F K H158).
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS F K G H22) as H160.
----------------------------------------------------------------------------------------------------------------------- destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
destruct H155 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H84 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
exact H165.
----------------------------------------------------------------------------------------------------------------------- assert (H22 = H22) as H161 by exact H105.
assert (euclidean__axioms.Col G H22 H22) as H162 by exact H108.
assert (* Cut *) (euclidean__axioms.TS K G H22 M) as H163.
------------------------------------------------------------------------------------------------------------------------ exists H22.
split.
------------------------------------------------------------------------------------------------------------------------- exact H97.
------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------- exact H162.
-------------------------------------------------------------------------------------------------------------------------- exact H59.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS F G H22 M) as H164.
------------------------------------------------------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation G H22 F K M H160 H163).
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS M G H22 F) as H165.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric G H22 F M H164).
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS L G H22 F) as H166.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation G H22 L M F H156 H165).
--------------------------------------------------------------------------------------------------------------------------- assert (exists t, (euclidean__axioms.BetS L t F) /\ ((euclidean__axioms.Col G H22 t) /\ (euclidean__axioms.nCol G H22 L))) as H167 by exact H166.
destruct H167 as [t H168].
destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
assert (* Cut *) (euclidean__axioms.Col F L G) as H173.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F G L) /\ ((euclidean__axioms.Col F L G) /\ ((euclidean__axioms.Col L G F) /\ ((euclidean__axioms.Col G L F) /\ (euclidean__axioms.Col L F G))))) as H173.
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G F L H130).
----------------------------------------------------------------------------------------------------------------------------- destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
exact H176.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L t F) as H174.
----------------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H169.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F L t) as H175.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col t L F) /\ ((euclidean__axioms.Col t F L) /\ ((euclidean__axioms.Col F L t) /\ ((euclidean__axioms.Col L F t) /\ (euclidean__axioms.Col F t L))))) as H175.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder L t F H174).
------------------------------------------------------------------------------------------------------------------------------- destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
exact H180.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq F L) as H176.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F L) /\ ((euclidean__axioms.neq L M) /\ ((euclidean__axioms.neq F M) /\ ((euclidean__axioms.neq L F) /\ ((euclidean__axioms.neq M L) /\ (euclidean__axioms.neq M F)))))) as H176.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct F L M H131).
-------------------------------------------------------------------------------------------------------------------------------- destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
exact H177.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L G t) as H177.
-------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col L G t).
---------------------------------------------------------------------------------------------------------------------------------intro H177.
apply (@euclidean__tactics.Col__nCol__False L G t H177).
----------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 F L G t H173 H175 H176).


-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col t G L) as H178.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G L t) /\ ((euclidean__axioms.Col G t L) /\ ((euclidean__axioms.Col t L G) /\ ((euclidean__axioms.Col L t G) /\ (euclidean__axioms.Col t G L))))) as H178.
---------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder L G t H177).
---------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
exact H186.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col t G H22) as H179.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H22 G t) /\ ((euclidean__axioms.Col H22 t G) /\ ((euclidean__axioms.Col t G H22) /\ ((euclidean__axioms.Col G t H22) /\ (euclidean__axioms.Col t H22 G))))) as H179.
----------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G H22 t H171).
----------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
destruct H183 as [H184 H185].
destruct H185 as [H186 H187].
exact H184.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq t G)) as H180.
----------------------------------------------------------------------------------------------------------------------------------- intro H180.
assert (* Cut *) (euclidean__axioms.Col G L H22) as H181.
------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col G L H22).
-------------------------------------------------------------------------------------------------------------------------------------intro H181.
apply (@euclidean__tactics.Col__nCol__False G L H22 H181).
--------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 t G L H22 H178 H179 H180).


------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col G H22 L) as H182.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col L G H22) /\ ((euclidean__axioms.Col L H22 G) /\ ((euclidean__axioms.Col H22 G L) /\ ((euclidean__axioms.Col G H22 L) /\ (euclidean__axioms.Col H22 L G))))) as H182.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G L H22 H181).
-------------------------------------------------------------------------------------------------------------------------------------- destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
exact H189.
------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False G H22 L H172 H182).
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS L G F) as H181.
------------------------------------------------------------------------------------------------------------------------------------ apply (@eq__ind euclidean__axioms.Point t (fun X => euclidean__axioms.BetS L X F)) with (y := G).
------------------------------------------------------------------------------------------------------------------------------------- exact H169.
-------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.NNPP (t = G) H180).

------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS F G L) as H182.
------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry L G F H181).
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists j, (euclidean__axioms.BetS F j M) /\ (euclidean__axioms.BetS K j L)) as H183.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet F K M L H136).
-------------------------------------------------------------------------------------------------------------------------------------- destruct H183 as [j H184].
destruct H184 as [H185 H186].
assert (* Cut *) (euclidean__axioms.EF A B C D F K M L) as H187.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__paste4 A B C D F G H22 j K L M O e m H50 H68 H2 H3 H97 H182 H9 H72 H185 H186).
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF F K M L A B C D) as H188.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric A B C D F K M L H187).
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS P K M) as H189.
----------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__3__7b.lemma__3__7b P K H22 M H24 H97).
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out K R M) as H190.
------------------------------------------------------------------------------------------------------------------------------------------ exists P.
split.
------------------------------------------------------------------------------------------------------------------------------------------- exact H189.
------------------------------------------------------------------------------------------------------------------------------------------- exact H32.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS F S K H22) as H191.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS F S K H22) /\ ((euclidean__defs.OS S F H22 K) /\ (euclidean__defs.OS F S H22 K))) as H191.
-------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric K H22 S F H53).
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
exact H192.
------------------------------------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.Col K H22 M) as H192 by exact H118.
assert (* Cut *) (euclidean__defs.OS F S K M) as H193.
-------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear K H22 M F S H191 H192 H120).
-------------------------------------------------------------------------------------------------------------------------------------------- exists F.
exists M.
exists L.
split.
--------------------------------------------------------------------------------------------------------------------------------------------- exact H136.
--------------------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------------------- exact H149.
---------------------------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------------------------- exact H188.
----------------------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H190.
------------------------------------------------------------------------------------------------------------------------------------------------ exact H193.
Qed.
