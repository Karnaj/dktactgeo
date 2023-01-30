Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__PGflip.
Require Export lemma__PGrotate.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__angletrichotomy2.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__crossbar2.
Require Export lemma__diagonalsmeet.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoffunique.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray2.
Require Export lemma__ray4.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export lemma__sameside2.
Require Export lemma__samesidecollinear.
Require Export lemma__samesidesymmetric.
Require Export lemma__supplementinequality.
Require Export lemma__triangletoparallelogram.
Require Export logic.
Require Export proposition__07.
Require Export proposition__23C.
Require Export proposition__31.
Require Export proposition__34.
Require Export proposition__38.
Require Export proposition__41.
Definition proposition__42 : forall A B C D E J K, (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.nCol J D K) -> ((euclidean__defs.Midpoint B E C) -> (exists X Z, (euclidean__defs.PG X E C Z) /\ ((euclidean__axioms.EF A B E C X E C Z) /\ ((euclidean__defs.CongA C E X J D K) /\ (euclidean__axioms.Col X Z A)))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro J.
intro K.
intro H.
intro H0.
intro H1.
assert (* Cut *) ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H2.
- assert ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as H2 by exact H1.
assert ((euclidean__axioms.BetS B E C) /\ (euclidean__axioms.Cong B E E C)) as __TmpHyp by exact H2.
destruct __TmpHyp as [H3 H4].
split.
-- exact H3.
-- exact H4.
- assert (* Cut *) (euclidean__axioms.Cong E B E C) as H3.
-- destruct H2 as [H3 H4].
assert (* Cut *) ((euclidean__axioms.Cong E B C E) /\ ((euclidean__axioms.Cong E B E C) /\ (euclidean__axioms.Cong B E C E))) as H5.
--- apply (@lemma__congruenceflip.lemma__congruenceflip B E E C H4).
--- destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
exact H8.
-- assert (* Cut *) (euclidean__axioms.nCol A B C) as H4.
--- destruct H2 as [H4 H5].
exact H.
--- assert (* Cut *) (euclidean__axioms.Col B E C) as H5.
---- destruct H2 as [H5 H6].
right.
right.
right.
right.
left.
exact H5.
---- assert (* Cut *) (euclidean__axioms.nCol B C A) as H6.
----- destruct H2 as [H6 H7].
assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H8.
------ apply (@lemma__NCorder.lemma__NCorder A B C H4).
------ destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H11.
----- assert (* Cut *) (euclidean__axioms.Col B C E) as H7.
------ destruct H2 as [H7 H8].
assert (* Cut *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H9.
------- apply (@lemma__collinearorder.lemma__collinearorder B E C H5).
------- destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H16.
------ assert (* Cut *) (C = C) as H8.
------- destruct H2 as [H8 H9].
apply (@logic.eq__refl Point C).
------- assert (* Cut *) (euclidean__axioms.Col B C C) as H9.
-------- right.
right.
left.
exact H8.
-------- assert (* Cut *) (euclidean__axioms.neq E C) as H10.
--------- destruct H2 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H12.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal B E C H10).
---------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H13.
--------- assert (* Cut *) (euclidean__axioms.nCol E C A) as H11.
---------- destruct H2 as [H11 H12].
apply (@euclidean__tactics.nCol__notCol E C A).
-----------apply (@euclidean__tactics.nCol__not__Col E C A).
------------apply (@lemma__NChelper.lemma__NChelper B C A E C H6 H7 H9 H10).


---------- assert (* Cut *) (exists f c, (euclidean__defs.Out E C c) /\ ((euclidean__defs.CongA f E c J D K) /\ (euclidean__defs.OS f A E C))) as H12.
----------- destruct H2 as [H12 H13].
apply (@proposition__23C.proposition__23C E C D J K A H10 H0 H11).
----------- destruct H12 as [f H13].
destruct H13 as [c H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H2 as [H19 H20].
assert (* Cut *) (euclidean__axioms.nCol B C A) as H21.
------------ assert (* Cut *) ((euclidean__axioms.nCol C E A) /\ ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol E A C) /\ (euclidean__axioms.nCol A C E))))) as H21.
------------- apply (@lemma__NCorder.lemma__NCorder E C A H11).
------------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H6.
------------ assert (* Cut *) (exists P Q M, (euclidean__axioms.BetS P A Q) /\ ((euclidean__defs.CongA Q A E A E B) /\ ((euclidean__defs.CongA Q A E B E A) /\ ((euclidean__defs.CongA E A Q B E A) /\ ((euclidean__defs.CongA P A E A E C) /\ ((euclidean__defs.CongA P A E C E A) /\ ((euclidean__defs.CongA E A P C E A) /\ ((euclidean__defs.Par P Q B C) /\ ((euclidean__axioms.Cong P A E C) /\ ((euclidean__axioms.Cong A Q B E) /\ ((euclidean__axioms.Cong A M M E) /\ ((euclidean__axioms.Cong P M M C) /\ ((euclidean__axioms.Cong B M M Q) /\ ((euclidean__axioms.BetS P M C) /\ ((euclidean__axioms.BetS B M Q) /\ (euclidean__axioms.BetS A M E)))))))))))))))) as H22.
------------- apply (@proposition__31.proposition__31 A B C E H19 H21).
------------- destruct H22 as [P H23].
destruct H23 as [Q H24].
destruct H24 as [M H25].
destruct H25 as [H26 H27].
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
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
assert (* Cut *) (euclidean__defs.CongA A E C P A E) as H56.
-------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric P A E A E C H34).
-------------- assert (* Cut *) (euclidean__axioms.nCol P A E) as H57.
--------------- apply (@euclidean__tactics.nCol__notCol P A E).
----------------apply (@euclidean__tactics.nCol__not__Col P A E).
-----------------apply (@lemma__equalanglesNC.lemma__equalanglesNC A E C P A E H56).


--------------- assert (* Cut *) (euclidean__axioms.nCol E A P) as H58.
---------------- assert (* Cut *) ((euclidean__axioms.nCol A P E) /\ ((euclidean__axioms.nCol A E P) /\ ((euclidean__axioms.nCol E P A) /\ ((euclidean__axioms.nCol P E A) /\ (euclidean__axioms.nCol E A P))))) as H58.
----------------- apply (@lemma__NCorder.lemma__NCorder P A E H57).
----------------- destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H66.
---------------- assert (* Cut *) (euclidean__defs.OS A f E C) as H59.
----------------- assert (* Cut *) ((euclidean__defs.OS A f E C) /\ ((euclidean__defs.OS f A C E) /\ (euclidean__defs.OS A f C E))) as H59.
------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric E C f A H18).
------------------ destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H60.
----------------- assert (* Cut *) (euclidean__axioms.nCol B C A) as H60.
------------------ assert (* Cut *) ((euclidean__axioms.nCol A E P) /\ ((euclidean__axioms.nCol A P E) /\ ((euclidean__axioms.nCol P E A) /\ ((euclidean__axioms.nCol E P A) /\ (euclidean__axioms.nCol P A E))))) as H60.
------------------- apply (@lemma__NCorder.lemma__NCorder E A P H58).
------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H21.
------------------ assert (* Cut *) (euclidean__axioms.Col B C E) as H61.
------------------- assert (* Cut *) ((euclidean__axioms.Col C B C) /\ ((euclidean__axioms.Col C C B) /\ ((euclidean__axioms.Col C B C) /\ ((euclidean__axioms.Col B C C) /\ (euclidean__axioms.Col C C B))))) as H61.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder B C C H9).
-------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H7.
------------------- assert (* Cut *) (B = B) as H62.
-------------------- apply (@logic.eq__refl Point B).
-------------------- assert (* Cut *) (A = A) as H63.
--------------------- apply (@logic.eq__refl Point A).
--------------------- assert (* Cut *) (euclidean__axioms.Col B C B) as H64.
---------------------- right.
left.
exact H62.
---------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H65.
----------------------- assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B C))) as H65.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal B E C H19).
------------------------ destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H68.
----------------------- assert (* Cut *) (euclidean__axioms.nCol B E A) as H66.
------------------------ apply (@euclidean__tactics.nCol__notCol B E A).
-------------------------apply (@euclidean__tactics.nCol__not__Col B E A).
--------------------------apply (@lemma__NChelper.lemma__NChelper B C A B E H60 H64 H61 H65).


------------------------ assert (C = C) as H67 by exact H8.
assert (euclidean__axioms.Col B C C) as H68 by exact H9.
assert (* Cut *) (euclidean__axioms.neq E C) as H69.
------------------------- assert (* Cut *) ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A E))) as H69.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A M E H55).
-------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H10.
------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H70.
-------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E C H69).
-------------------------- assert (* Cut *) (euclidean__axioms.nCol C E A) as H71.
--------------------------- apply (@euclidean__tactics.nCol__notCol C E A).
----------------------------apply (@euclidean__tactics.nCol__not__Col C E A).
-----------------------------apply (@lemma__NChelper.lemma__NChelper B C A C E H60 H68 H61 H70).


--------------------------- assert (* Cut *) (euclidean__axioms.neq E A) as H72.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A C)))))) as H72.
----------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct C E A H71).
----------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H75.
---------------------------- assert (* Cut *) (~(~(euclidean__defs.Meet E f P Q))) as H73.
----------------------------- intro H73.
assert (* Cut *) (~(euclidean__defs.LtA C E f C E A)) as H74.
------------------------------ intro H74.
assert (* Cut *) (euclidean__defs.Out E C C) as H75.
------------------------------- apply (@lemma__ray4.lemma__ray4 E C C).
--------------------------------right.
left.
exact H67.

-------------------------------- exact H69.
------------------------------- assert (* Cut *) (euclidean__defs.Out E A A) as H76.
-------------------------------- apply (@lemma__ray4.lemma__ray4 E A A).
---------------------------------right.
left.
exact H63.

--------------------------------- exact H72.
-------------------------------- assert (* Cut *) (exists m, (euclidean__axioms.BetS A m C) /\ (euclidean__defs.Out E f m)) as H77.
--------------------------------- apply (@lemma__crossbar2.lemma__crossbar2 f E C A C A H74 H18 H75 H76).
--------------------------------- destruct H77 as [m H78].
destruct H78 as [H79 H80].
assert (* Cut *) (euclidean__axioms.BetS C m A) as H81.
---------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A m C H79).
---------------------------------- assert (* Cut *) (euclidean__axioms.BetS C M P) as H82.
----------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry P M C H52).
----------------------------------- assert (* Cut *) (euclidean__axioms.BetS E M A) as H83.
------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry A M E H55).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong M E A M) as H84.
------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric M A M E H46).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E M A M) as H85.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E M M A) /\ ((euclidean__axioms.Cong E M A M) /\ (euclidean__axioms.Cong M E M A))) as H85.
--------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip M E A M H84).
--------------------------------------- destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H88.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M C P M) as H86.
--------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric M P M C H48).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M C M P) as H87.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C M M P) /\ ((euclidean__axioms.Cong C M P M) /\ (euclidean__axioms.Cong M C M P))) as H87.
----------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip M C P M H86).
----------------------------------------- destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H91.
---------------------------------------- assert (* Cut *) (exists F, (euclidean__axioms.BetS E m F) /\ (euclidean__axioms.BetS P A F)) as H88.
----------------------------------------- apply (@euclidean__axioms.postulate__Euclid5 m E A C P M H82 H83 H81 H85 H87 H58).
----------------------------------------- destruct H88 as [F H89].
destruct H89 as [H90 H91].
assert (* Cut *) (euclidean__axioms.Col E m F) as H92.
------------------------------------------ right.
right.
right.
right.
left.
exact H90.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col m E F) as H93.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m E F) /\ ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))))) as H93.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E m F H92).
-------------------------------------------- destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
exact H94.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E f m) as H94.
-------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear E f m H80).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m E f) as H95.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col f E m) /\ ((euclidean__axioms.Col f m E) /\ ((euclidean__axioms.Col m E f) /\ ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E))))) as H95.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E f m H94).
---------------------------------------------- destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
exact H100.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E m) as H96.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F))) as H96.
----------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E m F H90).
----------------------------------------------- destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
exact H99.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq m E) as H97.
----------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E m H96).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E f F) as H98.
------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col E f F).
-------------------------------------------------intro H98.
apply (@euclidean__tactics.Col__nCol__False E f F H98).
--------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 m E f F H95 H93 H97).


------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P A F) as H99.
------------------------------------------------- right.
right.
right.
right.
left.
exact H91.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P A Q) as H100.
-------------------------------------------------- right.
right.
right.
right.
left.
exact H26.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P A) as H101.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P F))) as H101.
---------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal P A F H91).
---------------------------------------------------- destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H104.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A P) as H102.
---------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric P A H101).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A P F) as H103.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A P F) /\ ((euclidean__axioms.Col A F P) /\ ((euclidean__axioms.Col F P A) /\ ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P))))) as H103.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder P A F H99).
------------------------------------------------------ destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
exact H104.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A P Q) as H104.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P))))) as H104.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder P A Q H100).
------------------------------------------------------- destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
exact H105.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P F Q) as H105.
------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col P F Q).
--------------------------------------------------------intro H105.
apply (@euclidean__tactics.Col__nCol__False P F Q H105).
---------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 A P F Q H103 H104 H102).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P Q F) as H106.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col F Q P) /\ ((euclidean__axioms.Col Q P F) /\ ((euclidean__axioms.Col P Q F) /\ (euclidean__axioms.Col Q F P))))) as H106.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder P F Q H105).
--------------------------------------------------------- destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
exact H113.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E f) as H107.
--------------------------------------------------------- apply (@lemma__ray2.lemma__ray2 E f m H80).
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H108.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q))) as H108.
----------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal P A Q H26).
----------------------------------------------------------- destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
exact H112.
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H109.
----------------------------------------------------------- exists F.
split.
------------------------------------------------------------ exact H107.
------------------------------------------------------------ split.
------------------------------------------------------------- exact H108.
------------------------------------------------------------- split.
-------------------------------------------------------------- exact H98.
-------------------------------------------------------------- exact H106.
----------------------------------------------------------- apply (@H73 H109).
------------------------------ assert (* Cut *) (euclidean__axioms.Col E C B) as H75.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H75.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C E H61).
-------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H83.
------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H76.
-------------------------------- assert (* Cut *) ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A E))) as H76.
--------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A M E H55).
--------------------------------- destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H65.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H77.
--------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B E H76).
--------------------------------- assert (* Cut *) (euclidean__defs.OS A f E B) as H78.
---------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear E C B A f H59 H75 H77).
---------------------------------- assert (* Cut *) (euclidean__defs.OS f A E B) as H79.
----------------------------------- assert (* Cut *) ((euclidean__defs.OS f A E B) /\ ((euclidean__defs.OS A f B E) /\ (euclidean__defs.OS f A B E))) as H79.
------------------------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric E B A f H78).
------------------------------------ destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H80.
----------------------------------- assert (* Cut *) (euclidean__axioms.BetS C E B) as H80.
------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry B E C H19).
------------------------------------ assert (A = A) as H81 by exact H63.
assert (* Cut *) (f = f) as H82.
------------------------------------- apply (@logic.eq__refl Point f).
------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E B f) as H83.
-------------------------------------- assert (exists X U V, (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS f U X) /\ ((euclidean__axioms.BetS A V X) /\ ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A)))))) as H83 by exact H79.
assert (exists X U V, (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS f U X) /\ ((euclidean__axioms.BetS A V X) /\ ((euclidean__axioms.nCol E B f) /\ (euclidean__axioms.nCol E B A)))))) as __TmpHyp by exact H83.
destruct __TmpHyp as [x H84].
destruct H84 as [x0 H85].
destruct H85 as [x1 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
assert (exists X U V, (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS f V X) /\ ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f)))))) as H97 by exact H78.
assert (exists X U V, (euclidean__axioms.Col E B U) /\ ((euclidean__axioms.Col E B V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS f V X) /\ ((euclidean__axioms.nCol E B A) /\ (euclidean__axioms.nCol E B f)))))) as __TmpHyp0 by exact H97.
destruct __TmpHyp0 as [x2 H98].
destruct H98 as [x3 H99].
destruct H99 as [x4 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
assert (exists X U V, (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS f V X) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f)))))) as H111 by exact H59.
assert (exists X U V, (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS A U X) /\ ((euclidean__axioms.BetS f V X) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol E C f)))))) as __TmpHyp1 by exact H111.
destruct __TmpHyp1 as [x5 H112].
destruct H112 as [x6 H113].
destruct H113 as [x7 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
assert (exists X U V, (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS f U X) /\ ((euclidean__axioms.BetS A V X) /\ ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A)))))) as H125 by exact H18.
assert (exists X U V, (euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.BetS f U X) /\ ((euclidean__axioms.BetS A V X) /\ ((euclidean__axioms.nCol E C f) /\ (euclidean__axioms.nCol E C A)))))) as __TmpHyp2 by exact H125.
destruct __TmpHyp2 as [x8 H126].
destruct H126 as [x9 H127].
destruct H127 as [x10 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
exact H110.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq E f) as H84.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq B f) /\ ((euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq f B) /\ (euclidean__axioms.neq f E)))))) as H84.
---------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct E B f H83).
---------------------------------------- destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
exact H89.
--------------------------------------- assert (euclidean__axioms.Col B E C) as H85 by exact H5.
assert (* Cut *) (euclidean__axioms.Col E B C) as H86.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col E C B) /\ ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col B C E) /\ (euclidean__axioms.Col C E B))))) as H86.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B E C H85).
----------------------------------------- destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
exact H87.
---------------------------------------- assert (* Cut *) (E = E) as H87.
----------------------------------------- apply (@logic.eq__refl Point E).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B E) as H88.
------------------------------------------ right.
left.
exact H87.
------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol E C f) as H89.
------------------------------------------- apply (@euclidean__tactics.nCol__notCol E C f).
--------------------------------------------apply (@euclidean__tactics.nCol__not__Col E C f).
---------------------------------------------apply (@lemma__NChelper.lemma__NChelper E B f E C H83 H88 H86 H69).


------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E f) as H90.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C E f) /\ ((euclidean__axioms.nCol C f E) /\ ((euclidean__axioms.nCol f E C) /\ ((euclidean__axioms.nCol E f C) /\ (euclidean__axioms.nCol f C E))))) as H90.
--------------------------------------------- apply (@lemma__NCorder.lemma__NCorder E C f H89).
--------------------------------------------- destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
exact H91.
-------------------------------------------- assert (* Cut *) (~(euclidean__defs.LtA C E A C E f)) as H91.
--------------------------------------------- intro H91.
assert (* Cut *) (euclidean__defs.Out E A A) as H92.
---------------------------------------------- apply (@lemma__ray4.lemma__ray4 E A A).
-----------------------------------------------right.
left.
exact H81.

----------------------------------------------- exact H72.
---------------------------------------------- assert (* Cut *) (euclidean__defs.Out E f f) as H93.
----------------------------------------------- apply (@lemma__ray4.lemma__ray4 E f f).
------------------------------------------------right.
left.
exact H82.

------------------------------------------------ exact H84.
----------------------------------------------- assert (* Cut *) (euclidean__defs.Supp C E A A B) as H94.
------------------------------------------------ split.
------------------------------------------------- exact H92.
------------------------------------------------- exact H80.
------------------------------------------------ assert (* Cut *) (euclidean__defs.Supp C E f f B) as H95.
------------------------------------------------- split.
-------------------------------------------------- exact H93.
-------------------------------------------------- exact H80.
------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA f E B A E B) as H96.
-------------------------------------------------- apply (@lemma__supplementinequality.lemma__supplementinequality C E f f B C E A A B H95 H94 H91).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E f) as H97.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B E f) /\ ((euclidean__axioms.nCol B f E) /\ ((euclidean__axioms.nCol f E B) /\ ((euclidean__axioms.nCol E f B) /\ (euclidean__axioms.nCol f B E))))) as H97.
---------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder E B f H83).
---------------------------------------------------- destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H98.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B E f f E B) as H98.
---------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B E f H97).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA B E f A E B) as H99.
----------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 f E B A E B B E f H96 H98).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B E A A E B) as H100.
------------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B E A H66).
------------------------------------------------------ assert (* Cut *) (euclidean__defs.LtA B E f B E A) as H101.
------------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence B E f A E B B E A H99 H100).
------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E B B) as H102.
-------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 E B B).
---------------------------------------------------------right.
left.
exact H62.

--------------------------------------------------------- exact H77.
-------------------------------------------------------- assert (euclidean__defs.Out E A A) as H103 by exact H92.
assert (* Cut *) (exists m, (euclidean__axioms.BetS A m B) /\ (euclidean__defs.Out E f m)) as H104.
--------------------------------------------------------- apply (@lemma__crossbar2.lemma__crossbar2 f E B A B A H101 H79 H102 H103).
--------------------------------------------------------- destruct H104 as [m H105].
destruct H105 as [H106 H107].
assert (* Cut *) (euclidean__axioms.BetS B m A) as H108.
---------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A m B H106).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E M A) as H109.
----------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A M E H55).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M E A M) as H110.
------------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric M A M E H46).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong E M A M) as H111.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong E M M A) /\ ((euclidean__axioms.Cong E M A M) /\ (euclidean__axioms.Cong M E M A))) as H111.
-------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip M E A M H110).
-------------------------------------------------------------- destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
exact H114.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M B M Q) as H112.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M B Q M) /\ ((euclidean__axioms.Cong M B M Q) /\ (euclidean__axioms.Cong B M Q M))) as H112.
--------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip B M M Q H50).
--------------------------------------------------------------- destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
exact H115.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol P A E) as H113.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B f) /\ ((euclidean__axioms.nCol E f B) /\ ((euclidean__axioms.nCol f B E) /\ ((euclidean__axioms.nCol B f E) /\ (euclidean__axioms.nCol f E B))))) as H113.
---------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder B E f H97).
---------------------------------------------------------------- destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
exact H57.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P A Q) as H114.
---------------------------------------------------------------- right.
right.
right.
right.
left.
exact H26.
---------------------------------------------------------------- assert (A = A) as H115 by exact H81.
assert (* Cut *) (euclidean__axioms.Col P A A) as H116.
----------------------------------------------------------------- right.
right.
left.
exact H115.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A Q) as H117.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q))) as H117.
------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal P A Q H26).
------------------------------------------------------------------- destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
exact H118.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq Q A) as H118.
------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A Q H117).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol Q A E) as H119.
-------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol Q A E).
---------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col Q A E).
----------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper P A E Q A H113 H114 H116 H118).


-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E A Q) as H120.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A Q E) /\ ((euclidean__axioms.nCol A E Q) /\ ((euclidean__axioms.nCol E Q A) /\ ((euclidean__axioms.nCol Q E A) /\ (euclidean__axioms.nCol E A Q))))) as H120.
---------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder Q A E H119).
---------------------------------------------------------------------- destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
exact H128.
--------------------------------------------------------------------- assert (* Cut *) (exists F, (euclidean__axioms.BetS E m F) /\ (euclidean__axioms.BetS Q A F)) as H121.
---------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Euclid5 m E A B Q M H54 H109 H108 H111 H112 H120).
---------------------------------------------------------------------- destruct H121 as [F H122].
destruct H122 as [H123 H124].
assert (* Cut *) (euclidean__axioms.Col E m F) as H125.
----------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H123.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m E F) as H126.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col m E F) /\ ((euclidean__axioms.Col m F E) /\ ((euclidean__axioms.Col F E m) /\ ((euclidean__axioms.Col E F m) /\ (euclidean__axioms.Col F m E))))) as H126.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E m F H125).
------------------------------------------------------------------------- destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
exact H127.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E f m) as H127.
------------------------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear E f m H107).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m E f) as H128.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col f E m) /\ ((euclidean__axioms.Col f m E) /\ ((euclidean__axioms.Col m E f) /\ ((euclidean__axioms.Col E m f) /\ (euclidean__axioms.Col m f E))))) as H128.
--------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E f m H127).
--------------------------------------------------------------------------- destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
exact H133.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E m) as H129.
--------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E F))) as H129.
---------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E m F H123).
---------------------------------------------------------------------------- destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
exact H132.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq m E) as H130.
---------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E m H129).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E f F) as H131.
----------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E f F).
------------------------------------------------------------------------------intro H131.
apply (@euclidean__tactics.Col__nCol__False E f F H131).
-------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 m E f F H128 H126 H130).


----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q A F) as H132.
------------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H124.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS Q A P) as H133.
------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry P A Q H26).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q A P) as H134.
-------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H133.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q A) as H135.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q P))) as H135.
---------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal Q A P H133).
---------------------------------------------------------------------------------- destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
exact H138.
--------------------------------------------------------------------------------- assert (euclidean__axioms.neq A Q) as H136 by exact H117.
assert (* Cut *) (euclidean__axioms.Col A Q F) as H137.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A Q F) /\ ((euclidean__axioms.Col A F Q) /\ ((euclidean__axioms.Col F Q A) /\ ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q))))) as H137.
----------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder Q A F H132).
----------------------------------------------------------------------------------- destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
exact H138.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A Q P) as H138.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P Q A) /\ ((euclidean__axioms.Col Q P A) /\ (euclidean__axioms.Col P A Q))))) as H138.
------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder Q A P H134).
------------------------------------------------------------------------------------ destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
exact H139.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q F P) as H139.
------------------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col Q F P).
-------------------------------------------------------------------------------------intro H139.
apply (@euclidean__tactics.Col__nCol__False Q F P H139).
--------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 A Q F P H137 H138 H136).


------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P Q F) as H140.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F Q P) /\ ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col P Q F) /\ ((euclidean__axioms.Col Q P F) /\ (euclidean__axioms.Col P F Q))))) as H140.
-------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder Q F P H139).
-------------------------------------------------------------------------------------- destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
exact H145.
------------------------------------------------------------------------------------- assert (euclidean__axioms.neq E f) as H141 by exact H84.
assert (* Cut *) (euclidean__axioms.neq Q P) as H142.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A P) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q P))) as H142.
--------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal Q A P H133).
--------------------------------------------------------------------------------------- destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
exact H146.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H143.
--------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric Q P H142).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H144.
---------------------------------------------------------------------------------------- exists F.
split.
----------------------------------------------------------------------------------------- exact H141.
----------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------ exact H143.
------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------- exact H131.
------------------------------------------------------------------------------------------- exact H140.
---------------------------------------------------------------------------------------- apply (@H73 H144).
--------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.CongA C E A C E f))) as H92.
---------------------------------------------- intro H92.
assert (* Cut *) (euclidean__defs.LtA C E A C E f) as H93.
----------------------------------------------- apply (@lemma__angletrichotomy2.lemma__angletrichotomy2 C E A C E f H71 H90 H92 H74).
----------------------------------------------- apply (@H91 H93).
---------------------------------------------- assert (* Cut *) (exists d a p q, (euclidean__defs.Out E C d) /\ ((euclidean__defs.Out E A a) /\ ((euclidean__defs.Out E C p) /\ ((euclidean__defs.Out E f q) /\ ((euclidean__axioms.Cong E d E p) /\ ((euclidean__axioms.Cong E a E q) /\ ((euclidean__axioms.Cong d a p q) /\ (euclidean__axioms.nCol C E A)))))))) as H93.
----------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H93.
------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
------------------------------------------------ exact H93.
----------------------------------------------- destruct H93 as [d H94].
destruct H94 as [a H95].
destruct H95 as [p H96].
destruct H96 as [q H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
assert (* Cut *) (euclidean__axioms.Col P Q A) as H112.
------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H112.
------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
------------------------------------------------- right.
right.
right.
right.
right.
exact H26.
------------------------------------------------ assert (* Cut *) (d = p) as H113.
------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H113.
-------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
-------------------------------------------------- apply (@lemma__layoffunique.lemma__layoffunique E C d p H98 H102 H106).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong d a d q) as H114.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H114.
--------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
--------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point p (fun d0 => (euclidean__defs.Out E C d0) -> ((euclidean__axioms.Cong E d0 E p) -> ((euclidean__axioms.Cong d0 a p q) -> (euclidean__axioms.Cong d0 a d0 q))))) with (x := d).
----------------------------------------------------intro H115.
intro H116.
intro H117.
exact H117.

---------------------------------------------------- exact H113.
---------------------------------------------------- exact H98.
---------------------------------------------------- exact H106.
---------------------------------------------------- exact H110.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a d q d) as H115.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong a d q d) /\ ((euclidean__axioms.Cong a d d q) /\ (euclidean__axioms.Cong d a q d))) as H115.
---------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip d a d q H114).
---------------------------------------------------- destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
exact H116.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong a E q E) as H116.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong a E q E) /\ ((euclidean__axioms.Cong a E E q) /\ (euclidean__axioms.Cong E a q E))) as H116.
----------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip E a E q H108).
----------------------------------------------------- destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
exact H117.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E d) as H117.
----------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H117.
------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
------------------------------------------------------ apply (@lemma__raystrict.lemma__raystrict E C d H98).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C d) as H118.
------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H118.
------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear E C d H98).
------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS A f E d) as H119.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H119.
-------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
-------------------------------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear E C d A f H59 H118 H117).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E d E) as H120.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H120.
--------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
--------------------------------------------------------- right.
left.
exact H87.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E E d) as H121.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col d E E) /\ ((euclidean__axioms.Col d E E) /\ ((euclidean__axioms.Col E E d) /\ ((euclidean__axioms.Col E E d) /\ (euclidean__axioms.Col E d E))))) as H121.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E d E H120).
---------------------------------------------------------- destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
exact H128.
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A q E d) as H122.
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H122.
----------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
----------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 E E d A f q H119 H121 H104).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS q A E d) as H123.
----------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS q A E d) /\ ((euclidean__defs.OS A q d E) /\ (euclidean__defs.OS q A d E))) as H123.
------------------------------------------------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric E d A q H122).
------------------------------------------------------------ destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H124.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS q a E d) as H124.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H124.
------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
------------------------------------------------------------- apply (@lemma__sameside2.lemma__sameside2 E E d q A a H123 H121 H100).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS a q E d) as H125.
------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS a q E d) /\ ((euclidean__defs.OS q a d E) /\ (euclidean__defs.OS a q d E))) as H125.
-------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric E d q a H124).
-------------------------------------------------------------- destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
exact H126.
------------------------------------------------------------- assert (* Cut *) (a = q) as H126.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H126.
--------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
--------------------------------------------------------------- apply (@proposition__07.proposition__07 E d a q H117 H116 H115 H125).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A a) as H127.
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H127.
---------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
---------------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear E A a H100).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E f q) as H128.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H128.
----------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
----------------------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear E f q H104).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A q) as H129.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H129.
------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point q (fun a0 => (euclidean__defs.Out E A a0) -> ((euclidean__axioms.Cong E a0 E q) -> ((euclidean__axioms.Cong d a0 p q) -> ((euclidean__axioms.Cong d a0 d q) -> ((euclidean__axioms.Cong a0 d q d) -> ((euclidean__axioms.Cong a0 E q E) -> ((euclidean__defs.OS q a0 E d) -> ((euclidean__defs.OS a0 q E d) -> ((euclidean__axioms.Col E A a0) -> (euclidean__axioms.Col E A q))))))))))) with (x := a).
-------------------------------------------------------------------intro H130.
intro H131.
intro H132.
intro H133.
intro H134.
intro H135.
intro H136.
intro H137.
intro H138.
apply (@eq__ind__r euclidean__axioms.Point p (fun d0 => (euclidean__defs.Out E C d0) -> ((euclidean__axioms.Cong E d0 E p) -> ((euclidean__axioms.Cong d0 q p q) -> ((euclidean__axioms.Cong q d0 q d0) -> ((euclidean__axioms.Cong d0 q d0 q) -> ((euclidean__axioms.neq E d0) -> ((euclidean__axioms.Col E C d0) -> ((euclidean__defs.OS A f E d0) -> ((euclidean__axioms.Col E d0 E) -> ((euclidean__axioms.Col E E d0) -> ((euclidean__defs.OS A q E d0) -> ((euclidean__defs.OS q A E d0) -> ((euclidean__defs.OS q q E d0) -> ((euclidean__defs.OS q q E d0) -> (euclidean__axioms.Col E A q)))))))))))))))) with (x := d).
--------------------------------------------------------------------intro H139.
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
exact H138.

-------------------------------------------------------------------- exact H113.
-------------------------------------------------------------------- exact H98.
-------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------- exact H132.
-------------------------------------------------------------------- exact H134.
-------------------------------------------------------------------- exact H133.
-------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------- exact H118.
-------------------------------------------------------------------- exact H119.
-------------------------------------------------------------------- exact H120.
-------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------- exact H122.
-------------------------------------------------------------------- exact H123.
-------------------------------------------------------------------- exact H137.
-------------------------------------------------------------------- exact H136.

------------------------------------------------------------------- exact H126.
------------------------------------------------------------------- exact H100.
------------------------------------------------------------------- exact H108.
------------------------------------------------------------------- exact H110.
------------------------------------------------------------------- exact H114.
------------------------------------------------------------------- exact H115.
------------------------------------------------------------------- exact H116.
------------------------------------------------------------------- exact H124.
------------------------------------------------------------------- exact H125.
------------------------------------------------------------------- exact H127.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col q E A) as H130.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A E q) /\ ((euclidean__axioms.Col A q E) /\ ((euclidean__axioms.Col q E A) /\ ((euclidean__axioms.Col E q A) /\ (euclidean__axioms.Col q A E))))) as H130.
------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E A q H129).
------------------------------------------------------------------- destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
exact H135.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col q E f) as H131.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col f E q) /\ ((euclidean__axioms.Col f q E) /\ ((euclidean__axioms.Col q E f) /\ ((euclidean__axioms.Col E q f) /\ (euclidean__axioms.Col q f E))))) as H131.
-------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E f q H128).
-------------------------------------------------------------------- destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
exact H136.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E q) as H132.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H132.
--------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
--------------------------------------------------------------------- apply (@lemma__raystrict.lemma__raystrict E f q H104).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq q E) as H133.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H133.
---------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
---------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E q H132).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A f) as H134.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H134.
----------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
----------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E A f).
------------------------------------------------------------------------intro H135.
apply (@euclidean__tactics.Col__nCol__False E A f H135).
-------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 q E A f H130 H131 H133).


---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E f A) as H135.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A E f) /\ ((euclidean__axioms.Col A f E) /\ ((euclidean__axioms.Col f E A) /\ ((euclidean__axioms.Col E f A) /\ (euclidean__axioms.Col f A E))))) as H135.
------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder E A f H134).
------------------------------------------------------------------------ destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
exact H142.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H136.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q))) as H136.
------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal P A Q H26).
------------------------------------------------------------------------- destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
exact H140.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H137.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E A C E f) as H137.
-------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.CongA C E A C E f) H92).
-------------------------------------------------------------------------- exists A.
split.
--------------------------------------------------------------------------- exact H84.
--------------------------------------------------------------------------- split.
---------------------------------------------------------------------------- exact H136.
---------------------------------------------------------------------------- split.
----------------------------------------------------------------------------- exact H135.
----------------------------------------------------------------------------- exact H112.
------------------------------------------------------------------------- apply (@H73 H137).
----------------------------- assert (* Cut *) (exists F, (euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f F) /\ (euclidean__axioms.Col P Q F)))) as H74.
------------------------------ assert (* Cut *) (exists X, (euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f X) /\ (euclidean__axioms.Col P Q X)))) as H74.
------------------------------- apply (@euclidean__tactics.NNPP (exists X, (euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f X) /\ (euclidean__axioms.Col P Q X)))) H73).
------------------------------- assert (exists X, (euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f X) /\ (euclidean__axioms.Col P Q X)))) as H75 by exact H74.
assert (exists X, (euclidean__axioms.neq E f) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E f X) /\ (euclidean__axioms.Col P Q X)))) as __TmpHyp by exact H75.
destruct __TmpHyp as [x H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exists x.
split.
-------------------------------- exact H77.
-------------------------------- split.
--------------------------------- exact H79.
--------------------------------- split.
---------------------------------- exact H81.
---------------------------------- exact H82.
------------------------------ destruct H74 as [F H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
assert (* Cut *) (euclidean__axioms.neq C E) as H82.
------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H82.
-------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------- exact H70.
------------------------------- assert (* Cut *) (euclidean__defs.Par P Q E C) as H83.
-------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H83.
--------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel P Q E B C H40 H61 H69).
-------------------------------- assert (* Cut *) (euclidean__defs.Par E C P Q) as H84.
--------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H84.
---------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric P Q E C H83).
--------------------------------- assert (* Cut *) (exists G, (euclidean__defs.PG F G C E) /\ (euclidean__axioms.Col P Q G)) as H85.
---------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H85.
----------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------- apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram F C E P Q H84 H81).
---------------------------------- destruct H85 as [G H86].
destruct H86 as [H87 H88].
assert (* Cut *) (euclidean__defs.PG G F E C) as H89.
----------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H89.
------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------ apply (@lemma__PGflip.lemma__PGflip F G C E H87).
----------------------------------- assert (* Cut *) (euclidean__defs.PG F E C G) as H90.
------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H90.
------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate G F E C H89).
------------------------------------ assert (* Cut *) (euclidean__axioms.Col P A Q) as H91.
------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H91.
-------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------- right.
right.
right.
right.
left.
exact H26.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col P Q A) as H92.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P))))) as H92.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder P A Q H91).
--------------------------------------- destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
exact H99.
-------------------------------------- assert (* Cut *) (euclidean__defs.Par F E C G) as H93.
--------------------------------------- destruct H90 as [H93 H94].
destruct H89 as [H95 H96].
destruct H87 as [H97 H98].
exact H93.
--------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F E G) as H94.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F E C) /\ ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)))) as H94.
----------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC F E C G H93).
----------------------------------------- destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
exact H100.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq F G) as H95.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq G E) /\ (euclidean__axioms.neq G F)))))) as H95.
------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct F E G H94).
------------------------------------------ destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H100.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col F G A) as H96.
------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H96.
------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------- apply (@euclidean__tactics.not__nCol__Col F G A).
--------------------------------------------intro H97.
apply (@euclidean__tactics.Col__nCol__False F G A H97).
---------------------------------------------apply (@lemma__collinear5.lemma__collinear5 P Q F G A H78 H81 H88 H92).


------------------------------------------ assert (* Cut *) (euclidean__axioms.ET F E C A E C) as H97.
------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H97.
-------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------- apply (@proposition__41.proposition__41 F E C G A H90 H96).
------------------------------------------- assert (* Cut *) (euclidean__defs.Par P Q C B) as H98.
-------------------------------------------- assert (* Cut *) ((euclidean__defs.Par Q P B C) /\ ((euclidean__defs.Par P Q C B) /\ (euclidean__defs.Par Q P C B))) as H98.
--------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip P Q B C H40).
--------------------------------------------- destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
exact H101.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B E) as H99.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H99.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C E H61).
---------------------------------------------- destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
exact H100.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E B) as H100.
---------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H100.
----------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B E H65).
---------------------------------------------- assert (* Cut *) (euclidean__defs.Par P Q E B) as H101.
----------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H101.
------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel P Q E C B H98 H99 H100).
----------------------------------------------- assert (* Cut *) (euclidean__defs.Par P Q B E) as H102.
------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par Q P E B) /\ ((euclidean__defs.Par P Q B E) /\ (euclidean__defs.Par Q P B E))) as H102.
------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip P Q E B H101).
------------------------------------------------- destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
exact H105.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B E E C) as H103.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M B Q M) /\ ((euclidean__axioms.Cong M B M Q) /\ (euclidean__axioms.Cong B M Q M))) as H103.
-------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip B M M Q H50).
-------------------------------------------------- destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
exact H20.
------------------------------------------------- assert (* Cut *) (E = E) as H104.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H104.
--------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------- apply (@logic.eq__refl Point E).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E E) as H105.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H105.
---------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------- right.
right.
left.
exact H104.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B E A E C) as H106.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H106.
----------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------- apply (@proposition__38.proposition__38 A B E A E C P Q H102 H92 H92 H103 H105 H5).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E C A B E) as H107.
----------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H107.
------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------ apply (@euclidean__axioms.axiom__ETsymmetric A B E A E C H106).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E C A E B) as H108.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.ET A E C B E A) /\ ((euclidean__axioms.ET A E C A E B) /\ ((euclidean__axioms.ET A E C B A E) /\ ((euclidean__axioms.ET A E C E B A) /\ (euclidean__axioms.ET A E C E A B))))) as H108.
------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation A E C A B E H107).
------------------------------------------------------- destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
exact H111.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET A E B A E C) as H109.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H109.
-------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric A E C A E B H108).
------------------------------------------------------- assert (* Cut *) (E = E) as H110.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H110.
--------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------- exact H104.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A E E) as H111.
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H111.
---------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------- right.
right.
left.
exact H110.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A E B) as H112.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E B A) /\ ((euclidean__axioms.nCol E A B) /\ ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol B A E) /\ (euclidean__axioms.nCol A E B))))) as H112.
----------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder B E A H66).
----------------------------------------------------------- destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
exact H120.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS B A E C) as H113.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H113.
------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------ exists E.
split.
------------------------------------------------------------- exact H19.
------------------------------------------------------------- split.
-------------------------------------------------------------- exact H111.
-------------------------------------------------------------- exact H112.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG E F G C) as H114.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H114.
------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------- apply (@lemma__PGflip.lemma__PGflip F E C G H90).
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong__3 F E C C G F) as H115.
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H115.
-------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H116.
--------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
---------------------------------------------------------------- apply (@proposition__34.proposition__34 A0 B0 C0 D0 __).
---------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
--------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H117.
---------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
----------------------------------------------------------------- apply (@H116 A0 B0 C0 D0 __).
----------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
---------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H118.
----------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
------------------------------------------------------------------ apply (@H117 A0 B0 C0 D0 __).
------------------------------------------------------------------ destruct __0 as [__0 __1].
exact __1.
----------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H119.
------------------------------------------------------------------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
------------------------------------------------------------------- apply (@H118 A0 B0 C0 D0 __).
------------------------------------------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------------------------------------------ apply (@H119 E C F G H114).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F E C C G F) as H116.
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H116.
--------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------- apply (@euclidean__axioms.axiom__congruentequal F E C C G F H115).
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F E C F C G) as H117.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F E C G F C) /\ ((euclidean__axioms.ET F E C C F G) /\ ((euclidean__axioms.ET F E C G C F) /\ ((euclidean__axioms.ET F E C F G C) /\ (euclidean__axioms.ET F E C F C G))))) as H117.
---------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation F E C C G F H116).
---------------------------------------------------------------- destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
exact H125.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F C G F E C) as H118.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H118.
----------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric F E C F C G H117).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F C G F C E) as H119.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F C G E C F) /\ ((euclidean__axioms.ET F C G F C E) /\ ((euclidean__axioms.ET F C G E F C) /\ ((euclidean__axioms.ET F C G C E F) /\ (euclidean__axioms.ET F C G C F E))))) as H119.
------------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETpermutation F C G F E C H118).
------------------------------------------------------------------ destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H122.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F C E F C G) as H120.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H120.
------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric F C G F C E H119).
------------------------------------------------------------------ assert (* Cut *) (exists m, (euclidean__axioms.BetS E m G) /\ (euclidean__axioms.BetS F m C)) as H121.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H121.
-------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet E F G C H114).
------------------------------------------------------------------- destruct H121 as [m H122].
destruct H122 as [H123 H124].
assert (* Cut *) (euclidean__axioms.Col F m C) as H125.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H125.
--------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H124.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F C m) as H126.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m F C) /\ ((euclidean__axioms.Col m C F) /\ ((euclidean__axioms.Col C F m) /\ ((euclidean__axioms.Col F C m) /\ (euclidean__axioms.Col C m F))))) as H126.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F m C H125).
---------------------------------------------------------------------- destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
exact H133.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F E C G) as H127.
---------------------------------------------------------------------- destruct H114 as [H127 H128].
destruct H90 as [H129 H130].
destruct H89 as [H131 H132].
destruct H87 as [H133 H134].
exact H93.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F E C) as H128.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F E C) /\ ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)))) as H128.
------------------------------------------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC F E C G H127).
------------------------------------------------------------------------ destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
exact H129.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F C E) as H129.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol E C F) /\ ((euclidean__axioms.nCol C F E) /\ ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F))))) as H129.
------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder F E C H128).
------------------------------------------------------------------------- destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
exact H136.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS E F C G) as H130.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H130.
-------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------- exists m.
split.
--------------------------------------------------------------------------- exact H123.
--------------------------------------------------------------------------- split.
---------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------- exact H129.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E C F E C) as H131.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H131.
--------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric F E C A E C H97).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E B F E C) as H132.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H132.
---------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETtransitive A E B F E C A E C H109 H131).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E B F C E) as H133.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET A E B E C F) /\ ((euclidean__axioms.ET A E B F C E) /\ ((euclidean__axioms.ET A E B E F C) /\ ((euclidean__axioms.ET A E B C E F) /\ (euclidean__axioms.ET A E B C F E))))) as H133.
----------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation A E B F E C H132).
----------------------------------------------------------------------------- destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
exact H136.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E C F E C) as H134.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H134.
------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------ exact H131.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F C G F C E) as H135.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H135.
------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------- exact H119.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.ET F C G F E C) as H136.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.ET F C G C E F) /\ ((euclidean__axioms.ET F C G F E C) /\ ((euclidean__axioms.ET F C G C F E) /\ ((euclidean__axioms.ET F C G E C F) /\ (euclidean__axioms.ET F C G E F C))))) as H136.
-------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETpermutation F C G F C E H135).
-------------------------------------------------------------------------------- destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
exact H139.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET F E C F C G) as H137.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H137.
--------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------- exact H117.
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A E C F C G) as H138.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H138.
---------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETtransitive A E C F C G F E C H134 H137).
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF A B E C F E C G) as H139.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H139.
----------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__paste3 A E B C E F C E G m H133 H138 H19).
------------------------------------------------------------------------------------right.
right.
exact H110.

------------------------------------------------------------------------------------ exact H123.
------------------------------------------------------------------------------------left.
exact H124.

---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F E C) as H140.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F E C) /\ ((euclidean__axioms.nCol F C G) /\ ((euclidean__axioms.nCol E C G) /\ (euclidean__axioms.nCol F E G)))) as H140.
------------------------------------------------------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC F E C G H127).
------------------------------------------------------------------------------------ destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
exact H128.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E F) as H141.
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol E C F) /\ ((euclidean__axioms.nCol C F E) /\ ((euclidean__axioms.nCol F C E) /\ (euclidean__axioms.nCol C E F))))) as H141.
------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder F E C H140).
------------------------------------------------------------------------------------- destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
exact H149.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C E F C E F) as H142.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H142.
-------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive C E F H141).
------------------------------------------------------------------------------------- assert ((E = f) \/ ((E = F) \/ ((f = F) \/ ((euclidean__axioms.BetS f E F) \/ ((euclidean__axioms.BetS E f F) \/ (euclidean__axioms.BetS E F f)))))) as H143 by exact H80.
assert (* Cut *) (euclidean__axioms.neq F E) as H144.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq C F) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F C)))))) as H144.
--------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct C E F H141).
--------------------------------------------------------------------------------------- destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
exact H153.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E F) as H145.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H145.
---------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric F E H144).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E F f) as H146.
---------------------------------------------------------------------------------------- assert ((E = f) \/ ((E = F) \/ ((f = F) \/ ((euclidean__axioms.BetS f E F) \/ ((euclidean__axioms.BetS E f F) \/ (euclidean__axioms.BetS E F f)))))) as H146 by exact H143.
assert ((E = f) \/ ((E = F) \/ ((f = F) \/ ((euclidean__axioms.BetS f E F) \/ ((euclidean__axioms.BetS E f F) \/ (euclidean__axioms.BetS E F f)))))) as __TmpHyp by exact H146.
destruct __TmpHyp as [H147|H147].
----------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out E F f))) as H148.
------------------------------------------------------------------------------------------ intro H148.
apply (@H73).
-------------------------------------------------------------------------------------------intro H149.
apply (@H76 H147).

------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Out E F f)).
-------------------------------------------------------------------------------------------intro H149.
destruct H0 as [H150 H151].
destruct H4 as [H152 H153].
destruct H6 as [H154 H155].
destruct H11 as [H156 H157].
destruct H21 as [H158 H159].
destruct H57 as [H160 H161].
destruct H58 as [H162 H163].
destruct H60 as [H164 H165].
destruct H66 as [H166 H167].
destruct H71 as [H168 H169].
destruct H94 as [H170 H171].
destruct H112 as [H172 H173].
destruct H128 as [H174 H175].
destruct H129 as [H176 H177].
destruct H140 as [H178 H179].
destruct H141 as [H180 H181].
destruct H151 as [H182 H183].
destruct H153 as [H184 H185].
destruct H155 as [H186 H187].
destruct H157 as [H188 H189].
destruct H159 as [H190 H191].
destruct H161 as [H192 H193].
destruct H163 as [H194 H195].
destruct H165 as [H196 H197].
destruct H167 as [H198 H199].
destruct H169 as [H200 H201].
destruct H171 as [H202 H203].
destruct H173 as [H204 H205].
destruct H175 as [H206 H207].
destruct H177 as [H208 H209].
destruct H179 as [H210 H211].
destruct H181 as [H212 H213].
destruct H183 as [H214 H215].
destruct H185 as [H216 H217].
destruct H187 as [H218 H219].
destruct H189 as [H220 H221].
destruct H191 as [H222 H223].
destruct H193 as [H224 H225].
destruct H195 as [H226 H227].
destruct H197 as [H228 H229].
destruct H199 as [H230 H231].
destruct H201 as [H232 H233].
destruct H203 as [H234 H235].
destruct H205 as [H236 H237].
destruct H207 as [H238 H239].
destruct H209 as [H240 H241].
destruct H211 as [H242 H243].
destruct H213 as [H244 H245].
destruct H215 as [H246 H247].
destruct H217 as [H248 H249].
destruct H219 as [H250 H251].
destruct H221 as [H252 H253].
destruct H223 as [H254 H255].
destruct H225 as [H256 H257].
destruct H227 as [H258 H259].
destruct H229 as [H260 H261].
destruct H231 as [H262 H263].
destruct H233 as [H264 H265].
destruct H235 as [H266 H267].
destruct H237 as [H268 H269].
destruct H239 as [H270 H271].
destruct H241 as [H272 H273].
destruct H243 as [H274 H275].
destruct H245 as [H276 H277].
destruct H247 as [H278 H279].
destruct H249 as [H280 H281].
destruct H251 as [H282 H283].
destruct H253 as [H284 H285].
destruct H255 as [H286 H287].
destruct H257 as [H288 H289].
destruct H259 as [H290 H291].
destruct H261 as [H292 H293].
destruct H263 as [H294 H295].
destruct H265 as [H296 H297].
destruct H267 as [H298 H299].
destruct H269 as [H300 H301].
destruct H271 as [H302 H303].
destruct H273 as [H304 H305].
destruct H275 as [H306 H307].
destruct H277 as [H308 H309].
assert (* Cut *) (False) as H310.
-------------------------------------------------------------------------------------------- apply (@H76 H147).
-------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H311.
--------------------------------------------------------------------------------------------- apply (@H148 H149).
--------------------------------------------------------------------------------------------- contradiction H311.

----------------------------------------------------------------------------------------- destruct H147 as [H148|H148].
------------------------------------------------------------------------------------------ assert (* Cut *) (~(~(euclidean__defs.Out E F f))) as H149.
------------------------------------------------------------------------------------------- intro H149.
apply (@H73).
--------------------------------------------------------------------------------------------intro H150.
apply (@H145 H148).

------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out E F f)).
--------------------------------------------------------------------------------------------intro H150.
destruct H0 as [H151 H152].
destruct H4 as [H153 H154].
destruct H6 as [H155 H156].
destruct H11 as [H157 H158].
destruct H21 as [H159 H160].
destruct H57 as [H161 H162].
destruct H58 as [H163 H164].
destruct H60 as [H165 H166].
destruct H66 as [H167 H168].
destruct H71 as [H169 H170].
destruct H94 as [H171 H172].
destruct H112 as [H173 H174].
destruct H128 as [H175 H176].
destruct H129 as [H177 H178].
destruct H140 as [H179 H180].
destruct H141 as [H181 H182].
destruct H152 as [H183 H184].
destruct H154 as [H185 H186].
destruct H156 as [H187 H188].
destruct H158 as [H189 H190].
destruct H160 as [H191 H192].
destruct H162 as [H193 H194].
destruct H164 as [H195 H196].
destruct H166 as [H197 H198].
destruct H168 as [H199 H200].
destruct H170 as [H201 H202].
destruct H172 as [H203 H204].
destruct H174 as [H205 H206].
destruct H176 as [H207 H208].
destruct H178 as [H209 H210].
destruct H180 as [H211 H212].
destruct H182 as [H213 H214].
destruct H184 as [H215 H216].
destruct H186 as [H217 H218].
destruct H188 as [H219 H220].
destruct H190 as [H221 H222].
destruct H192 as [H223 H224].
destruct H194 as [H225 H226].
destruct H196 as [H227 H228].
destruct H198 as [H229 H230].
destruct H200 as [H231 H232].
destruct H202 as [H233 H234].
destruct H204 as [H235 H236].
destruct H206 as [H237 H238].
destruct H208 as [H239 H240].
destruct H210 as [H241 H242].
destruct H212 as [H243 H244].
destruct H214 as [H245 H246].
destruct H216 as [H247 H248].
destruct H218 as [H249 H250].
destruct H220 as [H251 H252].
destruct H222 as [H253 H254].
destruct H224 as [H255 H256].
destruct H226 as [H257 H258].
destruct H228 as [H259 H260].
destruct H230 as [H261 H262].
destruct H232 as [H263 H264].
destruct H234 as [H265 H266].
destruct H236 as [H267 H268].
destruct H238 as [H269 H270].
destruct H240 as [H271 H272].
destruct H242 as [H273 H274].
destruct H244 as [H275 H276].
destruct H246 as [H277 H278].
destruct H248 as [H279 H280].
destruct H250 as [H281 H282].
destruct H252 as [H283 H284].
destruct H254 as [H285 H286].
destruct H256 as [H287 H288].
destruct H258 as [H289 H290].
destruct H260 as [H291 H292].
destruct H262 as [H293 H294].
destruct H264 as [H295 H296].
destruct H266 as [H297 H298].
destruct H268 as [H299 H300].
destruct H270 as [H301 H302].
destruct H272 as [H303 H304].
destruct H274 as [H305 H306].
destruct H276 as [H307 H308].
destruct H278 as [H309 H310].
assert (* Cut *) (False) as H311.
--------------------------------------------------------------------------------------------- apply (@H145 H148).
--------------------------------------------------------------------------------------------- assert (* Cut *) (False) as H312.
---------------------------------------------------------------------------------------------- apply (@H149 H150).
---------------------------------------------------------------------------------------------- contradiction H312.

------------------------------------------------------------------------------------------ destruct H148 as [H149|H149].
------------------------------------------------------------------------------------------- assert (* Cut *) (F = F) as H150.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H150.
--------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------------------- apply (@logic.eq__refl Point F).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E F F) as H151.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H151.
---------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 E F F).
-----------------------------------------------------------------------------------------------right.
left.
exact H150.

----------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E F f) as H152.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H152.
----------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point f (fun F0 => (euclidean__axioms.Col E f F0) -> ((euclidean__axioms.Col P Q F0) -> ((euclidean__defs.PG F0 G C E) -> ((euclidean__defs.PG G F0 E C) -> ((euclidean__defs.PG F0 E C G) -> ((euclidean__defs.Par F0 E C G) -> ((euclidean__axioms.nCol F0 E G) -> ((euclidean__axioms.neq F0 G) -> ((euclidean__axioms.Col F0 G A) -> ((euclidean__axioms.ET F0 E C A E C) -> ((euclidean__defs.PG E F0 G C) -> ((euclidean__axioms.Cong__3 F0 E C C G F0) -> ((euclidean__axioms.ET F0 E C C G F0) -> ((euclidean__axioms.ET F0 E C F0 C G) -> ((euclidean__axioms.ET F0 C G F0 E C) -> ((euclidean__axioms.ET F0 C G F0 C E) -> ((euclidean__axioms.ET F0 C E F0 C G) -> ((euclidean__axioms.BetS F0 m C) -> ((euclidean__axioms.Col F0 m C) -> ((euclidean__axioms.Col F0 C m) -> ((euclidean__defs.Par F0 E C G) -> ((euclidean__axioms.nCol F0 E C) -> ((euclidean__axioms.nCol F0 C E) -> ((euclidean__axioms.TS E F0 C G) -> ((euclidean__axioms.ET A E C F0 E C) -> ((euclidean__axioms.ET A E B F0 E C) -> ((euclidean__axioms.ET A E B F0 C E) -> ((euclidean__axioms.ET A E C F0 E C) -> ((euclidean__axioms.ET F0 C G F0 C E) -> ((euclidean__axioms.ET F0 C G F0 E C) -> ((euclidean__axioms.ET F0 E C F0 C G) -> ((euclidean__axioms.ET A E C F0 C G) -> ((euclidean__axioms.EF A B E C F0 E C G) -> ((euclidean__axioms.nCol F0 E C) -> ((euclidean__axioms.nCol C E F0) -> ((euclidean__defs.CongA C E F0 C E F0) -> ((euclidean__axioms.neq F0 E) -> ((euclidean__axioms.neq E F0) -> ((F0 = F0) -> ((euclidean__defs.Out E F0 F0) -> (euclidean__defs.Out E F0 f)))))))))))))))))))))))))))))))))))))))))) with (y := F).
------------------------------------------------------------------------------------------------intro H153.
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
assert (f = f) as H193 by exact H191.
exact H192.

------------------------------------------------------------------------------------------------ exact H149.
------------------------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------------------------ exact H81.
------------------------------------------------------------------------------------------------ exact H87.
------------------------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------------------------ exact H90.
------------------------------------------------------------------------------------------------ exact H93.
------------------------------------------------------------------------------------------------ exact H94.
------------------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------------------ exact H96.
------------------------------------------------------------------------------------------------ exact H97.
------------------------------------------------------------------------------------------------ exact H114.
------------------------------------------------------------------------------------------------ exact H115.
------------------------------------------------------------------------------------------------ exact H116.
------------------------------------------------------------------------------------------------ exact H117.
------------------------------------------------------------------------------------------------ exact H118.
------------------------------------------------------------------------------------------------ exact H119.
------------------------------------------------------------------------------------------------ exact H120.
------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------ exact H126.
------------------------------------------------------------------------------------------------ exact H127.
------------------------------------------------------------------------------------------------ exact H128.
------------------------------------------------------------------------------------------------ exact H129.
------------------------------------------------------------------------------------------------ exact H130.
------------------------------------------------------------------------------------------------ exact H131.
------------------------------------------------------------------------------------------------ exact H132.
------------------------------------------------------------------------------------------------ exact H133.
------------------------------------------------------------------------------------------------ exact H134.
------------------------------------------------------------------------------------------------ exact H135.
------------------------------------------------------------------------------------------------ exact H136.
------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------ exact H140.
------------------------------------------------------------------------------------------------ exact H141.
------------------------------------------------------------------------------------------------ exact H142.
------------------------------------------------------------------------------------------------ exact H144.
------------------------------------------------------------------------------------------------ exact H145.
------------------------------------------------------------------------------------------------ exact H150.
------------------------------------------------------------------------------------------------ exact H151.
---------------------------------------------------------------------------------------------- exact H152.
------------------------------------------------------------------------------------------- destruct H149 as [H150|H150].
-------------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out E F f))) as H151.
--------------------------------------------------------------------------------------------- intro H151.
assert (* Cut *) (E = E) as H152.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H152.
----------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E C E) as H153.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H153.
------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------ right.
left.
exact H152.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F E f) as H154.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H154.
------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry f E F H150).
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol E C F) as H155.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E C F) /\ ((euclidean__axioms.nCol E F C) /\ ((euclidean__axioms.nCol F C E) /\ ((euclidean__axioms.nCol C F E) /\ (euclidean__axioms.nCol F E C))))) as H155.
-------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder C E F H141).
-------------------------------------------------------------------------------------------------- destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
exact H156.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS F E C f) as H156.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H156.
--------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------------------------- exists E.
split.
---------------------------------------------------------------------------------------------------- exact H154.
---------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------- exact H153.
----------------------------------------------------------------------------------------------------- exact H155.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS f E C F) as H157.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H157.
---------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric E C F f H156).
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A f E C) as H158.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS A f E C) /\ ((euclidean__defs.OS f A C E) /\ (euclidean__defs.OS A f C E))) as H158.
----------------------------------------------------------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric E C f A H18).
----------------------------------------------------------------------------------------------------- destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
exact H59.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS A E C F) as H159.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H159.
------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------ apply (@lemma__planeseparation.lemma__planeseparation E C A f F H158 H157).
----------------------------------------------------------------------------------------------------- assert (exists j, (euclidean__axioms.BetS A j F) /\ ((euclidean__axioms.Col E C j) /\ (euclidean__axioms.nCol E C A))) as H160 by exact H159.
destruct H160 as [j H161].
destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
assert (* Cut *) (euclidean__axioms.Col A j F) as H166.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H166.
------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H162.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq P Q) as H167.
------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq j F) /\ ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F))) as H167.
-------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A j F H162).
-------------------------------------------------------------------------------------------------------- destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
exact H78.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q P) as H168.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H168.
--------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric P Q H167).
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q A F) as H169.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H169.
---------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col Q A F).
-----------------------------------------------------------------------------------------------------------intro H170.
apply (@euclidean__tactics.Col__nCol__False Q A F H170).
------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 P Q A F H92 H81 H167).


--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F Q) as H170.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A Q F) /\ ((euclidean__axioms.Col A F Q) /\ ((euclidean__axioms.Col F Q A) /\ ((euclidean__axioms.Col Q F A) /\ (euclidean__axioms.Col F A Q))))) as H170.
----------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder Q A F H169).
----------------------------------------------------------------------------------------------------------- destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
exact H173.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q P A) as H171.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col P A Q) /\ (euclidean__axioms.Col A Q P))))) as H171.
------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder P Q A H92).
------------------------------------------------------------------------------------------------------------ destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
exact H172.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col Q P F) as H172.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col Q P F) /\ ((euclidean__axioms.Col Q F P) /\ ((euclidean__axioms.Col F P Q) /\ ((euclidean__axioms.Col P F Q) /\ (euclidean__axioms.Col F Q P))))) as H172.
------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder P Q F H81).
------------------------------------------------------------------------------------------------------------- destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
exact H173.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P A F) as H173.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H173.
-------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col P A F).
---------------------------------------------------------------------------------------------------------------intro H174.
apply (@euclidean__tactics.Col__nCol__False P A F H174).
----------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 Q P A F H171 H172 H168).


------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F P) as H174.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A P F) /\ ((euclidean__axioms.Col A F P) /\ ((euclidean__axioms.Col F P A) /\ ((euclidean__axioms.Col P F A) /\ (euclidean__axioms.Col F A P))))) as H174.
--------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder P A F H173).
--------------------------------------------------------------------------------------------------------------- destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
exact H177.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F j) as H175.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col j A F) /\ ((euclidean__axioms.Col j F A) /\ ((euclidean__axioms.Col F A j) /\ ((euclidean__axioms.Col A F j) /\ (euclidean__axioms.Col F j A))))) as H175.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A j F H166).
---------------------------------------------------------------------------------------------------------------- destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
exact H182.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H176.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq j F) /\ ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F))) as H176.
----------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A j F H162).
----------------------------------------------------------------------------------------------------------------- destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
exact H167.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A F) as H177.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq j F) /\ ((euclidean__axioms.neq A j) /\ (euclidean__axioms.neq A F))) as H177.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A j F H162).
------------------------------------------------------------------------------------------------------------------ destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
exact H181.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P Q j) as H178.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H178.
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col P Q j).
--------------------------------------------------------------------------------------------------------------------intro H179.
apply (@euclidean__tactics.Col__nCol__False P Q j H179).
---------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 A F P Q j H177 H174 H170 H175).


------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet P Q E C) as H179.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H179.
-------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------------------------------------------------- exists j.
split.
--------------------------------------------------------------------------------------------------------------------- exact H176.
--------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------- exact H69.
---------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------- exact H178.
----------------------------------------------------------------------------------------------------------------------- exact H164.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet P Q E C)) as H180.
-------------------------------------------------------------------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H180 by exact H127.
assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H180.
destruct __TmpHyp0 as [x H181].
destruct H181 as [x0 H182].
destruct H182 as [x1 H183].
destruct H183 as [x2 H184].
destruct H184 as [x3 H185].
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
assert (exists U V u v X, (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H206 by exact H102.
assert (exists U V u v X, (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B E u) /\ ((euclidean__axioms.Col B E v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B E)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H206.
destruct __TmpHyp1 as [x4 H207].
destruct H207 as [x5 H208].
destruct H208 as [x6 H209].
destruct H209 as [x7 H210].
destruct H210 as [x8 H211].
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
assert (exists U V u v X, (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H232 by exact H101.
assert (exists U V u v X, (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E B u) /\ ((euclidean__axioms.Col E B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H232.
destruct __TmpHyp2 as [x9 H233].
destruct H233 as [x10 H234].
destruct H234 as [x11 H235].
destruct H235 as [x12 H236].
destruct H236 as [x13 H237].
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
assert (exists U V u v X, (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H258 by exact H98.
assert (exists U V u v X, (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C B u) /\ ((euclidean__axioms.Col C B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q C B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp3 by exact H258.
destruct __TmpHyp3 as [x14 H259].
destruct H259 as [x15 H260].
destruct H260 as [x16 H261].
destruct H261 as [x17 H262].
destruct H262 as [x18 H263].
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
assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H284 by exact H93.
assert (exists U V u v X, (euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq C G) /\ ((euclidean__axioms.Col F E U) /\ ((euclidean__axioms.Col F E V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C G u) /\ ((euclidean__axioms.Col C G v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet F E C G)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp4 by exact H284.
destruct __TmpHyp4 as [x19 H285].
destruct H285 as [x20 H286].
destruct H286 as [x21 H287].
destruct H287 as [x22 H288].
destruct H288 as [x23 H289].
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
assert (exists U V u v X, (euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col P Q u) /\ ((euclidean__axioms.Col P Q v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H310 by exact H84.
assert (exists U V u v X, (euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq P Q) /\ ((euclidean__axioms.Col E C U) /\ ((euclidean__axioms.Col E C V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col P Q u) /\ ((euclidean__axioms.Col P Q v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E C P Q)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp5 by exact H310.
destruct __TmpHyp5 as [x24 H311].
destruct H311 as [x25 H312].
destruct H312 as [x26 H313].
destruct H313 as [x27 H314].
destruct H314 as [x28 H315].
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
assert (exists U V u v X, (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H336 by exact H83.
assert (exists U V u v X, (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col E C u) /\ ((euclidean__axioms.Col E C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q E C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp6 by exact H336.
destruct __TmpHyp6 as [x29 H337].
destruct H337 as [x30 H338].
destruct H338 as [x31 H339].
destruct H339 as [x32 H340].
destruct H340 as [x33 H341].
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
assert (exists U V u v X, (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H362 by exact H40.
assert (exists U V u v X, (euclidean__axioms.neq P Q) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col P Q U) /\ ((euclidean__axioms.Col P Q V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet P Q B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp7 by exact H362.
destruct __TmpHyp7 as [x34 H363].
destruct H363 as [x35 H364].
destruct H364 as [x36 H365].
destruct H365 as [x37 H366].
destruct H366 as [x38 H367].
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
exact H358.
-------------------------------------------------------------------------------------------------------------------- apply (@H73).
---------------------------------------------------------------------------------------------------------------------intro H181.
apply (@H180 H179).

--------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out E F f)).
----------------------------------------------------------------------------------------------intro H152.
destruct H0 as [H153 H154].
destruct H4 as [H155 H156].
destruct H6 as [H157 H158].
destruct H11 as [H159 H160].
destruct H21 as [H161 H162].
destruct H57 as [H163 H164].
destruct H58 as [H165 H166].
destruct H60 as [H167 H168].
destruct H66 as [H169 H170].
destruct H71 as [H171 H172].
destruct H94 as [H173 H174].
destruct H112 as [H175 H176].
destruct H128 as [H177 H178].
destruct H129 as [H179 H180].
destruct H140 as [H181 H182].
destruct H141 as [H183 H184].
destruct H154 as [H185 H186].
destruct H156 as [H187 H188].
destruct H158 as [H189 H190].
destruct H160 as [H191 H192].
destruct H162 as [H193 H194].
destruct H164 as [H195 H196].
destruct H166 as [H197 H198].
destruct H168 as [H199 H200].
destruct H170 as [H201 H202].
destruct H172 as [H203 H204].
destruct H174 as [H205 H206].
destruct H176 as [H207 H208].
destruct H178 as [H209 H210].
destruct H180 as [H211 H212].
destruct H182 as [H213 H214].
destruct H184 as [H215 H216].
destruct H186 as [H217 H218].
destruct H188 as [H219 H220].
destruct H190 as [H221 H222].
destruct H192 as [H223 H224].
destruct H194 as [H225 H226].
destruct H196 as [H227 H228].
destruct H198 as [H229 H230].
destruct H200 as [H231 H232].
destruct H202 as [H233 H234].
destruct H204 as [H235 H236].
destruct H206 as [H237 H238].
destruct H208 as [H239 H240].
destruct H210 as [H241 H242].
destruct H212 as [H243 H244].
destruct H214 as [H245 H246].
destruct H216 as [H247 H248].
destruct H218 as [H249 H250].
destruct H220 as [H251 H252].
destruct H222 as [H253 H254].
destruct H224 as [H255 H256].
destruct H226 as [H257 H258].
destruct H228 as [H259 H260].
destruct H230 as [H261 H262].
destruct H232 as [H263 H264].
destruct H234 as [H265 H266].
destruct H236 as [H267 H268].
destruct H238 as [H269 H270].
destruct H240 as [H271 H272].
destruct H242 as [H273 H274].
destruct H244 as [H275 H276].
destruct H246 as [H277 H278].
destruct H248 as [H279 H280].
destruct H250 as [H281 H282].
destruct H252 as [H283 H284].
destruct H254 as [H285 H286].
destruct H256 as [H287 H288].
destruct H258 as [H289 H290].
destruct H260 as [H291 H292].
destruct H262 as [H293 H294].
destruct H264 as [H295 H296].
destruct H266 as [H297 H298].
destruct H268 as [H299 H300].
destruct H270 as [H301 H302].
destruct H272 as [H303 H304].
destruct H274 as [H305 H306].
destruct H276 as [H307 H308].
destruct H278 as [H309 H310].
destruct H280 as [H311 H312].
assert (* Cut *) (False) as H313.
----------------------------------------------------------------------------------------------- apply (@H151 H152).
----------------------------------------------------------------------------------------------- contradiction H313.

-------------------------------------------------------------------------------------------- destruct H150 as [H151|H151].
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E F f) as H152.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H152.
----------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 E F f).
------------------------------------------------------------------------------------------------left.
exact H151.

------------------------------------------------------------------------------------------------ exact H145.
---------------------------------------------------------------------------------------------- exact H152.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out E F f) as H152.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H152.
----------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
----------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 E F f).
------------------------------------------------------------------------------------------------right.
right.
exact H151.

------------------------------------------------------------------------------------------------ exact H145.
---------------------------------------------------------------------------------------------- exact H152.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E F c E f) as H147.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H147.
------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper C E F C E F c f H142 H15 H146).
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F E C f E c) as H148.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Meet E f P Q) as H148.
------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
------------------------------------------------------------------------------------------- apply (@lemma__equalanglesflip.lemma__equalanglesflip C E F c E f H147).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA F E C J D K) as H149.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H149.
-------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
-------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive F E C f E c J D K H148 H17).
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E F F E C) as H150.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H150.
--------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
--------------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA C E F H141).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C E F J D K) as H151.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E f P Q) as H151.
---------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Meet E f P Q) H73).
---------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive C E F F E C J D K H150 H149).
--------------------------------------------------------------------------------------------- exists F.
exists G.
split.
---------------------------------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------- exact H139.
----------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------ exact H151.
------------------------------------------------------------------------------------------------ exact H96.
Qed.
