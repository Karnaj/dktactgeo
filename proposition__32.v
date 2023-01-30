Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__5b.
Require Export lemma__3__6a.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelflip.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__29.
Require Export proposition__31short.
Definition proposition__32 : forall A B C D, (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.BetS B C D) -> (euclidean__defs.SumA C A B A B C A C D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (euclidean__axioms.nCol A B C) as H1 by exact H.
assert (* Cut *) (euclidean__axioms.neq B A) as H2.
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H2.
-- apply (@lemma__NCdistinct.lemma__NCdistinct A B C H1).
-- destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H9.
- assert (* Cut *) (euclidean__axioms.neq A B) as H3.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B A H2).
-- assert (* Cut *) (exists F, (euclidean__axioms.BetS B A F) /\ (euclidean__axioms.Cong A F B A)) as H4.
--- apply (@lemma__extension.lemma__extension B A B A H2 H2).
--- destruct H4 as [F H5].
destruct H5 as [H6 H7].
assert (* Cut *) (euclidean__axioms.Col B A F) as H8.
---- right.
right.
right.
right.
left.
exact H6.
---- assert (* Cut *) (euclidean__axioms.Col A B F) as H9.
----- assert (* Cut *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))))) as H9.
------ apply (@lemma__collinearorder.lemma__collinearorder B A F H8).
------ destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H10.
----- assert (* Cut *) (B = B) as H10.
------ apply (@logic.eq__refl Point B).
------ assert (* Cut *) (euclidean__axioms.Col A B B) as H11.
------- right.
right.
left.
exact H10.
------- assert (* Cut *) (euclidean__axioms.neq B F) as H12.
-------- assert (* Cut *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B F))) as H12.
--------- apply (@lemma__betweennotequal.lemma__betweennotequal B A F H6).
--------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H16.
-------- assert (* Cut *) (euclidean__axioms.neq F B) as H13.
--------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B F H12).
--------- assert (* Cut *) (euclidean__axioms.nCol F B C) as H14.
---------- apply (@euclidean__tactics.nCol__notCol F B C).
-----------apply (@euclidean__tactics.nCol__not__Col F B C).
------------apply (@lemma__NChelper.lemma__NChelper A B C F B H1 H9 H11 H13).


---------- assert (* Cut *) (euclidean__axioms.BetS F A B) as H15.
----------- apply (@euclidean__axioms.axiom__betweennesssymmetry B A F H6).
----------- assert (* Cut *) (exists E H16 S, (euclidean__axioms.BetS E C H16) /\ ((euclidean__defs.CongA E C A C A B) /\ ((euclidean__defs.Par E H16 F B) /\ ((euclidean__axioms.BetS E S B) /\ (euclidean__axioms.BetS C S A))))) as H16.
------------ apply (@proposition__31short.proposition__31short C F B A H15 H14).
------------ destruct H16 as [E H17].
destruct H17 as [H18 H19].
destruct H19 as [S H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
assert (* Cut *) (euclidean__axioms.neq B C) as H29.
------------- assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D))) as H29.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal B C D H0).
-------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H32.
------------- assert (* Cut *) (euclidean__axioms.neq C B) as H30.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B C H29).
-------------- assert (* Cut *) (exists G, (euclidean__axioms.BetS C B G) /\ (euclidean__axioms.Cong B G C B)) as H31.
--------------- apply (@lemma__extension.lemma__extension C B C B H30 H30).
--------------- destruct H31 as [G H32].
destruct H32 as [H33 H34].
assert (* Cut *) (euclidean__axioms.neq C A) as H35.
---------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H35.
----------------- apply (@lemma__NCdistinct.lemma__NCdistinct A B C H1).
----------------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H45.
---------------- assert (* Cut *) (exists J, (euclidean__axioms.BetS C A J) /\ (euclidean__axioms.Cong A J C A)) as H36.
----------------- apply (@lemma__extension.lemma__extension C A C A H35 H35).
----------------- destruct H36 as [J H37].
destruct H37 as [H38 H39].
assert (* Cut *) (euclidean__axioms.neq A C) as H40.
------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C A H35).
------------------ assert (* Cut *) (exists K, (euclidean__axioms.BetS A C K) /\ (euclidean__axioms.Cong C K A C)) as H41.
------------------- apply (@lemma__extension.lemma__extension A C A C H40 H40).
------------------- destruct H41 as [K H42].
destruct H42 as [H43 H44].
assert (* Cut *) (exists M, (euclidean__axioms.BetS A B M) /\ (euclidean__axioms.Cong B M A B)) as H45.
-------------------- apply (@lemma__extension.lemma__extension A B A B H3 H3).
-------------------- destruct H45 as [M H46].
destruct H46 as [H47 H48].
assert (* Cut *) (euclidean__axioms.Col F B A) as H49.
--------------------- assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H49.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder A B F H9).
---------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H57.
--------------------- assert (* Cut *) (euclidean__defs.Par E H18 A B) as H50.
---------------------- apply (@lemma__collinearparallel.lemma__collinearparallel E H18 A F B H25 H49 H3).
---------------------- assert (* Cut *) (euclidean__axioms.BetS K C A) as H51.
----------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A C K H43).
----------------------- assert (* Cut *) (euclidean__axioms.Col C S A) as H52.
------------------------ right.
right.
right.
right.
left.
exact H28.
------------------------ assert (* Cut *) (euclidean__axioms.Col C A S) as H53.
------------------------- assert (* Cut *) ((euclidean__axioms.Col S C A) /\ ((euclidean__axioms.Col S A C) /\ ((euclidean__axioms.Col A C S) /\ ((euclidean__axioms.Col C A S) /\ (euclidean__axioms.Col A S C))))) as H53.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder C S A H52).
-------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H60.
------------------------- assert (* Cut *) (euclidean__axioms.nCol A C B) as H54.
-------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H54.
--------------------------- apply (@lemma__NCorder.lemma__NCorder A B C H1).
--------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H61.
-------------------------- assert (* Cut *) (euclidean__axioms.Col A C S) as H55.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col A C S) /\ ((euclidean__axioms.Col A S C) /\ ((euclidean__axioms.Col S C A) /\ ((euclidean__axioms.Col C S A) /\ (euclidean__axioms.Col S A C))))) as H55.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder C A S H53).
---------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H56.
--------------------------- assert (* Cut *) (euclidean__axioms.neq C S) as H56.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq S A) /\ ((euclidean__axioms.neq C S) /\ (euclidean__axioms.neq C A))) as H56.
----------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C S A H28).
----------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H59.
---------------------------- assert (* Cut *) (euclidean__axioms.neq S C) as H57.
----------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C S H56).
----------------------------- assert (* Cut *) (C = C) as H58.
------------------------------ apply (@logic.eq__refl Point C).
------------------------------ assert (* Cut *) (euclidean__axioms.Col A C C) as H59.
------------------------------- right.
right.
left.
exact H58.
------------------------------- assert (* Cut *) (euclidean__axioms.nCol S C B) as H60.
-------------------------------- apply (@euclidean__tactics.nCol__notCol S C B).
---------------------------------apply (@euclidean__tactics.nCol__not__Col S C B).
----------------------------------apply (@lemma__NChelper.lemma__NChelper A C B S C H54 H55 H59 H57).


-------------------------------- assert (* Cut *) (euclidean__axioms.nCol B S C) as H61.
--------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C S B) /\ ((euclidean__axioms.nCol C B S) /\ ((euclidean__axioms.nCol B S C) /\ ((euclidean__axioms.nCol S B C) /\ (euclidean__axioms.nCol B C S))))) as H61.
---------------------------------- apply (@lemma__NCorder.lemma__NCorder S C B H60).
---------------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H66.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col E S B) as H62.
---------------------------------- right.
right.
right.
right.
left.
exact H27.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col B S E) as H63.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col S E B) /\ ((euclidean__axioms.Col S B E) /\ ((euclidean__axioms.Col B E S) /\ ((euclidean__axioms.Col E B S) /\ (euclidean__axioms.Col B S E))))) as H63.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder E S B H62).
------------------------------------ destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H71.
----------------------------------- assert (B = B) as H64 by exact H10.
assert (* Cut *) (euclidean__axioms.Col B S B) as H65.
------------------------------------ right.
left.
exact H64.
------------------------------------ assert (* Cut *) (euclidean__axioms.BetS B S E) as H66.
------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E S B H27).
------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H67.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.neq S E) /\ ((euclidean__axioms.neq B S) /\ (euclidean__axioms.neq B E))) as H67.
--------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B S E H66).
--------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H71.
-------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E C) as H68.
--------------------------------------- apply (@euclidean__tactics.nCol__notCol B E C).
----------------------------------------apply (@euclidean__tactics.nCol__not__Col B E C).
-----------------------------------------apply (@lemma__NChelper.lemma__NChelper B S C B E H61 H65 H63 H67).


--------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E S) as H69.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col S B E) /\ ((euclidean__axioms.Col S E B) /\ ((euclidean__axioms.Col E B S) /\ ((euclidean__axioms.Col B E S) /\ (euclidean__axioms.Col E S B))))) as H69.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B S E H63).
----------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H76.
---------------------------------------- assert (* Cut *) (E = E) as H70.
----------------------------------------- apply (@logic.eq__refl Point E).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E E) as H71.
------------------------------------------ right.
right.
left.
exact H70.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq S E) as H72.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq S E) /\ ((euclidean__axioms.neq B S) /\ (euclidean__axioms.neq B E))) as H72.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B S E H66).
-------------------------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H73.
------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol S E C) as H73.
-------------------------------------------- apply (@euclidean__tactics.nCol__notCol S E C).
---------------------------------------------apply (@euclidean__tactics.nCol__not__Col S E C).
----------------------------------------------apply (@lemma__NChelper.lemma__NChelper B E C S E H68 H69 H71 H72).


-------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol S C E) as H74.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E S C) /\ ((euclidean__axioms.nCol E C S) /\ ((euclidean__axioms.nCol C S E) /\ ((euclidean__axioms.nCol S C E) /\ (euclidean__axioms.nCol C E S))))) as H74.
---------------------------------------------- apply (@lemma__NCorder.lemma__NCorder S E C H73).
---------------------------------------------- destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H81.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col S C C) as H75.
---------------------------------------------- right.
right.
left.
exact H58.
---------------------------------------------- assert (euclidean__axioms.Col C S A) as H76 by exact H52.
assert (* Cut *) (euclidean__axioms.Col S C A) as H77.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col S C A) /\ ((euclidean__axioms.Col S A C) /\ ((euclidean__axioms.Col A C S) /\ ((euclidean__axioms.Col C A S) /\ (euclidean__axioms.Col A S C))))) as H77.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder C S A H76).
------------------------------------------------ destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H78.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C A) as H78.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq S E) /\ ((euclidean__axioms.neq B S) /\ (euclidean__axioms.neq B E))) as H78.
------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B S E H66).
------------------------------------------------- destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H35.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol C A E) as H79.
------------------------------------------------- apply (@euclidean__tactics.nCol__notCol C A E).
--------------------------------------------------apply (@euclidean__tactics.nCol__not__Col C A E).
---------------------------------------------------apply (@lemma__NChelper.lemma__NChelper S C E C A H74 H75 H77 H78).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B M) as H80.
-------------------------------------------------- right.
right.
right.
right.
left.
exact H47.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A M) as H81.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A M) /\ ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A M B) /\ (euclidean__axioms.Col M B A))))) as H81.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B M H80).
---------------------------------------------------- destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H82.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H18 B A) as H82.
---------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par H18 E A B) /\ ((euclidean__defs.Par E H18 B A) /\ (euclidean__defs.Par H18 E B A))) as H82.
----------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip E H18 A B H50).
----------------------------------------------------- destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
exact H85.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A M) as H83.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B M) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A M))) as H83.
------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A B M H47).
------------------------------------------------------ destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
exact H87.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M A) as H84.
------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A M H83).
------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par E H18 M A) as H85.
------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel E H18 M B A H82 H81 H84).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS H18 C E) as H86.
-------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E C H18 H21).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS M B A) as H87.
--------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A B M H47).
--------------------------------------------------------- assert (euclidean__axioms.BetS F A B) as H88 by exact H15.
assert (* Cut *) (euclidean__axioms.BetS D C B) as H89.
---------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B C D H0).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C A) as H90.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H90.
------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder A C B H54).
------------------------------------------------------------ destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
exact H98.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A C B) as H91.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H91.
------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder B C A H90).
------------------------------------------------------------- destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
exact H99.
------------------------------------------------------------ assert (* Cut *) (A = A) as H92.
------------------------------------------------------------- apply (@logic.eq__refl Point A).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H93.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D B))) as H93.
--------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D C B H89).
--------------------------------------------------------------- destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
exact H67.
-------------------------------------------------------------- assert (euclidean__axioms.BetS E C H18) as H94 by exact H21.
assert (* Cut *) (euclidean__axioms.BetS A S C) as H95.
--------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C S A H28).
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E A) as H96.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol C E A) /\ (euclidean__axioms.nCol E A C))))) as H96.
----------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder C A E H79).
----------------------------------------------------------------- destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
exact H103.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C E H18) as H97.
----------------------------------------------------------------- right.
right.
right.
left.
exact H94.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C E E) as H98.
------------------------------------------------------------------ right.
right.
left.
exact H70.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq E H18) as H99.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C H18) /\ ((euclidean__axioms.neq E C) /\ (euclidean__axioms.neq E H18))) as H99.
-------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E C H18 H94).
-------------------------------------------------------------------- destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
exact H103.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H18 E) as H100.
-------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E H18 H99).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H18 E A) as H101.
--------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol H18 E A).
----------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col H18 E A).
-----------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper C E A H18 E H96 H97 H98 H100).


--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E H18 A) as H102.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E H18 A) /\ ((euclidean__axioms.nCol E A H18) /\ ((euclidean__axioms.nCol A H18 E) /\ ((euclidean__axioms.nCol H18 A E) /\ (euclidean__axioms.nCol A E H18))))) as H102.
----------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder H18 E A H101).
----------------------------------------------------------------------- destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
exact H103.
---------------------------------------------------------------------- assert (* Cut *) (exists Q, (euclidean__axioms.BetS A Q H18) /\ (euclidean__axioms.BetS E S Q)) as H103.
----------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__outer A E C S H18 H95 H94 H102).
----------------------------------------------------------------------- destruct H103 as [Q H104].
destruct H104 as [H105 H106].
assert (* Cut *) (euclidean__axioms.Col E S Q) as H107.
------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H106.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col S E B) as H108.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E B S) /\ ((euclidean__axioms.Col E S B) /\ ((euclidean__axioms.Col S B E) /\ ((euclidean__axioms.Col B S E) /\ (euclidean__axioms.Col S E B))))) as H108.
-------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B E S H69).
-------------------------------------------------------------------------- destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
exact H116.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col S E Q) as H109.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col S E Q) /\ ((euclidean__axioms.Col S Q E) /\ ((euclidean__axioms.Col Q E S) /\ ((euclidean__axioms.Col E Q S) /\ (euclidean__axioms.Col Q S E))))) as H109.
--------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E S Q H107).
--------------------------------------------------------------------------- destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
exact H110.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B Q) as H110.
--------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E B Q).
----------------------------------------------------------------------------intro H110.
apply (@euclidean__tactics.Col__nCol__False E B Q H110).
-----------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 S E B Q H108 H109 H72).


--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E Q) as H111.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B E Q) /\ ((euclidean__axioms.Col B Q E) /\ ((euclidean__axioms.Col Q E B) /\ ((euclidean__axioms.Col E Q B) /\ (euclidean__axioms.Col Q B E))))) as H111.
----------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E B Q H110).
----------------------------------------------------------------------------- destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
exact H112.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H18 E) as H112.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq S Q) /\ ((euclidean__axioms.neq E S) /\ (euclidean__axioms.neq E Q))) as H112.
------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal E S Q H106).
------------------------------------------------------------------------------ destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
exact H100.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H113.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq H18 C) /\ (euclidean__axioms.neq H18 E))) as H113.
------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H18 C E H86).
------------------------------------------------------------------------------- destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
exact H114.
------------------------------------------------------------------------------ assert (* Cut *) (exists L, (euclidean__axioms.BetS H18 E L) /\ (euclidean__axioms.Cong E L C E)) as H114.
------------------------------------------------------------------------------- apply (@lemma__extension.lemma__extension H18 E C E H112 H113).
------------------------------------------------------------------------------- destruct H114 as [L H115].
destruct H115 as [H116 H117].
assert (* Cut *) (euclidean__axioms.BetS L E H18) as H118.
-------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry H18 E L H116).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L E H18) as H119.
--------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H118.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L H18) as H120.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq L E) /\ (euclidean__axioms.neq L H18))) as H120.
----------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal L E H18 H118).
----------------------------------------------------------------------------------- destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
exact H124.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E H18) as H121.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq L E) /\ (euclidean__axioms.neq L H18))) as H121.
------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal L E H18 H118).
------------------------------------------------------------------------------------ destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
exact H122.
----------------------------------------------------------------------------------- assert (euclidean__axioms.Col A B M) as H122 by exact H80.
assert (* Cut *) (euclidean__axioms.neq A M) as H123.
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq L E) /\ (euclidean__axioms.neq L H18))) as H123.
------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal L E H18 H118).
------------------------------------------------------------------------------------- destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H83.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A B) as H124.
------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq L E) /\ (euclidean__axioms.neq L H18))) as H124.
-------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal L E H18 H118).
-------------------------------------------------------------------------------------- destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
exact H3.
------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A M L H18)) as H125.
-------------------------------------------------------------------------------------- intro H125.
assert (exists c, (euclidean__axioms.neq A M) /\ ((euclidean__axioms.neq L H18) /\ ((euclidean__axioms.Col A M c) /\ (euclidean__axioms.Col L H18 c)))) as H126 by exact H125.
destruct H126 as [c H127].
destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
assert (* Cut *) (euclidean__axioms.Col H18 E L) as H134.
--------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H116.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L H18 E) as H135.
---------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E H18 L) /\ ((euclidean__axioms.Col E L H18) /\ ((euclidean__axioms.Col L H18 E) /\ ((euclidean__axioms.Col H18 L E) /\ (euclidean__axioms.Col L E H18))))) as H135.
----------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H18 E L H134).
----------------------------------------------------------------------------------------- destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
exact H140.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H18 L) as H136.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E L) /\ ((euclidean__axioms.neq H18 E) /\ (euclidean__axioms.neq H18 L))) as H136.
------------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal H18 E L H116).
------------------------------------------------------------------------------------------ destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
exact H140.
----------------------------------------------------------------------------------------- assert (euclidean__axioms.neq L H18) as H137 by exact H130.
assert (* Cut *) (euclidean__axioms.Col H18 c E) as H138.
------------------------------------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col H18 c E).
-------------------------------------------------------------------------------------------intro H138.
apply (@euclidean__tactics.Col__nCol__False H18 c E H138).
--------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 L H18 c E H133 H135 H137).


------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E H18 c) as H139.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col c H18 E) /\ ((euclidean__axioms.Col c E H18) /\ ((euclidean__axioms.Col E H18 c) /\ ((euclidean__axioms.Col H18 E c) /\ (euclidean__axioms.Col E c H18))))) as H139.
-------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H18 c E H138).
-------------------------------------------------------------------------------------------- destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
exact H144.
------------------------------------------------------------------------------------------- assert (euclidean__axioms.Col A B M) as H140 by exact H122.
assert (* Cut *) (euclidean__axioms.Col M A B) as H141.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A M) /\ ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A M B) /\ (euclidean__axioms.Col M B A))))) as H141.
--------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B M H140).
--------------------------------------------------------------------------------------------- destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
exact H146.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M A c) as H142.
--------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M A c) /\ ((euclidean__axioms.Col M c A) /\ ((euclidean__axioms.Col c A M) /\ ((euclidean__axioms.Col A c M) /\ (euclidean__axioms.Col c M A))))) as H142.
---------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A M c H132).
---------------------------------------------------------------------------------------------- destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
exact H143.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A M) as H143.
---------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq L E) /\ (euclidean__axioms.neq L H18))) as H143.
----------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal L E H18 H118).
----------------------------------------------------------------------------------------------- destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
exact H128.
---------------------------------------------------------------------------------------------- assert (euclidean__axioms.neq M A) as H144 by exact H84.
assert (* Cut *) (euclidean__axioms.Col A B c) as H145.
----------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col A B c).
------------------------------------------------------------------------------------------------intro H145.
apply (@euclidean__tactics.Col__nCol__False A B c H145).
-------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 M A B c H141 H142 H144).


----------------------------------------------------------------------------------------------- assert (euclidean__axioms.Col B A F) as H146 by exact H8.
assert (* Cut *) (euclidean__axioms.Col A B F) as H147.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))))) as H147.
------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A F H146).
------------------------------------------------------------------------------------------------- destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
exact H148.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B c F) as H148.
------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col B c F).
--------------------------------------------------------------------------------------------------intro H148.
apply (@euclidean__tactics.Col__nCol__False B c F H148).
---------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 A B c F H145 H147 H124).


------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F B c) as H149.
-------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col c B F) /\ ((euclidean__axioms.Col c F B) /\ ((euclidean__axioms.Col F B c) /\ ((euclidean__axioms.Col B F c) /\ (euclidean__axioms.Col F c B))))) as H149.
--------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B c F H148).
--------------------------------------------------------------------------------------------------- destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
exact H154.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Meet E H18 F B) as H150.
--------------------------------------------------------------------------------------------------- exists c.
split.
---------------------------------------------------------------------------------------------------- exact H121.
---------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------- exact H13.
----------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------------ exact H149.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet E H18 F B)) as H151.
---------------------------------------------------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.Col E H18 U) /\ ((euclidean__axioms.Col E H18 V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M A u) /\ ((euclidean__axioms.Col M A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E H18 M A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H151 by exact H85.
assert (exists U V u v X, (euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.Col E H18 U) /\ ((euclidean__axioms.Col E H18 V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col M A u) /\ ((euclidean__axioms.Col M A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E H18 M A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H151.
destruct __TmpHyp as [x H152].
destruct H152 as [x0 H153].
destruct H153 as [x1 H154].
destruct H154 as [x2 H155].
destruct H155 as [x3 H156].
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
assert (exists U V u v X, (euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col E H18 U) /\ ((euclidean__axioms.Col E H18 V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E H18 B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H177 by exact H82.
assert (exists U V u v X, (euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.Col E H18 U) /\ ((euclidean__axioms.Col E H18 V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B A u) /\ ((euclidean__axioms.Col B A v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E H18 B A)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H177.
destruct __TmpHyp0 as [x4 H178].
destruct H178 as [x5 H179].
destruct H179 as [x6 H180].
destruct H180 as [x7 H181].
destruct H181 as [x8 H182].
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
assert (exists U V u v X, (euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col E H18 U) /\ ((euclidean__axioms.Col E H18 V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E H18 A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H203 by exact H50.
assert (exists U V u v X, (euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col E H18 U) /\ ((euclidean__axioms.Col E H18 V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col A B u) /\ ((euclidean__axioms.Col A B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E H18 A B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp1 by exact H203.
destruct __TmpHyp1 as [x9 H204].
destruct H204 as [x10 H205].
destruct H205 as [x11 H206].
destruct H206 as [x12 H207].
destruct H207 as [x13 H208].
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
assert (exists U V u v X, (euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col E H18 U) /\ ((euclidean__axioms.Col E H18 V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E H18 F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H229 by exact H25.
assert (exists U V u v X, (euclidean__axioms.neq E H18) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.Col E H18 U) /\ ((euclidean__axioms.Col E H18 V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col F B u) /\ ((euclidean__axioms.Col F B v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet E H18 F B)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp2 by exact H229.
destruct __TmpHyp2 as [x14 H230].
destruct H230 as [x15 H231].
destruct H231 as [x16 H232].
destruct H232 as [x17 H233].
destruct H233 as [x18 H234].
destruct H234 as [H235 H236].
destruct H236 as [H237 H238].
destruct H238 as [H239 H240].
destruct H240 as [H241 H242].
destruct H242 as [H243 H244].
destruct H244 as [H245 H246].
destruct H246 as [H247 H248].
destruct H248 as [H249 H250].
destruct H250 as [H251 H252].
destruct H252 as [H253 H254].
exact H251.
---------------------------------------------------------------------------------------------------- apply (@H151 H150).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B Q E) as H126.
--------------------------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween A M L H18 B E Q H122 H119 H123 H120 H124 H121 H125 H105 H111).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A H18 E) as H127.
---------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H18 E A) /\ ((euclidean__axioms.nCol H18 A E) /\ ((euclidean__axioms.nCol A E H18) /\ ((euclidean__axioms.nCol E A H18) /\ (euclidean__axioms.nCol A H18 E))))) as H127.
----------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder E H18 A H102).
----------------------------------------------------------------------------------------- destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
exact H135.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A Q H18) as H128.
----------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H105.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H18 Q) as H129.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col Q A H18) /\ ((euclidean__axioms.Col Q H18 A) /\ ((euclidean__axioms.Col H18 A Q) /\ ((euclidean__axioms.Col A H18 Q) /\ (euclidean__axioms.Col H18 Q A))))) as H129.
------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A Q H18 H128).
------------------------------------------------------------------------------------------- destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
exact H136.
------------------------------------------------------------------------------------------ assert (* Cut *) (H18 = H18) as H130.
------------------------------------------------------------------------------------------- apply (@logic.eq__refl Point H18).
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H18 H18) as H131.
-------------------------------------------------------------------------------------------- right.
right.
left.
exact H130.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq Q H18) as H132.
--------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq Q H18) /\ ((euclidean__axioms.neq A Q) /\ (euclidean__axioms.neq A H18))) as H132.
---------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A Q H18 H105).
---------------------------------------------------------------------------------------------- destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
exact H133.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol Q H18 E) as H133.
---------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol Q H18 E).
-----------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col Q H18 E).
------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper A H18 E Q H18 H127 H129 H131 H132).


---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol Q E H18) as H134.
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H18 Q E) /\ ((euclidean__axioms.nCol H18 E Q) /\ ((euclidean__axioms.nCol E Q H18) /\ ((euclidean__axioms.nCol Q E H18) /\ (euclidean__axioms.nCol E H18 Q))))) as H134.
------------------------------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder Q H18 E H133).
------------------------------------------------------------------------------------------------ destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
exact H141.
----------------------------------------------------------------------------------------------- assert (E = E) as H135 by exact H70.
assert (* Cut *) (euclidean__axioms.Col Q E E) as H136.
------------------------------------------------------------------------------------------------ right.
right.
left.
exact H135.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col Q E B) as H137.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E B Q) /\ ((euclidean__axioms.Col E Q B) /\ ((euclidean__axioms.Col Q B E) /\ ((euclidean__axioms.Col B Q E) /\ (euclidean__axioms.Col Q E B))))) as H137.
-------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B E Q H111).
-------------------------------------------------------------------------------------------------- destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
exact H145.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E H18) as H138.
-------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol B E H18).
---------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col B E H18).
----------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper Q E H18 B E H134 H137 H136 H93).


-------------------------------------------------------------------------------------------------- assert (* Cut *) (exists T, (euclidean__axioms.BetS B T C) /\ (euclidean__axioms.BetS H18 T Q)) as H139.
--------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner B H18 E Q C H126 H86 H138).
--------------------------------------------------------------------------------------------------- destruct H139 as [T H140].
destruct H140 as [H141 H142].
assert (* Cut *) (euclidean__axioms.BetS Q T H18) as H143.
---------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry H18 T Q H142).
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A T H18) as H144.
----------------------------------------------------------------------------------------------------- apply (@lemma__3__5b.lemma__3__5b A Q T H18 H105 H143).
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B T C) as H145.
------------------------------------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H141.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C B T) as H146.
------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col T B C) /\ ((euclidean__axioms.Col T C B) /\ ((euclidean__axioms.Col C B T) /\ ((euclidean__axioms.Col B C T) /\ (euclidean__axioms.Col C T B))))) as H146.
-------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B T C H145).
-------------------------------------------------------------------------------------------------------- destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
exact H151.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C B A) as H147.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol B C A))))) as H147.
--------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder A C B H91).
--------------------------------------------------------------------------------------------------------- destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
exact H150.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS A C B H18) as H148.
--------------------------------------------------------------------------------------------------------- exists T.
split.
---------------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------- exact H146.
----------------------------------------------------------------------------------------------------------- exact H147.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS H18 C B A) as H149.
---------------------------------------------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric C B A H18 H148).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H18 E M A) as H150.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par H18 E M A) /\ ((euclidean__defs.Par E H18 A M) /\ (euclidean__defs.Par H18 E A M))) as H150.
------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip E H18 M A H85).
------------------------------------------------------------------------------------------------------------ destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
exact H151.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A C E B A C) as H151.
------------------------------------------------------------------------------------------------------------ apply (@lemma__equalanglesflip.lemma__equalanglesflip E C A C A B H23).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CongA H18 C B C B A) /\ ((euclidean__defs.CongA D C E C B A) /\ (euclidean__defs.RT E C B C B A))) as H152.
------------------------------------------------------------------------------------------------------------- apply (@proposition__29.proposition__29 H18 E M A D C B H150 H86 H87 H89 H149).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C B A A B C) as H153.
-------------------------------------------------------------------------------------------------------------- destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA C B A H147).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D C E A B C) as H154.
--------------------------------------------------------------------------------------------------------------- destruct H152 as [H154 H155].
destruct H155 as [H156 H157].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive D C E C B A A B C H156 H153).
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS T C D) as H155.
---------------------------------------------------------------------------------------------------------------- destruct H152 as [H155 H156].
destruct H156 as [H157 H158].
apply (@lemma__3__6a.lemma__3__6a B T C D H141 H0).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq T D) as H156.
----------------------------------------------------------------------------------------------------------------- destruct H152 as [H156 H157].
destruct H157 as [H158 H159].
assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq T C) /\ (euclidean__axioms.neq T D))) as H160.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal T C D H155).
------------------------------------------------------------------------------------------------------------------ destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
exact H164.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C A) as H157.
------------------------------------------------------------------------------------------------------------------ destruct H152 as [H157 H158].
destruct H158 as [H159 H160].
assert (* Cut *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol A C B) /\ ((euclidean__axioms.nCol C A B) /\ (euclidean__axioms.nCol A B C))))) as H161.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder C B A H147).
------------------------------------------------------------------------------------------------------------------- destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
exact H162.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B C T) as H158.
------------------------------------------------------------------------------------------------------------------- destruct H152 as [H158 H159].
destruct H159 as [H160 H161].
assert (* Cut *) ((euclidean__axioms.Col B C T) /\ ((euclidean__axioms.Col B T C) /\ ((euclidean__axioms.Col T C B) /\ ((euclidean__axioms.Col C T B) /\ (euclidean__axioms.Col T B C))))) as H162.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C B T H146).
-------------------------------------------------------------------------------------------------------------------- destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
exact H163.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H159.
-------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H0.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol T D A) as H160.
--------------------------------------------------------------------------------------------------------------------- destruct H152 as [H160 H161].
destruct H161 as [H162 H163].
apply (@euclidean__tactics.nCol__notCol T D A).
----------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col T D A).
-----------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper B C A T D H157 H158 H159 H156).


--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A T D) as H161.
---------------------------------------------------------------------------------------------------------------------- destruct H152 as [H161 H162].
destruct H162 as [H163 H164].
assert (* Cut *) ((euclidean__axioms.nCol D T A) /\ ((euclidean__axioms.nCol D A T) /\ ((euclidean__axioms.nCol A T D) /\ ((euclidean__axioms.nCol T A D) /\ (euclidean__axioms.nCol A D T))))) as H165.
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder T D A H160).
----------------------------------------------------------------------------------------------------------------------- destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
exact H170.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A T A) as H162.
----------------------------------------------------------------------------------------------------------------------- right.
left.
exact H92.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A T H18) as H163.
------------------------------------------------------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H144.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq A H18) as H164.
------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H164 H165].
destruct H165 as [H166 H167].
assert (* Cut *) ((euclidean__axioms.neq T H18) /\ ((euclidean__axioms.neq A T) /\ (euclidean__axioms.neq A H18))) as H168.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A T H18 H144).
-------------------------------------------------------------------------------------------------------------------------- destruct H168 as [H169 H170].
destruct H170 as [H171 H172].
exact H172.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A H18 D) as H165.
-------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H165 H166].
destruct H166 as [H167 H168].
apply (@euclidean__tactics.nCol__notCol A H18 D).
---------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col A H18 D).
----------------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper A T D A H18 H161 H162 H163 H164).


-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H18 A D) as H166.
--------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H166 H167].
destruct H167 as [H168 H169].
assert (* Cut *) ((euclidean__axioms.nCol H18 A D) /\ ((euclidean__axioms.nCol H18 D A) /\ ((euclidean__axioms.nCol D A H18) /\ ((euclidean__axioms.nCol A D H18) /\ (euclidean__axioms.nCol D H18 A))))) as H170.
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder A H18 D H165).
---------------------------------------------------------------------------------------------------------------------------- destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
exact H171.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS H18 T A) as H167.
---------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H167 H168].
destruct H168 as [H169 H170].
apply (@euclidean__axioms.axiom__betweennesssymmetry A T H18 H144).
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D C T) as H168.
----------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H168 H169].
destruct H169 as [H170 H171].
apply (@euclidean__axioms.axiom__betweennesssymmetry T C D H155).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists R, (euclidean__axioms.BetS D R A) /\ (euclidean__axioms.BetS H18 C R)) as H169.
------------------------------------------------------------------------------------------------------------------------------ destruct H152 as [H169 H170].
destruct H170 as [H171 H172].
apply (@euclidean__axioms.postulate__Pasch__outer D H18 T C A H168 H167 H166).
------------------------------------------------------------------------------------------------------------------------------ destruct H169 as [R H170].
destruct H170 as [H171 H172].
destruct H152 as [H173 H174].
destruct H174 as [H175 H176].
assert (* Cut *) (euclidean__defs.Out C E R) as H177.
------------------------------------------------------------------------------------------------------------------------------- exists H18.
split.
-------------------------------------------------------------------------------------------------------------------------------- exact H172.
-------------------------------------------------------------------------------------------------------------------------------- exact H86.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C A A) as H178.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 C A A).
---------------------------------------------------------------------------------------------------------------------------------right.
left.
exact H92.

--------------------------------------------------------------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H179.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq T C) /\ (euclidean__axioms.neq T D))) as H179.
---------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal T C D H155).
---------------------------------------------------------------------------------------------------------------------------------- destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
exact H180.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (D = D) as H180.
---------------------------------------------------------------------------------------------------------------------------------- apply (@logic.eq__refl Point D).
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A R D) as H181.
----------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry D R A H171).
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B A C A C E) as H182.
------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A C E B A C H151).
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA B A C A C R) as H183.
------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper B A C A C E A R H182 H178 H177).
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C A B) as H184.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H184.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder B C A H157).
--------------------------------------------------------------------------------------------------------------------------------------- destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
exact H187.
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C A B B A C) as H185.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA C A B H184).
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C A B A C R) as H186.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive C A B B A C A C R H185 H183).
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C D D) as H187.
----------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 C D D).
------------------------------------------------------------------------------------------------------------------------------------------right.
left.
exact H180.

------------------------------------------------------------------------------------------------------------------------------------------ exact H179.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C D C E) as H188.
------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric D C E A B C H154).
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B C D C R) as H189.
------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper A B C D C E D R H188 H187 H177).
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A D H18) as H190.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A H18 D) /\ ((euclidean__axioms.nCol A D H18) /\ ((euclidean__axioms.nCol D H18 A) /\ ((euclidean__axioms.nCol H18 D A) /\ (euclidean__axioms.nCol D A H18))))) as H190.
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder H18 A D H166).
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
exact H193.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D R A) as H191.
--------------------------------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H171.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A D R) as H192.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col R D A) /\ ((euclidean__axioms.Col R A D) /\ ((euclidean__axioms.Col A D R) /\ ((euclidean__axioms.Col D A R) /\ (euclidean__axioms.Col A R D))))) as H192.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D R A H191).
----------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
destruct H196 as [H197 H198].
destruct H198 as [H199 H200].
exact H197.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (D = D) as H193 by exact H180.
assert (* Cut *) (euclidean__axioms.Col A D D) as H194.
----------------------------------------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H193.
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D R) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq R A) /\ ((euclidean__axioms.neq D R) /\ (euclidean__axioms.neq D A))) as H195.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D R A H171).
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
exact H198.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq R D) as H196.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D R H195).
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol R D H18) as H197.
-------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol R D H18).
---------------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col R D H18).
----------------------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper A D H18 R D H190 H192 H194 H196).


-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol R H18 D) as H198.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D R H18) /\ ((euclidean__axioms.nCol D H18 R) /\ ((euclidean__axioms.nCol H18 R D) /\ ((euclidean__axioms.nCol R H18 D) /\ (euclidean__axioms.nCol H18 D R))))) as H198.
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder R D H18 H197).
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [H199 H200].
destruct H200 as [H201 H202].
destruct H202 as [H203 H204].
destruct H204 as [H205 H206].
exact H205.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H18 C R) as H199.
---------------------------------------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H172.
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col R H18 C) as H200.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C H18 R) /\ ((euclidean__axioms.Col C R H18) /\ ((euclidean__axioms.Col R H18 C) /\ ((euclidean__axioms.Col H18 R C) /\ (euclidean__axioms.Col R C H18))))) as H200.
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder H18 C R H199).
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H200 as [H201 H202].
destruct H202 as [H203 H204].
destruct H204 as [H205 H206].
destruct H206 as [H207 H208].
exact H205.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (R = R) as H201.
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@logic.eq__refl Point R).
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col R H18 R) as H202.
------------------------------------------------------------------------------------------------------------------------------------------------------- right.
left.
exact H201.
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C R) as H203.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C R) /\ ((euclidean__axioms.neq H18 C) /\ (euclidean__axioms.neq H18 R))) as H203.
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H18 C R H172).
--------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H203 as [H204 H205].
destruct H205 as [H206 H207].
exact H204.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq R C) as H204.
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C R H203).
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol R C D) as H205.
---------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol R C D).
-----------------------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col R C D).
------------------------------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper R H18 D R C H198 H202 H200 H204).


---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D C R) as H206.
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C R D) /\ ((euclidean__axioms.nCol C D R) /\ ((euclidean__axioms.nCol D R C) /\ ((euclidean__axioms.nCol R D C) /\ (euclidean__axioms.nCol D C R))))) as H206.
------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder R C D H205).
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H206 as [H207 H208].
destruct H208 as [H209 H210].
destruct H210 as [H211 H212].
destruct H212 as [H213 H214].
exact H214.
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D C R R C D) as H207.
------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA D C R H206).
------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B C R C D) as H208.
------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B C D C R R C D H189 H207).
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.SumA C A B A B C A C D) as H209.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exists R.
split.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H186.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H208.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H181.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H209.
Qed.
