Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennesspreserved.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelflip.
Require Export lemma__pointreflectionisometry.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__10.
Require Export proposition__27.
Definition proposition__31 : forall A B C D, (euclidean__axioms.BetS B D C) -> ((euclidean__axioms.nCol B C A) -> (exists X Y Z, (euclidean__axioms.BetS X A Y) /\ ((euclidean__defs.CongA Y A D A D B) /\ ((euclidean__defs.CongA Y A D B D A) /\ ((euclidean__defs.CongA D A Y B D A) /\ ((euclidean__defs.CongA X A D A D C) /\ ((euclidean__defs.CongA X A D C D A) /\ ((euclidean__defs.CongA D A X C D A) /\ ((euclidean__defs.Par X Y B C) /\ ((euclidean__axioms.Cong X A D C) /\ ((euclidean__axioms.Cong A Y B D) /\ ((euclidean__axioms.Cong A Z Z D) /\ ((euclidean__axioms.Cong X Z Z C) /\ ((euclidean__axioms.Cong B Z Z Y) /\ ((euclidean__axioms.BetS X Z C) /\ ((euclidean__axioms.BetS B Z Y) /\ (euclidean__axioms.BetS A Z D))))))))))))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.Col B D C) as H1.
- right.
right.
right.
right.
left.
exact H.
- assert (* Cut *) (~(A = D)) as H2.
-- intro H2.
assert (* Cut *) (euclidean__axioms.Col B A C) as H3.
--- apply (@eq__ind__r euclidean__axioms.Point D (fun A0 => (euclidean__axioms.nCol B C A0) -> (euclidean__axioms.Col B A0 C))) with (x := A).
----intro H3.
exact H1.

---- exact H2.
---- exact H0.
--- assert (* Cut *) (euclidean__axioms.Col B C A) as H4.
---- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H4.
----- apply (@lemma__collinearorder.lemma__collinearorder B A C H3).
----- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H11.
---- apply (@euclidean__tactics.Col__nCol__False B C A H0 H4).
-- assert (* Cut *) (exists M, (euclidean__axioms.BetS A M D) /\ (euclidean__axioms.Cong M A M D)) as H3.
--- apply (@proposition__10.proposition__10 A D H2).
--- destruct H3 as [M H4].
destruct H4 as [H5 H6].
assert (* Cut *) (euclidean__axioms.Cong A M M D) as H7.
---- assert (* Cut *) ((euclidean__axioms.Cong A M D M) /\ ((euclidean__axioms.Cong A M M D) /\ (euclidean__axioms.Cong M A D M))) as H7.
----- apply (@lemma__congruenceflip.lemma__congruenceflip M A M D H6).
----- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H10.
---- assert (* Cut *) (euclidean__axioms.Col C B D) as H8.
----- assert (* Cut *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B))))) as H8.
------ apply (@lemma__collinearorder.lemma__collinearorder B D C H1).
------ destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H13.
----- assert (* Cut *) (B = B) as H9.
------ apply (@logic.eq__refl Point B).
------ assert (* Cut *) (euclidean__axioms.Col C B B) as H10.
------- right.
right.
left.
exact H9.
------- assert (* Cut *) (euclidean__axioms.nCol C B A) as H11.
-------- assert (* Cut *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H11.
--------- apply (@lemma__NCorder.lemma__NCorder B C A H0).
--------- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H12.
-------- assert (* Cut *) (euclidean__axioms.neq B D) as H12.
--------- assert (* Cut *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B C))) as H12.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal B D C H).
---------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H15.
--------- assert (* Cut *) (euclidean__axioms.nCol B D A) as H13.
---------- apply (@euclidean__tactics.nCol__notCol B D A).
-----------apply (@euclidean__tactics.nCol__not__Col B D A).
------------apply (@lemma__NChelper.lemma__NChelper C B A B D H11 H10 H8 H12).


---------- assert (euclidean__axioms.Col B D C) as H14 by exact H1.
assert (* Cut *) (D = D) as H15.
----------- apply (@logic.eq__refl Point D).
----------- assert (* Cut *) (euclidean__axioms.Col B D D) as H16.
------------ right.
right.
left.
exact H15.
------------ assert (* Cut *) (euclidean__axioms.neq D C) as H17.
------------- assert (* Cut *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B D) /\ (euclidean__axioms.neq B C))) as H17.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal B D C H).
-------------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H18.
------------- assert (* Cut *) (euclidean__axioms.neq C D) as H18.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D C H17).
-------------- assert (* Cut *) (euclidean__axioms.nCol C D A) as H19.
--------------- apply (@euclidean__tactics.nCol__notCol C D A).
----------------apply (@euclidean__tactics.nCol__not__Col C D A).
-----------------apply (@lemma__NChelper.lemma__NChelper B D A C D H13 H14 H16 H18).


--------------- assert (* Cut *) (euclidean__axioms.nCol A D C) as H20.
---------------- assert (* Cut *) ((euclidean__axioms.nCol D C A) /\ ((euclidean__axioms.nCol D A C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol C A D) /\ (euclidean__axioms.nCol A D C))))) as H20.
----------------- apply (@lemma__NCorder.lemma__NCorder C D A H19).
----------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H28.
---------------- assert (* Cut *) (euclidean__axioms.Col A M D) as H21.
----------------- right.
right.
right.
right.
left.
exact H5.
----------------- assert (* Cut *) (euclidean__axioms.Col A D M) as H22.
------------------ assert (* Cut *) ((euclidean__axioms.Col M A D) /\ ((euclidean__axioms.Col M D A) /\ ((euclidean__axioms.Col D A M) /\ ((euclidean__axioms.Col A D M) /\ (euclidean__axioms.Col D M A))))) as H22.
------------------- apply (@lemma__collinearorder.lemma__collinearorder A M D H21).
------------------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H29.
------------------ assert (* Cut *) (A = A) as H23.
------------------- apply (@logic.eq__refl Point A).
------------------- assert (* Cut *) (euclidean__axioms.Col A D A) as H24.
-------------------- right.
left.
exact H23.
-------------------- assert (* Cut *) (euclidean__axioms.neq A M) as H25.
--------------------- assert (* Cut *) ((euclidean__axioms.neq M D) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A D))) as H25.
---------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A M D H5).
---------------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H28.
--------------------- assert (* Cut *) (euclidean__axioms.nCol A M C) as H26.
---------------------- apply (@euclidean__tactics.nCol__notCol A M C).
-----------------------apply (@euclidean__tactics.nCol__not__Col A M C).
------------------------apply (@lemma__NChelper.lemma__NChelper A D C A M H20 H24 H22 H25).


---------------------- assert (* Cut *) (~(C = M)) as H27.
----------------------- intro H27.
assert (* Cut *) (euclidean__axioms.Col A C M) as H28.
------------------------ right.
right.
left.
exact H27.
------------------------ assert (* Cut *) (euclidean__axioms.Col A M C) as H29.
------------------------- assert (* Cut *) ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col C M A) /\ ((euclidean__axioms.Col M A C) /\ ((euclidean__axioms.Col A M C) /\ (euclidean__axioms.Col M C A))))) as H29.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder A C M H28).
-------------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H36.
------------------------- apply (@euclidean__tactics.Col__nCol__False A M C H26 H29).
----------------------- assert (* Cut *) (euclidean__axioms.neq M C) as H28.
------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C M H27).
------------------------ assert (* Cut *) (exists E, (euclidean__axioms.BetS C M E) /\ (euclidean__axioms.Cong M E M C)) as H29.
------------------------- apply (@lemma__extension.lemma__extension C M M C H27 H28).
------------------------- destruct H29 as [E H30].
destruct H30 as [H31 H32].
assert (* Cut *) (euclidean__axioms.Cong M C M E) as H33.
-------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric M M E C H32).
-------------------------- assert (* Cut *) (euclidean__axioms.Cong C M M E) as H34.
--------------------------- assert (* Cut *) ((euclidean__axioms.Cong C M E M) /\ ((euclidean__axioms.Cong C M M E) /\ (euclidean__axioms.Cong M C E M))) as H34.
---------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip M C M E H33).
---------------------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H37.
--------------------------- assert (* Cut *) (euclidean__defs.Midpoint C M E) as H35.
---------------------------- split.
----------------------------- exact H31.
----------------------------- exact H34.
---------------------------- assert (* Cut *) (euclidean__axioms.neq A M) as H36.
----------------------------- assert (* Cut *) ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C E))) as H36.
------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal C M E H31).
------------------------------ destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H25.
----------------------------- assert (* Cut *) (euclidean__axioms.nCol A D B) as H37.
------------------------------ assert (* Cut *) ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol B A D) /\ (euclidean__axioms.nCol A D B))))) as H37.
------------------------------- apply (@lemma__NCorder.lemma__NCorder B D A H13).
------------------------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H45.
------------------------------ assert (* Cut *) (euclidean__axioms.nCol A M B) as H38.
------------------------------- apply (@euclidean__tactics.nCol__notCol A M B).
--------------------------------apply (@euclidean__tactics.nCol__not__Col A M B).
---------------------------------apply (@lemma__NChelper.lemma__NChelper A D B A M H37 H24 H22 H36).


------------------------------- assert (* Cut *) (~(B = M)) as H39.
-------------------------------- intro H39.
assert (* Cut *) (euclidean__axioms.Col A B M) as H40.
--------------------------------- right.
right.
left.
exact H39.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col A M B) as H41.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A M) /\ ((euclidean__axioms.Col B M A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A M B) /\ (euclidean__axioms.Col M B A))))) as H41.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B M H40).
----------------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H48.
---------------------------------- apply (@euclidean__tactics.Col__nCol__False A M B H38 H41).
-------------------------------- assert (* Cut *) (euclidean__axioms.neq M B) as H40.
--------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B M H39).
--------------------------------- assert (* Cut *) (exists F, (euclidean__axioms.BetS B M F) /\ (euclidean__axioms.Cong M F M B)) as H41.
---------------------------------- apply (@lemma__extension.lemma__extension B M M B H39 H40).
---------------------------------- destruct H41 as [F H42].
destruct H42 as [H43 H44].
assert (* Cut *) (euclidean__axioms.Cong M F B M) as H45.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Cong F M B M) /\ ((euclidean__axioms.Cong F M M B) /\ (euclidean__axioms.Cong M F B M))) as H45.
------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip M F M B H44).
------------------------------------ destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H49.
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong B M M F) as H46.
------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B M F M H45).
------------------------------------ assert (* Cut *) (euclidean__defs.Midpoint B M F) as H47.
------------------------------------- split.
-------------------------------------- exact H43.
-------------------------------------- exact H46.
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M D M A) as H48.
-------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric M M A D H6).
-------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D M A) as H49.
--------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A M D H5).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D M M A) as H50.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong D M A M) /\ ((euclidean__axioms.Cong D M M A) /\ (euclidean__axioms.Cong M D A M))) as H50.
----------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip M D M A H48).
----------------------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H53.
---------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint D M A) as H51.
----------------------------------------- split.
------------------------------------------ exact H49.
------------------------------------------ exact H50.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H52.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq D M) /\ (euclidean__axioms.neq D A))) as H52.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D M A H49).
------------------------------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H12.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq D C) as H53.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq D M) /\ (euclidean__axioms.neq D A))) as H53.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D M A H49).
-------------------------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H17.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H54.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A C)))))) as H54.
--------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct C B A H11).
--------------------------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H61.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D F A) as H55.
--------------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry B M F D A H47 H51 H52).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D C A E) as H56.
---------------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry D M A C E H51 H35 H53).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C F E) as H57.
----------------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry B M F C E H47 H35 H54).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F A E) as H58.
------------------------------------------------ apply (@lemma__betweennesspreserved.lemma__betweennesspreserved B D C F A E H55 H57 H56 H).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS E A F) as H59.
------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry F A E H58).
------------------------------------------------- assert (* Cut *) (F = F) as H60.
-------------------------------------------------- apply (@logic.eq__refl Point F).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A F) as H61.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E F))) as H61.
---------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E A F H59).
---------------------------------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H62.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A F F) as H62.
---------------------------------------------------- apply (@lemma__ray4.lemma__ray4 A F F).
-----------------------------------------------------right.
left.
exact H60.

----------------------------------------------------- exact H61.
---------------------------------------------------- assert (B = B) as H63 by exact H9.
assert (* Cut *) (euclidean__axioms.neq B D) as H64.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E F))) as H64.
------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal E A F H59).
------------------------------------------------------ destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H52.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H65.
------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B D H64).
------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out D B B) as H66.
------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 D B B).
--------------------------------------------------------right.
left.
exact H63.

-------------------------------------------------------- exact H65.
------------------------------------------------------- assert (A = A) as H67 by exact H23.
assert (* Cut *) (euclidean__axioms.neq D A) as H68.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq D M) /\ (euclidean__axioms.neq D A))) as H68.
--------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D M A H49).
--------------------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H72.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out D A A) as H69.
--------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 D A A).
----------------------------------------------------------right.
left.
exact H67.

---------------------------------------------------------- exact H68.
--------------------------------------------------------- assert (D = D) as H70 by exact H15.
assert (euclidean__axioms.neq A D) as H71 by exact H2.
assert (* Cut *) (euclidean__defs.Out A D D) as H72.
---------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 A D D).
-----------------------------------------------------------right.
left.
exact H70.

----------------------------------------------------------- exact H71.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B M A) as H73.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol M A B) /\ ((euclidean__axioms.nCol M B A) /\ ((euclidean__axioms.nCol B A M) /\ ((euclidean__axioms.nCol A B M) /\ (euclidean__axioms.nCol B M A))))) as H73.
------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder A M B H38).
------------------------------------------------------------ destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
exact H81.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B M F) as H74.
------------------------------------------------------------ right.
right.
right.
right.
left.
exact H43.
------------------------------------------------------------ assert (* Cut *) (M = M) as H75.
------------------------------------------------------------- apply (@logic.eq__refl Point M).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B M M) as H76.
-------------------------------------------------------------- right.
right.
left.
exact H75.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M F) as H77.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M F) /\ ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B F))) as H77.
---------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B M F H43).
---------------------------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
exact H78.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F M) as H78.
---------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric M F H77).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F M A) as H79.
----------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol F M A).
------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col F M A).
-------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper B M A F M H73 H74 H76 H78).


----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A M F) as H80.
------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol M F A) /\ ((euclidean__axioms.nCol M A F) /\ ((euclidean__axioms.nCol A F M) /\ ((euclidean__axioms.nCol F A M) /\ (euclidean__axioms.nCol A M F))))) as H80.
------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder F M A H79).
------------------------------------------------------------------- destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H88.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A M A) as H81.
------------------------------------------------------------------- right.
left.
exact H67.
------------------------------------------------------------------- assert (euclidean__axioms.Col A M D) as H82 by exact H21.
assert (* Cut *) (euclidean__axioms.nCol A D F) as H83.
-------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol A D F).
---------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col A D F).
----------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper A M F A D H80 H81 H82 H71).


-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F A D) as H84.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D A F) /\ ((euclidean__axioms.nCol D F A) /\ ((euclidean__axioms.nCol F A D) /\ ((euclidean__axioms.nCol A F D) /\ (euclidean__axioms.nCol F D A))))) as H84.
---------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder A D F H83).
---------------------------------------------------------------------- destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
exact H89.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D B A F) as H85.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong D B A F) /\ ((euclidean__axioms.Cong D B F A) /\ (euclidean__axioms.Cong B D A F))) as H85.
----------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip B D F A H55).
----------------------------------------------------------------------- destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H86.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint A M D) as H86.
----------------------------------------------------------------------- split.
------------------------------------------------------------------------ exact H5.
------------------------------------------------------------------------ exact H7.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H87.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq B M) /\ ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A B)))))) as H87.
------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct B M A H73).
------------------------------------------------------------------------- destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
exact H92.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong B A F D) as H88.
------------------------------------------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry B M F A D H47 H86 H87).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F D B A) as H89.
-------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric F B A D H88).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A F D B) as H90.
--------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A D B F H85).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D D A) as H91.
---------------------------------------------------------------------------- apply (@euclidean__axioms.cn__equalityreverse A D).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A D B D A) as H92.
----------------------------------------------------------------------------- exists F.
exists D.
exists B.
exists A.
split.
------------------------------------------------------------------------------ exact H62.
------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------- exact H72.
------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------- exact H66.
-------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------- exact H69.
--------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------- exact H91.
----------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------ exact H89.
------------------------------------------------------------------------------------ exact H84.
----------------------------------------------------------------------------- assert (euclidean__axioms.nCol B D A) as H93 by exact H13.
assert (* Cut *) (euclidean__defs.CongA B D A A D B) as H94.
------------------------------------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B D A H93).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA F A D A D B) as H95.
------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive F A D B D A A D B H92 H94).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A D B F A D) as H96.
-------------------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric F A D A D B H95).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D A B) as H97.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol B A D) /\ (euclidean__axioms.nCol A D B))))) as H97.
---------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder B D A H93).
---------------------------------------------------------------------------------- destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H100.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F A D) as H98.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D B A) /\ (euclidean__axioms.nCol B A D))))) as H98.
----------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder D A B H97).
----------------------------------------------------------------------------------- destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
exact H84.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F A D D A F) as H99.
----------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA F A D H98).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A D B D A F) as H100.
------------------------------------------------------------------------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A D B F A D D A F H96 H99).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA D A F A D B) as H101.
------------------------------------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A D B D A F H100).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A D B) as H102.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A F D) /\ ((euclidean__axioms.nCol A D F) /\ ((euclidean__axioms.nCol D F A) /\ ((euclidean__axioms.nCol F D A) /\ (euclidean__axioms.nCol D A F))))) as H102.
--------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder F A D H98).
--------------------------------------------------------------------------------------- destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
exact H37.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A D B B D A) as H103.
--------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A D B H102).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D A F B D A) as H104.
---------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive D A F A D B B D A H101 H103).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS B A D F) as H105.
----------------------------------------------------------------------------------------- exists M.
split.
------------------------------------------------------------------------------------------ exact H43.
------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------- exact H22.
------------------------------------------------------------------------------------------- exact H102.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS F A D B) as H106.
------------------------------------------------------------------------------------------ apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric A D B F H105).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS C D B) as H107.
------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B D C H).
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F E C B) as H108.
-------------------------------------------------------------------------------------------- apply (@proposition__27.proposition__27 F E C B A D H58 H107 H95 H106).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E F B C) as H109.
--------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par E F C B) /\ ((euclidean__defs.Par F E B C) /\ (euclidean__defs.Par E F B C))) as H109.
---------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip F E C B H108).
---------------------------------------------------------------------------------------------- destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
exact H113.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D C E A) as H110.
---------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C D E A) /\ ((euclidean__axioms.Cong C D A E) /\ (euclidean__axioms.Cong D C E A))) as H110.
----------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip D C A E H56).
----------------------------------------------------------------------------------------------- destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
exact H114.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E A D C) as H111.
----------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric E D C A H110).
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B D A F) as H112.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong B D F A) /\ ((euclidean__axioms.Cong B D A F) /\ (euclidean__axioms.Cong D B F A))) as H112.
------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip D B A F H85).
------------------------------------------------------------------------------------------------- destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
exact H115.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A F B D) as H113.
------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A B D F H112).
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong M C E M) as H114.
-------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M C E M) /\ ((euclidean__axioms.Cong M C M E) /\ (euclidean__axioms.Cong C M E M))) as H114.
--------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip C M M E H34).
--------------------------------------------------------------------------------------------------- destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
exact H115.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E M M C) as H115.
--------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric E M C M H114).
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E A) as H116.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E F))) as H116.
----------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E A F H59).
----------------------------------------------------------------------------------------------------- destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
exact H119.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H117.
----------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E A H116).
----------------------------------------------------------------------------------------------------- assert (* Cut *) (E = E) as H118.
------------------------------------------------------------------------------------------------------ apply (@logic.eq__refl Point E).
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out A E E) as H119.
------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 A E E).
--------------------------------------------------------------------------------------------------------right.
left.
exact H118.

-------------------------------------------------------------------------------------------------------- exact H117.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H120.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C B))) as H120.
--------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C D B H107).
--------------------------------------------------------------------------------------------------------- destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
exact H53.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (C = C) as H121.
--------------------------------------------------------------------------------------------------------- apply (@logic.eq__refl Point C).
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out D C C) as H122.
---------------------------------------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 D C C).
-----------------------------------------------------------------------------------------------------------right.
left.
exact H121.

----------------------------------------------------------------------------------------------------------- exact H120.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong E M M C) as H123.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong C M M E) /\ ((euclidean__axioms.Cong C M E M) /\ (euclidean__axioms.Cong M C M E))) as H123.
------------------------------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip M C E M H114).
------------------------------------------------------------------------------------------------------------ destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H115.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E M C) as H124.
------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry C M E H31).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Midpoint E M C) as H125.
------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------- exact H124.
-------------------------------------------------------------------------------------------------------------- exact H123.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(E = D)) as H126.
-------------------------------------------------------------------------------------------------------------- intro H126.
assert (* Cut *) (euclidean__axioms.BetS C M D) as H127.
--------------------------------------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point D (fun E0 => (euclidean__axioms.BetS C M E0) -> ((euclidean__axioms.Cong M E0 M C) -> ((euclidean__axioms.Cong M C M E0) -> ((euclidean__axioms.Cong C M M E0) -> ((euclidean__defs.Midpoint C M E0) -> ((euclidean__axioms.Cong D C A E0) -> ((euclidean__axioms.Cong B C F E0) -> ((euclidean__axioms.BetS F A E0) -> ((euclidean__axioms.BetS E0 A F) -> ((euclidean__defs.Par F E0 C B) -> ((euclidean__defs.Par E0 F B C) -> ((euclidean__axioms.Cong D C E0 A) -> ((euclidean__axioms.Cong E0 A D C) -> ((euclidean__axioms.Cong M C E0 M) -> ((euclidean__axioms.Cong E0 M M C) -> ((euclidean__axioms.neq E0 A) -> ((euclidean__axioms.neq A E0) -> ((E0 = E0) -> ((euclidean__defs.Out A E0 E0) -> ((euclidean__axioms.Cong E0 M M C) -> ((euclidean__axioms.BetS E0 M C) -> ((euclidean__defs.Midpoint E0 M C) -> (euclidean__axioms.BetS C M D)))))))))))))))))))))))) with (x := E).
----------------------------------------------------------------------------------------------------------------intro H127.
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
exact H127.

---------------------------------------------------------------------------------------------------------------- exact H126.
---------------------------------------------------------------------------------------------------------------- exact H31.
---------------------------------------------------------------------------------------------------------------- exact H32.
---------------------------------------------------------------------------------------------------------------- exact H33.
---------------------------------------------------------------------------------------------------------------- exact H34.
---------------------------------------------------------------------------------------------------------------- exact H35.
---------------------------------------------------------------------------------------------------------------- exact H56.
---------------------------------------------------------------------------------------------------------------- exact H57.
---------------------------------------------------------------------------------------------------------------- exact H58.
---------------------------------------------------------------------------------------------------------------- exact H59.
---------------------------------------------------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------------------------------------------------- exact H109.
---------------------------------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------------------------------- exact H111.
---------------------------------------------------------------------------------------------------------------- exact H114.
---------------------------------------------------------------------------------------------------------------- exact H115.
---------------------------------------------------------------------------------------------------------------- exact H116.
---------------------------------------------------------------------------------------------------------------- exact H117.
---------------------------------------------------------------------------------------------------------------- exact H118.
---------------------------------------------------------------------------------------------------------------- exact H119.
---------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------- exact H124.
---------------------------------------------------------------------------------------------------------------- exact H125.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C M D) as H128.
---------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H127.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M D C) as H129.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M C D) /\ ((euclidean__axioms.Col M D C) /\ ((euclidean__axioms.Col D C M) /\ ((euclidean__axioms.Col C D M) /\ (euclidean__axioms.Col D M C))))) as H129.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder C M D H128).
------------------------------------------------------------------------------------------------------------------ destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
exact H132.
----------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.Col A M D) as H130 by exact H82.
assert (* Cut *) (euclidean__axioms.Col M D A) as H131.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col M A D) /\ ((euclidean__axioms.Col M D A) /\ ((euclidean__axioms.Col D A M) /\ ((euclidean__axioms.Col A D M) /\ (euclidean__axioms.Col D M A))))) as H131.
------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A M D H130).
------------------------------------------------------------------------------------------------------------------- destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
exact H134.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq M D) as H132.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M D) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C D))) as H132.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C M D H127).
-------------------------------------------------------------------------------------------------------------------- destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
exact H133.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C A) as H133.
-------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col D C A).
---------------------------------------------------------------------------------------------------------------------intro H133.
apply (@euclidean__tactics.Col__nCol__False D C A H133).
----------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 M D C A H129 H131 H132).


-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C B) as H134.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B))))) as H134.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B D C H14).
---------------------------------------------------------------------------------------------------------------------- destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
exact H137.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H135.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M D) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C D))) as H135.
----------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C M D H127).
----------------------------------------------------------------------------------------------------------------------- destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
exact H120.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C A B) as H136.
----------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col C A B).
------------------------------------------------------------------------------------------------------------------------intro H136.
apply (@euclidean__tactics.Col__nCol__False C A B H136).
-------------------------------------------------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D C A B H133 H134 H135).


----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C A) as H137.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C B A) /\ (euclidean__axioms.Col B A C))))) as H137.
------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C A B H136).
------------------------------------------------------------------------------------------------------------------------- destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
exact H142.
------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.Col__nCol__False A D B H102).
-------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col A D B).
--------------------------------------------------------------------------------------------------------------------------intro H138.
apply (@euclidean__tactics.Col__nCol__False B C A H0 H137).


-------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.neq E D) as H127 by exact H126.
assert (* Cut *) (euclidean__axioms.neq D A) as H128.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq E M) /\ (euclidean__axioms.neq E C))) as H128.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E M C H124).
---------------------------------------------------------------------------------------------------------------- destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
exact H68.
--------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.neq A D) as H129 by exact H71.
assert (* Cut *) (euclidean__axioms.Cong E D C A) as H130.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry E M C D A H125 H51 H127).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A E D C) as H131.
----------------------------------------------------------------------------------------------------------------- apply (@lemma__pointreflectionisometry.lemma__pointreflectionisometry A M D E C H86 H125 H117).
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A F) as H132.
------------------------------------------------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H59.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col F A E) as H133.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E))))) as H133.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E A F H132).
-------------------------------------------------------------------------------------------------------------------- destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
exact H141.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F A A) as H134.
-------------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H67.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E A D) as H135.
--------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol E A D).
----------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col E A D).
-----------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper F A D E A H98 H133 H134 H116).


--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA E A D C D A) as H136.
---------------------------------------------------------------------------------------------------------------------- exists E.
exists D.
exists C.
exists A.
split.
----------------------------------------------------------------------------------------------------------------------- exact H119.
----------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------ exact H72.
------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------- exact H122.
------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------- exact H69.
-------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------- exact H131.
--------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------- exact H130.
----------------------------------------------------------------------------------------------------------------------------- exact H135.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C D A) as H137.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A E D) /\ ((euclidean__axioms.nCol A D E) /\ ((euclidean__axioms.nCol D E A) /\ ((euclidean__axioms.nCol E D A) /\ (euclidean__axioms.nCol D A E))))) as H137.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder E A D H135).
------------------------------------------------------------------------------------------------------------------------ destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
exact H19.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C D A A D C) as H138.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA C D A H137).
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA E A D A D C) as H139.
------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive E A D C D A A D C H136 H138).
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D A E) as H140.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A E D) /\ ((euclidean__axioms.nCol A D E) /\ ((euclidean__axioms.nCol D E A) /\ ((euclidean__axioms.nCol E D A) /\ (euclidean__axioms.nCol D A E))))) as H140.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder E A D H135).
--------------------------------------------------------------------------------------------------------------------------- destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
exact H148.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D A E E A D) as H141.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA D A E H140).
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D A E C D A) as H142.
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive D A E E A D C D A H141 H136).
---------------------------------------------------------------------------------------------------------------------------- exists E.
exists F.
exists M.
split.
----------------------------------------------------------------------------------------------------------------------------- exact H59.
----------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------- exact H92.
------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------- exact H104.
-------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------- exact H139.
--------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------- exact H136.
---------------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------------- exact H142.
----------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------ exact H109.
------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------- exact H111.
------------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------------- exact H113.
-------------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------------- exact H7.
--------------------------------------------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------------------------------------------- exact H123.
---------------------------------------------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------------------------------------------- exact H46.
----------------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------------- exact H43.
------------------------------------------------------------------------------------------------------------------------------------------- exact H5.
Qed.
