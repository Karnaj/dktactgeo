Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__3__7a.
Require Export lemma__8__2.
Require Export lemma__9__5.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__PGflip.
Require Export lemma__PGsymmetric.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__collinearright.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equaltorightisright.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray2.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__samenotopposite.
Require Export lemma__triangletoparallelogram.
Require Export logic.
Require Export proposition__11B.
Require Export proposition__31short.
Require Export proposition__34.
Definition proposition__46 : forall A B R, (euclidean__axioms.neq A B) -> ((euclidean__axioms.nCol A B R) -> (exists X Y, (euclidean__defs.SQ A B X Y) /\ ((euclidean__axioms.TS Y A B R) /\ (euclidean__defs.PG A B X Y)))).
Proof.
intro A.
intro B.
intro R.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.neq B A) as H1.
- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H).
- assert (* Cut *) (exists F, (euclidean__axioms.BetS B A F) /\ (euclidean__axioms.Cong A F A B)) as H2.
-- apply (@lemma__extension.lemma__extension B A A B H1 H).
-- destruct H2 as [F H3].
destruct H3 as [H4 H5].
assert (* Cut *) (euclidean__axioms.nCol B A R) as H6.
--- assert (* Cut *) ((euclidean__axioms.nCol B A R) /\ ((euclidean__axioms.nCol B R A) /\ ((euclidean__axioms.nCol R A B) /\ ((euclidean__axioms.nCol A R B) /\ (euclidean__axioms.nCol R B A))))) as H6.
---- apply (@lemma__NCorder.lemma__NCorder A B R H0).
---- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H7.
--- assert (* Cut *) (euclidean__axioms.Col B A F) as H7.
---- right.
right.
right.
right.
left.
exact H4.
---- assert (* Cut *) (B = B) as H8.
----- apply (@logic.eq__refl Point B).
----- assert (* Cut *) (euclidean__axioms.Col B A B) as H9.
------ right.
left.
exact H8.
------ assert (* Cut *) (euclidean__axioms.neq B F) as H10.
------- assert (* Cut *) ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B F))) as H10.
-------- apply (@lemma__betweennotequal.lemma__betweennotequal B A F H4).
-------- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H14.
------- assert (* Cut *) (euclidean__axioms.nCol B F R) as H11.
-------- apply (@euclidean__tactics.nCol__notCol B F R).
---------apply (@euclidean__tactics.nCol__not__Col B F R).
----------apply (@lemma__NChelper.lemma__NChelper B A R B F H6 H9 H7 H10).


-------- assert (* Cut *) (exists C, (euclidean__defs.Per B A C) /\ (euclidean__axioms.TS C B F R)) as H12.
--------- apply (@proposition__11B.proposition__11B B F A R H4 H11).
--------- destruct H12 as [C H13].
destruct H13 as [H14 H15].
assert (* Cut *) (euclidean__axioms.nCol B F C) as H16.
---------- assert (exists X, (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as H16 by exact H15.
assert (exists X, (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as __TmpHyp by exact H16.
destruct __TmpHyp as [x H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H21.
---------- assert (* Cut *) (euclidean__axioms.Col B F A) as H17.
----------- assert (* Cut *) ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col A F B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B F A) /\ (euclidean__axioms.Col F A B))))) as H17.
------------ apply (@lemma__collinearorder.lemma__collinearorder B A F H7).
------------ destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H24.
----------- assert (* Cut *) (euclidean__axioms.Col B F B) as H18.
------------ right.
left.
exact H8.
------------ assert (* Cut *) (euclidean__axioms.nCol B A C) as H19.
------------- apply (@euclidean__tactics.nCol__notCol B A C).
--------------apply (@euclidean__tactics.nCol__not__Col B A C).
---------------apply (@lemma__NChelper.lemma__NChelper B F C B A H16 H18 H17 H1).


------------- assert (* Cut *) (euclidean__axioms.neq A C) as H20.
-------------- assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)))))) as H20.
--------------- apply (@lemma__NCdistinct.lemma__NCdistinct B A C H19).
--------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H23.
-------------- assert (* Cut *) (exists D, (euclidean__defs.Out A C D) /\ (euclidean__axioms.Cong A D A B)) as H21.
--------------- apply (@lemma__layoff.lemma__layoff A C A B H20 H).
--------------- destruct H21 as [D H22].
destruct H22 as [H23 H24].
assert (* Cut *) (euclidean__defs.Out A D C) as H25.
---------------- apply (@lemma__ray5.lemma__ray5 A C D H23).
---------------- assert (* Cut *) (A = A) as H26.
----------------- apply (@logic.eq__refl Point A).
----------------- assert (* Cut *) (euclidean__axioms.Col A B A) as H27.
------------------ right.
left.
exact H26.
------------------ assert (exists q, (euclidean__axioms.BetS C q R) /\ ((euclidean__axioms.Col B F q) /\ (euclidean__axioms.nCol B F C))) as H28 by exact H15.
destruct H28 as [q H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
assert (* Cut *) (euclidean__axioms.Col F B q) as H34.
------------------- assert (* Cut *) ((euclidean__axioms.Col F B q) /\ ((euclidean__axioms.Col F q B) /\ ((euclidean__axioms.Col q B F) /\ ((euclidean__axioms.Col B q F) /\ (euclidean__axioms.Col q F B))))) as H34.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder B F q H32).
-------------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H35.
------------------- assert (B = B) as H35 by exact H8.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H36.
-------------------- apply (@euclidean__tactics.nCol__notCol A B C).
---------------------apply (@euclidean__tactics.nCol__not__Col A B C).
----------------------apply (@lemma__NChelper.lemma__NChelper B F C A B H33 H17 H18 H).


-------------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H37.
--------------------- assert (* Cut *) ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.Col B A F) /\ (euclidean__axioms.Col A F B))))) as H37.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder B F A H17).
---------------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H42.
--------------------- assert (* Cut *) (euclidean__axioms.Col F B A) as H38.
---------------------- assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H38.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder A B F H37).
----------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H46.
---------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H39.
----------------------- assert (* Cut *) ((euclidean__axioms.neq q R) /\ ((euclidean__axioms.neq C q) /\ (euclidean__axioms.neq C R))) as H39.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal C q R H30).
------------------------ destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H10.
----------------------- assert (* Cut *) (euclidean__axioms.neq F B) as H40.
------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B F H39).
------------------------ assert (* Cut *) (euclidean__axioms.Col B A q) as H41.
------------------------- apply (@euclidean__tactics.not__nCol__Col B A q).
--------------------------intro H41.
apply (@euclidean__tactics.Col__nCol__False B A q H41).
---------------------------apply (@lemma__collinear4.lemma__collinear4 F B A q H38 H34 H40).


------------------------- assert (* Cut *) (euclidean__axioms.Col A B q) as H42.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col A B q) /\ ((euclidean__axioms.Col A q B) /\ ((euclidean__axioms.Col q B A) /\ ((euclidean__axioms.Col B q A) /\ (euclidean__axioms.Col q A B))))) as H42.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A q H41).
--------------------------- destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H43.
-------------------------- assert (* Cut *) (euclidean__axioms.TS C A B R) as H43.
--------------------------- exists q.
split.
---------------------------- exact H30.
---------------------------- split.
----------------------------- exact H42.
----------------------------- exact H36.
--------------------------- assert (* Cut *) (euclidean__axioms.TS D A B R) as H44.
---------------------------- apply (@lemma__9__5.lemma__9__5 A B R C D A H43 H25 H27).
---------------------------- assert (* Cut *) (euclidean__axioms.nCol C A B) as H45.
----------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H45.
------------------------------ apply (@lemma__NCorder.lemma__NCorder A B C H36).
------------------------------ destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H50.
----------------------------- assert (A = A) as H46 by exact H26.
assert (* Cut *) (euclidean__axioms.Col C A A) as H47.
------------------------------ right.
right.
left.
exact H46.
------------------------------ assert (* Cut *) (euclidean__axioms.Col A C D) as H48.
------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear A C D H23).
------------------------------- assert (* Cut *) (euclidean__axioms.Col C A D) as H49.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H49.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A C D H48).
--------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H50.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H50.
--------------------------------- apply (@lemma__ray2.lemma__ray2 A D C H25).
--------------------------------- assert (* Cut *) (euclidean__axioms.nCol C A B) as H51.
---------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H51.
----------------------------------- apply (@lemma__NCorder.lemma__NCorder A B C H36).
----------------------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H45.
---------------------------------- assert (* Cut *) (euclidean__axioms.nCol A D B) as H52.
----------------------------------- apply (@euclidean__tactics.nCol__notCol A D B).
------------------------------------apply (@euclidean__tactics.nCol__not__Col A D B).
-------------------------------------apply (@lemma__NChelper.lemma__NChelper C A B A D H51 H47 H49 H50).


----------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B D) as H53.
------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A))))) as H53.
------------------------------------- apply (@lemma__NCorder.lemma__NCorder A D B H52).
------------------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H60.
------------------------------------ assert (* Cut *) (euclidean__axioms.BetS F A B) as H54.
------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B A F H4).
------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H55.
-------------------------------------- right.
right.
left.
exact H35.
-------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F B D) as H56.
--------------------------------------- apply (@euclidean__tactics.nCol__notCol F B D).
----------------------------------------apply (@euclidean__tactics.nCol__not__Col F B D).
-----------------------------------------apply (@lemma__NChelper.lemma__NChelper A B D F B H53 H37 H55 H40).


--------------------------------------- assert (* Cut *) (exists G e M, (euclidean__axioms.BetS G D e) /\ ((euclidean__defs.CongA G D A D A B) /\ ((euclidean__defs.Par G e F B) /\ ((euclidean__axioms.BetS G M B) /\ (euclidean__axioms.BetS D M A))))) as H57.
---------------------------------------- apply (@proposition__31short.proposition__31short D F B A H54 H56).
---------------------------------------- destruct H57 as [G H58].
destruct H58 as [e H59].
destruct H59 as [M H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
assert (* Cut *) (euclidean__defs.Par G e A B) as H69.
----------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel G e A F B H65 H38 H).
----------------------------------------- assert (* Cut *) (euclidean__defs.Par A B G e) as H70.
------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric G e A B H69).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col G D e) as H71.
------------------------------------------- right.
right.
right.
right.
left.
exact H61.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G e D) as H72.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D G e) /\ ((euclidean__axioms.Col D e G) /\ ((euclidean__axioms.Col e G D) /\ ((euclidean__axioms.Col G e D) /\ (euclidean__axioms.Col e D G))))) as H72.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G D e H71).
--------------------------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H79.
-------------------------------------------- assert (* Cut *) (exists E, (euclidean__defs.PG D E B A) /\ (euclidean__axioms.Col G e E)) as H73.
--------------------------------------------- apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram D B A G e H70 H72).
--------------------------------------------- destruct H73 as [E H74].
destruct H74 as [H75 H76].
assert (* Cut *) (euclidean__defs.Per C A B) as H77.
---------------------------------------------- apply (@lemma__8__2.lemma__8__2 B A C H14).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D A) as H78.
----------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A D H50).
----------------------------------------------- assert (* Cut *) (euclidean__defs.Per D A B) as H79.
------------------------------------------------ apply (@lemma__collinearright.lemma__collinearright C A D B H77 H49 H78).
------------------------------------------------ assert (* Cut *) (euclidean__defs.Per B A D) as H80.
------------------------------------------------- apply (@lemma__8__2.lemma__8__2 D A B H79).
------------------------------------------------- assert (* Cut *) (euclidean__defs.Per G D A) as H81.
-------------------------------------------------- apply (@lemma__equaltorightisright.lemma__equaltorightisright D A B G D A H79 H63).
-------------------------------------------------- assert (exists p, (euclidean__axioms.BetS G D p) /\ ((euclidean__axioms.Cong G D p D) /\ ((euclidean__axioms.Cong G A p A) /\ (euclidean__axioms.neq D A)))) as H82 by exact H81.
destruct H82 as [p H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
assert (* Cut *) (euclidean__axioms.BetS p D G) as H90.
--------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry G D p H84).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong p D G D) as H91.
---------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric p G D D H86).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong p A G A) as H92.
----------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric p G A A H88).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.Per p D A) as H93.
------------------------------------------------------ exists G.
split.
------------------------------------------------------- exact H90.
------------------------------------------------------- split.
-------------------------------------------------------- exact H91.
-------------------------------------------------------- split.
--------------------------------------------------------- exact H92.
--------------------------------------------------------- exact H89.
------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par D A E B) as H94.
------------------------------------------------------- destruct H75 as [H94 H95].
exact H95.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP D A E B) as H95.
-------------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B D A E B H94).
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS E B D A) as H96.
--------------------------------------------------------- destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
exact H101.
--------------------------------------------------------- assert (* Cut *) (D = D) as H97.
---------------------------------------------------------- apply (@logic.eq__refl Point D).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D A D) as H98.
----------------------------------------------------------- right.
left.
exact H97.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D A B) as H99.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A D B) /\ (euclidean__axioms.nCol D B A))))) as H99.
------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder A B D H53).
------------------------------------------------------------- destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
exact H104.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS B M G) as H100.
------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry G M B H67).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D M A) as H101.
-------------------------------------------------------------- right.
right.
right.
right.
left.
exact H68.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D A M) as H102.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M D A) /\ ((euclidean__axioms.Col M A D) /\ ((euclidean__axioms.Col A D M) /\ ((euclidean__axioms.Col D A M) /\ (euclidean__axioms.Col A M D))))) as H102.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D M A H101).
---------------------------------------------------------------- destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
exact H109.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS B D A G) as H103.
---------------------------------------------------------------- exists M.
split.
----------------------------------------------------------------- exact H100.
----------------------------------------------------------------- split.
------------------------------------------------------------------ exact H102.
------------------------------------------------------------------ exact H99.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS E D A G) as H104.
----------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation D A E B G H96 H103).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D A E) as H105.
------------------------------------------------------------------ assert (exists X, (euclidean__axioms.BetS E X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A E))) as H105 by exact H104.
assert (exists X, (euclidean__axioms.BetS E X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A E))) as __TmpHyp by exact H105.
destruct __TmpHyp as [x H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
assert (exists X, (euclidean__axioms.BetS B X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A B))) as H111 by exact H103.
assert (exists X, (euclidean__axioms.BetS B X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A B))) as __TmpHyp0 by exact H111.
destruct __TmpHyp0 as [x0 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
assert (exists X, (euclidean__axioms.BetS D X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B D))) as H117 by exact H44.
assert (exists X, (euclidean__axioms.BetS D X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B D))) as __TmpHyp1 by exact H117.
destruct __TmpHyp1 as [x1 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
assert (exists X, (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B C))) as H123 by exact H43.
assert (exists X, (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B C))) as __TmpHyp2 by exact H123.
destruct __TmpHyp2 as [x2 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
assert (exists X, (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as H129 by exact H15.
assert (exists X, (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as __TmpHyp3 by exact H129.
destruct __TmpHyp3 as [x3 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
exact H110.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS G D A E) as H106.
------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric D A E G H104).
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol D A G) as H107.
-------------------------------------------------------------------- assert (exists X, (euclidean__axioms.BetS G X E) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A G))) as H107 by exact H106.
assert (exists X, (euclidean__axioms.BetS G X E) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A G))) as __TmpHyp by exact H107.
destruct __TmpHyp as [x H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
assert (exists X, (euclidean__axioms.BetS E X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A E))) as H113 by exact H104.
assert (exists X, (euclidean__axioms.BetS E X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A E))) as __TmpHyp0 by exact H113.
destruct __TmpHyp0 as [x0 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
assert (exists X, (euclidean__axioms.BetS B X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A B))) as H119 by exact H103.
assert (exists X, (euclidean__axioms.BetS B X G) /\ ((euclidean__axioms.Col D A X) /\ (euclidean__axioms.nCol D A B))) as __TmpHyp1 by exact H119.
destruct __TmpHyp1 as [x1 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
assert (exists X, (euclidean__axioms.BetS D X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B D))) as H125 by exact H44.
assert (exists X, (euclidean__axioms.BetS D X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B D))) as __TmpHyp2 by exact H125.
destruct __TmpHyp2 as [x2 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
assert (exists X, (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B C))) as H131 by exact H43.
assert (exists X, (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B C))) as __TmpHyp3 by exact H131.
destruct __TmpHyp3 as [x3 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
assert (exists X, (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as H137 by exact H15.
assert (exists X, (euclidean__axioms.BetS C X R) /\ ((euclidean__axioms.Col B F X) /\ (euclidean__axioms.nCol B F C))) as __TmpHyp4 by exact H137.
destruct __TmpHyp4 as [x4 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
exact H112.
-------------------------------------------------------------------- assert (exists d, (euclidean__axioms.BetS E d G) /\ ((euclidean__axioms.Col D A d) /\ (euclidean__axioms.nCol D A E))) as H108 by exact H104.
destruct H108 as [d H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
assert (* Cut *) (euclidean__axioms.neq E G) as H114.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq d G) /\ ((euclidean__axioms.neq E d) /\ (euclidean__axioms.neq E G))) as H114.
---------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E d G H110).
---------------------------------------------------------------------- destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
exact H118.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G E) as H115.
---------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E G H114).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G D) as H116.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq D G) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G D)))))) as H116.
------------------------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct D A G H107).
------------------------------------------------------------------------ destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
exact H126.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D E) as H117.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E D)))))) as H117.
------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct D A E H113).
------------------------------------------------------------------------- destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H122.
------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__defs.OS E G D A)) as H118.
------------------------------------------------------------------------- intro H118.
assert (* Cut *) (~(euclidean__axioms.TS E D A G)) as H119.
-------------------------------------------------------------------------- apply (@lemma__samenotopposite.lemma__samenotopposite E G D A H118).
-------------------------------------------------------------------------- apply (@H119 H104).
------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS D G E)) as H119.
-------------------------------------------------------------------------- intro H119.
assert (* Cut *) (euclidean__axioms.BetS E G D) as H120.
--------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry D G E H119).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E D e) as H121.
---------------------------------------------------------------------------- apply (@lemma__3__7a.lemma__3__7a E G D e H120 H61).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS E G D A) as H122.
----------------------------------------------------------------------------- exists e.
exists D.
exists D.
split.
------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------- exact H61.
--------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------- exact H113.
---------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------- apply (@H118 H122).
-------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS G E D)) as H120.
--------------------------------------------------------------------------- intro H120.
assert (* Cut *) (euclidean__axioms.BetS E D e) as H121.
---------------------------------------------------------------------------- apply (@lemma__3__6a.lemma__3__6a G E D e H120 H61).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS E G D A) as H122.
----------------------------------------------------------------------------- exists e.
exists D.
exists D.
split.
------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------- exact H98.
------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------- exact H121.
-------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------- exact H61.
--------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------- exact H113.
---------------------------------------------------------------------------------- exact H107.
----------------------------------------------------------------------------- apply (@H118 H122).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e G D) as H121.
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col e G D) /\ ((euclidean__axioms.Col e D G) /\ ((euclidean__axioms.Col D G e) /\ ((euclidean__axioms.Col G D e) /\ (euclidean__axioms.Col D e G))))) as H121.
----------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G e D H72).
----------------------------------------------------------------------------- destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
exact H122.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col e G E) as H122.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col e G E) /\ ((euclidean__axioms.Col e E G) /\ ((euclidean__axioms.Col E G e) /\ ((euclidean__axioms.Col G E e) /\ (euclidean__axioms.Col E e G))))) as H122.
------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder G e E H76).
------------------------------------------------------------------------------ destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
exact H123.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G e F) as H123.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol G e F) /\ ((euclidean__axioms.nCol G F B) /\ ((euclidean__axioms.nCol e F B) /\ (euclidean__axioms.nCol G e B)))) as H123.
------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC G e F B H65).
------------------------------------------------------------------------------- destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
exact H124.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq G e) as H124.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G e) /\ ((euclidean__axioms.neq e F) /\ ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq e G) /\ ((euclidean__axioms.neq F e) /\ (euclidean__axioms.neq F G)))))) as H124.
-------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct G e F H123).
-------------------------------------------------------------------------------- destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
exact H125.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq e G) as H125.
-------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G e H124).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G D E) as H126.
--------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col G D E).
----------------------------------------------------------------------------------intro H126.
apply (@euclidean__tactics.Col__nCol__False G D E H126).
-----------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 e G D E H121 H122 H125).


--------------------------------------------------------------------------------- assert ((G = D) \/ ((G = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D G E) \/ ((euclidean__axioms.BetS G D E) \/ (euclidean__axioms.BetS G E D)))))) as H127 by exact H126.
assert (* Cut *) (euclidean__axioms.BetS G D E) as H128.
---------------------------------------------------------------------------------- assert ((G = D) \/ ((G = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D G E) \/ ((euclidean__axioms.BetS G D E) \/ (euclidean__axioms.BetS G E D)))))) as H128 by exact H127.
assert ((G = D) \/ ((G = E) \/ ((D = E) \/ ((euclidean__axioms.BetS D G E) \/ ((euclidean__axioms.BetS G D E) \/ (euclidean__axioms.BetS G E D)))))) as __TmpHyp by exact H128.
destruct __TmpHyp as [H129|H129].
----------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS G D E))) as H130.
------------------------------------------------------------------------------------ intro H130.
apply (@H116 H129).
------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS G D E)).
-------------------------------------------------------------------------------------intro H131.
destruct H0 as [H132 H133].
destruct H6 as [H134 H135].
destruct H11 as [H136 H137].
destruct H16 as [H138 H139].
destruct H19 as [H140 H141].
destruct H33 as [H142 H143].
destruct H36 as [H144 H145].
destruct H45 as [H146 H147].
destruct H51 as [H148 H149].
destruct H52 as [H150 H151].
destruct H53 as [H152 H153].
destruct H56 as [H154 H155].
destruct H99 as [H156 H157].
destruct H105 as [H158 H159].
destruct H107 as [H160 H161].
destruct H113 as [H162 H163].
destruct H123 as [H164 H165].
destruct H133 as [H166 H167].
destruct H135 as [H168 H169].
destruct H137 as [H170 H171].
destruct H139 as [H172 H173].
destruct H141 as [H174 H175].
destruct H143 as [H176 H177].
destruct H145 as [H178 H179].
destruct H147 as [H180 H181].
destruct H149 as [H182 H183].
destruct H151 as [H184 H185].
destruct H153 as [H186 H187].
destruct H155 as [H188 H189].
destruct H157 as [H190 H191].
destruct H159 as [H192 H193].
destruct H161 as [H194 H195].
destruct H163 as [H196 H197].
destruct H165 as [H198 H199].
destruct H167 as [H200 H201].
destruct H169 as [H202 H203].
destruct H171 as [H204 H205].
destruct H173 as [H206 H207].
destruct H175 as [H208 H209].
destruct H177 as [H210 H211].
destruct H179 as [H212 H213].
destruct H181 as [H214 H215].
destruct H183 as [H216 H217].
destruct H185 as [H218 H219].
destruct H187 as [H220 H221].
destruct H189 as [H222 H223].
destruct H191 as [H224 H225].
destruct H193 as [H226 H227].
destruct H195 as [H228 H229].
destruct H197 as [H230 H231].
destruct H199 as [H232 H233].
destruct H201 as [H234 H235].
destruct H203 as [H236 H237].
destruct H205 as [H238 H239].
destruct H207 as [H240 H241].
destruct H209 as [H242 H243].
destruct H211 as [H244 H245].
destruct H213 as [H246 H247].
destruct H215 as [H248 H249].
destruct H217 as [H250 H251].
destruct H219 as [H252 H253].
destruct H221 as [H254 H255].
destruct H223 as [H256 H257].
destruct H225 as [H258 H259].
destruct H227 as [H260 H261].
destruct H229 as [H262 H263].
destruct H231 as [H264 H265].
destruct H233 as [H266 H267].
destruct H235 as [H268 H269].
destruct H237 as [H270 H271].
destruct H239 as [H272 H273].
destruct H241 as [H274 H275].
destruct H243 as [H276 H277].
destruct H245 as [H278 H279].
destruct H247 as [H280 H281].
destruct H249 as [H282 H283].
destruct H251 as [H284 H285].
destruct H253 as [H286 H287].
destruct H255 as [H288 H289].
destruct H257 as [H290 H291].
destruct H259 as [H292 H293].
destruct H261 as [H294 H295].
destruct H263 as [H296 H297].
destruct H265 as [H298 H299].
destruct H267 as [H300 H301].
assert (* Cut *) (False) as H302.
-------------------------------------------------------------------------------------- apply (@H116 H129).
-------------------------------------------------------------------------------------- assert (* Cut *) (False) as H303.
--------------------------------------------------------------------------------------- apply (@H130 H131).
--------------------------------------------------------------------------------------- contradiction H303.

----------------------------------------------------------------------------------- destruct H129 as [H130|H130].
------------------------------------------------------------------------------------ assert (* Cut *) (~(~(euclidean__axioms.BetS G D E))) as H131.
------------------------------------------------------------------------------------- intro H131.
apply (@H115 H130).
------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS G D E)).
--------------------------------------------------------------------------------------intro H132.
destruct H0 as [H133 H134].
destruct H6 as [H135 H136].
destruct H11 as [H137 H138].
destruct H16 as [H139 H140].
destruct H19 as [H141 H142].
destruct H33 as [H143 H144].
destruct H36 as [H145 H146].
destruct H45 as [H147 H148].
destruct H51 as [H149 H150].
destruct H52 as [H151 H152].
destruct H53 as [H153 H154].
destruct H56 as [H155 H156].
destruct H99 as [H157 H158].
destruct H105 as [H159 H160].
destruct H107 as [H161 H162].
destruct H113 as [H163 H164].
destruct H123 as [H165 H166].
destruct H134 as [H167 H168].
destruct H136 as [H169 H170].
destruct H138 as [H171 H172].
destruct H140 as [H173 H174].
destruct H142 as [H175 H176].
destruct H144 as [H177 H178].
destruct H146 as [H179 H180].
destruct H148 as [H181 H182].
destruct H150 as [H183 H184].
destruct H152 as [H185 H186].
destruct H154 as [H187 H188].
destruct H156 as [H189 H190].
destruct H158 as [H191 H192].
destruct H160 as [H193 H194].
destruct H162 as [H195 H196].
destruct H164 as [H197 H198].
destruct H166 as [H199 H200].
destruct H168 as [H201 H202].
destruct H170 as [H203 H204].
destruct H172 as [H205 H206].
destruct H174 as [H207 H208].
destruct H176 as [H209 H210].
destruct H178 as [H211 H212].
destruct H180 as [H213 H214].
destruct H182 as [H215 H216].
destruct H184 as [H217 H218].
destruct H186 as [H219 H220].
destruct H188 as [H221 H222].
destruct H190 as [H223 H224].
destruct H192 as [H225 H226].
destruct H194 as [H227 H228].
destruct H196 as [H229 H230].
destruct H198 as [H231 H232].
destruct H200 as [H233 H234].
destruct H202 as [H235 H236].
destruct H204 as [H237 H238].
destruct H206 as [H239 H240].
destruct H208 as [H241 H242].
destruct H210 as [H243 H244].
destruct H212 as [H245 H246].
destruct H214 as [H247 H248].
destruct H216 as [H249 H250].
destruct H218 as [H251 H252].
destruct H220 as [H253 H254].
destruct H222 as [H255 H256].
destruct H224 as [H257 H258].
destruct H226 as [H259 H260].
destruct H228 as [H261 H262].
destruct H230 as [H263 H264].
destruct H232 as [H265 H266].
destruct H234 as [H267 H268].
destruct H236 as [H269 H270].
destruct H238 as [H271 H272].
destruct H240 as [H273 H274].
destruct H242 as [H275 H276].
destruct H244 as [H277 H278].
destruct H246 as [H279 H280].
destruct H248 as [H281 H282].
destruct H250 as [H283 H284].
destruct H252 as [H285 H286].
destruct H254 as [H287 H288].
destruct H256 as [H289 H290].
destruct H258 as [H291 H292].
destruct H260 as [H293 H294].
destruct H262 as [H295 H296].
destruct H264 as [H297 H298].
destruct H266 as [H299 H300].
destruct H268 as [H301 H302].
assert (* Cut *) (False) as H303.
--------------------------------------------------------------------------------------- apply (@H115 H130).
--------------------------------------------------------------------------------------- assert (* Cut *) (False) as H304.
---------------------------------------------------------------------------------------- apply (@H131 H132).
---------------------------------------------------------------------------------------- contradiction H304.

------------------------------------------------------------------------------------ destruct H130 as [H131|H131].
------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS G D E))) as H132.
-------------------------------------------------------------------------------------- intro H132.
apply (@H117 H131).
-------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS G D E)).
---------------------------------------------------------------------------------------intro H133.
destruct H0 as [H134 H135].
destruct H6 as [H136 H137].
destruct H11 as [H138 H139].
destruct H16 as [H140 H141].
destruct H19 as [H142 H143].
destruct H33 as [H144 H145].
destruct H36 as [H146 H147].
destruct H45 as [H148 H149].
destruct H51 as [H150 H151].
destruct H52 as [H152 H153].
destruct H53 as [H154 H155].
destruct H56 as [H156 H157].
destruct H99 as [H158 H159].
destruct H105 as [H160 H161].
destruct H107 as [H162 H163].
destruct H113 as [H164 H165].
destruct H123 as [H166 H167].
destruct H135 as [H168 H169].
destruct H137 as [H170 H171].
destruct H139 as [H172 H173].
destruct H141 as [H174 H175].
destruct H143 as [H176 H177].
destruct H145 as [H178 H179].
destruct H147 as [H180 H181].
destruct H149 as [H182 H183].
destruct H151 as [H184 H185].
destruct H153 as [H186 H187].
destruct H155 as [H188 H189].
destruct H157 as [H190 H191].
destruct H159 as [H192 H193].
destruct H161 as [H194 H195].
destruct H163 as [H196 H197].
destruct H165 as [H198 H199].
destruct H167 as [H200 H201].
destruct H169 as [H202 H203].
destruct H171 as [H204 H205].
destruct H173 as [H206 H207].
destruct H175 as [H208 H209].
destruct H177 as [H210 H211].
destruct H179 as [H212 H213].
destruct H181 as [H214 H215].
destruct H183 as [H216 H217].
destruct H185 as [H218 H219].
destruct H187 as [H220 H221].
destruct H189 as [H222 H223].
destruct H191 as [H224 H225].
destruct H193 as [H226 H227].
destruct H195 as [H228 H229].
destruct H197 as [H230 H231].
destruct H199 as [H232 H233].
destruct H201 as [H234 H235].
destruct H203 as [H236 H237].
destruct H205 as [H238 H239].
destruct H207 as [H240 H241].
destruct H209 as [H242 H243].
destruct H211 as [H244 H245].
destruct H213 as [H246 H247].
destruct H215 as [H248 H249].
destruct H217 as [H250 H251].
destruct H219 as [H252 H253].
destruct H221 as [H254 H255].
destruct H223 as [H256 H257].
destruct H225 as [H258 H259].
destruct H227 as [H260 H261].
destruct H229 as [H262 H263].
destruct H231 as [H264 H265].
destruct H233 as [H266 H267].
destruct H235 as [H268 H269].
destruct H237 as [H270 H271].
destruct H239 as [H272 H273].
destruct H241 as [H274 H275].
destruct H243 as [H276 H277].
destruct H245 as [H278 H279].
destruct H247 as [H280 H281].
destruct H249 as [H282 H283].
destruct H251 as [H284 H285].
destruct H253 as [H286 H287].
destruct H255 as [H288 H289].
destruct H257 as [H290 H291].
destruct H259 as [H292 H293].
destruct H261 as [H294 H295].
destruct H263 as [H296 H297].
destruct H265 as [H298 H299].
destruct H267 as [H300 H301].
destruct H269 as [H302 H303].
assert (* Cut *) (False) as H304.
---------------------------------------------------------------------------------------- apply (@H117 H131).
---------------------------------------------------------------------------------------- assert (* Cut *) (False) as H305.
----------------------------------------------------------------------------------------- apply (@H132 H133).
----------------------------------------------------------------------------------------- contradiction H305.

------------------------------------------------------------------------------------- destruct H131 as [H132|H132].
-------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS G D E))) as H133.
--------------------------------------------------------------------------------------- intro H133.
apply (@H119 H132).
--------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS G D E)).
----------------------------------------------------------------------------------------intro H134.
destruct H0 as [H135 H136].
destruct H6 as [H137 H138].
destruct H11 as [H139 H140].
destruct H16 as [H141 H142].
destruct H19 as [H143 H144].
destruct H33 as [H145 H146].
destruct H36 as [H147 H148].
destruct H45 as [H149 H150].
destruct H51 as [H151 H152].
destruct H52 as [H153 H154].
destruct H53 as [H155 H156].
destruct H56 as [H157 H158].
destruct H99 as [H159 H160].
destruct H105 as [H161 H162].
destruct H107 as [H163 H164].
destruct H113 as [H165 H166].
destruct H123 as [H167 H168].
destruct H136 as [H169 H170].
destruct H138 as [H171 H172].
destruct H140 as [H173 H174].
destruct H142 as [H175 H176].
destruct H144 as [H177 H178].
destruct H146 as [H179 H180].
destruct H148 as [H181 H182].
destruct H150 as [H183 H184].
destruct H152 as [H185 H186].
destruct H154 as [H187 H188].
destruct H156 as [H189 H190].
destruct H158 as [H191 H192].
destruct H160 as [H193 H194].
destruct H162 as [H195 H196].
destruct H164 as [H197 H198].
destruct H166 as [H199 H200].
destruct H168 as [H201 H202].
destruct H170 as [H203 H204].
destruct H172 as [H205 H206].
destruct H174 as [H207 H208].
destruct H176 as [H209 H210].
destruct H178 as [H211 H212].
destruct H180 as [H213 H214].
destruct H182 as [H215 H216].
destruct H184 as [H217 H218].
destruct H186 as [H219 H220].
destruct H188 as [H221 H222].
destruct H190 as [H223 H224].
destruct H192 as [H225 H226].
destruct H194 as [H227 H228].
destruct H196 as [H229 H230].
destruct H198 as [H231 H232].
destruct H200 as [H233 H234].
destruct H202 as [H235 H236].
destruct H204 as [H237 H238].
destruct H206 as [H239 H240].
destruct H208 as [H241 H242].
destruct H210 as [H243 H244].
destruct H212 as [H245 H246].
destruct H214 as [H247 H248].
destruct H216 as [H249 H250].
destruct H218 as [H251 H252].
destruct H220 as [H253 H254].
destruct H222 as [H255 H256].
destruct H224 as [H257 H258].
destruct H226 as [H259 H260].
destruct H228 as [H261 H262].
destruct H230 as [H263 H264].
destruct H232 as [H265 H266].
destruct H234 as [H267 H268].
destruct H236 as [H269 H270].
destruct H238 as [H271 H272].
destruct H240 as [H273 H274].
destruct H242 as [H275 H276].
destruct H244 as [H277 H278].
destruct H246 as [H279 H280].
destruct H248 as [H281 H282].
destruct H250 as [H283 H284].
destruct H252 as [H285 H286].
destruct H254 as [H287 H288].
destruct H256 as [H289 H290].
destruct H258 as [H291 H292].
destruct H260 as [H293 H294].
destruct H262 as [H295 H296].
destruct H264 as [H297 H298].
destruct H266 as [H299 H300].
destruct H268 as [H301 H302].
destruct H270 as [H303 H304].
assert (* Cut *) (False) as H305.
----------------------------------------------------------------------------------------- apply (@H119 H132).
----------------------------------------------------------------------------------------- assert (* Cut *) (False) as H306.
------------------------------------------------------------------------------------------ apply (@H133 H134).
------------------------------------------------------------------------------------------ contradiction H306.

-------------------------------------------------------------------------------------- destruct H132 as [H133|H133].
--------------------------------------------------------------------------------------- exact H133.
--------------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__axioms.BetS G D E))) as H134.
---------------------------------------------------------------------------------------- intro H134.
apply (@H120 H133).
---------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS G D E)).
-----------------------------------------------------------------------------------------intro H135.
destruct H0 as [H136 H137].
destruct H6 as [H138 H139].
destruct H11 as [H140 H141].
destruct H16 as [H142 H143].
destruct H19 as [H144 H145].
destruct H33 as [H146 H147].
destruct H36 as [H148 H149].
destruct H45 as [H150 H151].
destruct H51 as [H152 H153].
destruct H52 as [H154 H155].
destruct H53 as [H156 H157].
destruct H56 as [H158 H159].
destruct H99 as [H160 H161].
destruct H105 as [H162 H163].
destruct H107 as [H164 H165].
destruct H113 as [H166 H167].
destruct H123 as [H168 H169].
destruct H137 as [H170 H171].
destruct H139 as [H172 H173].
destruct H141 as [H174 H175].
destruct H143 as [H176 H177].
destruct H145 as [H178 H179].
destruct H147 as [H180 H181].
destruct H149 as [H182 H183].
destruct H151 as [H184 H185].
destruct H153 as [H186 H187].
destruct H155 as [H188 H189].
destruct H157 as [H190 H191].
destruct H159 as [H192 H193].
destruct H161 as [H194 H195].
destruct H163 as [H196 H197].
destruct H165 as [H198 H199].
destruct H167 as [H200 H201].
destruct H169 as [H202 H203].
destruct H171 as [H204 H205].
destruct H173 as [H206 H207].
destruct H175 as [H208 H209].
destruct H177 as [H210 H211].
destruct H179 as [H212 H213].
destruct H181 as [H214 H215].
destruct H183 as [H216 H217].
destruct H185 as [H218 H219].
destruct H187 as [H220 H221].
destruct H189 as [H222 H223].
destruct H191 as [H224 H225].
destruct H193 as [H226 H227].
destruct H195 as [H228 H229].
destruct H197 as [H230 H231].
destruct H199 as [H232 H233].
destruct H201 as [H234 H235].
destruct H203 as [H236 H237].
destruct H205 as [H238 H239].
destruct H207 as [H240 H241].
destruct H209 as [H242 H243].
destruct H211 as [H244 H245].
destruct H213 as [H246 H247].
destruct H215 as [H248 H249].
destruct H217 as [H250 H251].
destruct H219 as [H252 H253].
destruct H221 as [H254 H255].
destruct H223 as [H256 H257].
destruct H225 as [H258 H259].
destruct H227 as [H260 H261].
destruct H229 as [H262 H263].
destruct H231 as [H264 H265].
destruct H233 as [H266 H267].
destruct H235 as [H268 H269].
destruct H237 as [H270 H271].
destruct H239 as [H272 H273].
destruct H241 as [H274 H275].
destruct H243 as [H276 H277].
destruct H245 as [H278 H279].
destruct H247 as [H280 H281].
destruct H249 as [H282 H283].
destruct H251 as [H284 H285].
destruct H253 as [H286 H287].
destruct H255 as [H288 H289].
destruct H257 as [H290 H291].
destruct H259 as [H292 H293].
destruct H261 as [H294 H295].
destruct H263 as [H296 H297].
destruct H265 as [H298 H299].
destruct H267 as [H300 H301].
destruct H269 as [H302 H303].
destruct H271 as [H304 H305].
assert (* Cut *) (False) as H306.
------------------------------------------------------------------------------------------ apply (@H120 H133).
------------------------------------------------------------------------------------------ assert (* Cut *) (False) as H307.
------------------------------------------------------------------------------------------- apply (@H134 H135).
------------------------------------------------------------------------------------------- contradiction H307.

---------------------------------------------------------------------------------- assert (euclidean__axioms.Col G D E) as H129 by exact H127.
assert (* Cut *) (euclidean__axioms.neq E D) as H130.
----------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric D E H117).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per E D A) as H131.
------------------------------------------------------------------------------------ apply (@lemma__collinearright.lemma__collinearright G D E A H81 H129 H130).
------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Cong D A E B) /\ ((euclidean__axioms.Cong D E A B) /\ ((euclidean__defs.CongA E D A A B E) /\ ((euclidean__defs.CongA D A B B E D) /\ (euclidean__axioms.Cong__3 E D A A B E))))) as H132.
------------------------------------------------------------------------------------- apply (@proposition__34.proposition__34 D A E B H75).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B D E) as H133.
-------------------------------------------------------------------------------------- destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A D E B H135).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B E D) as H134.
--------------------------------------------------------------------------------------- destruct H132 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
assert (* Cut *) ((euclidean__axioms.Cong B A E D) /\ ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D))) as H142.
---------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A B D E H133).
---------------------------------------------------------------------------------------- destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
exact H146.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A D) as H135.
---------------------------------------------------------------------------------------- destruct H132 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A D B H24).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A D E B) as H136.
----------------------------------------------------------------------------------------- destruct H132 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
assert (* Cut *) ((euclidean__axioms.Cong A D B E) /\ ((euclidean__axioms.Cong A D E B) /\ (euclidean__axioms.Cong D A B E))) as H144.
------------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip D A E B H136).
------------------------------------------------------------------------------------------ destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
exact H147.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B E B) as H137.
------------------------------------------------------------------------------------------ destruct H132 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
apply (@lemma__congruencetransitive.lemma__congruencetransitive A B A D E B H135 H136).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A B B E) as H138.
------------------------------------------------------------------------------------------- destruct H132 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
assert (* Cut *) ((euclidean__axioms.Cong B A B E) /\ ((euclidean__axioms.Cong B A E B) /\ (euclidean__axioms.Cong A B B E))) as H146.
-------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A B E B H137).
-------------------------------------------------------------------------------------------- destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
exact H150.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B D A) as H139.
-------------------------------------------------------------------------------------------- destruct H132 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
assert (* Cut *) ((euclidean__axioms.Cong B A D A) /\ ((euclidean__axioms.Cong B A A D) /\ (euclidean__axioms.Cong A B D A))) as H147.
--------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A B A D H135).
--------------------------------------------------------------------------------------------- destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
exact H151.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B E D D A B) as H140.
--------------------------------------------------------------------------------------------- destruct H132 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric D A B B E D H146).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B E E D A) as H141.
---------------------------------------------------------------------------------------------- destruct H132 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric E D A A B E H145).
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per B E D) as H142.
----------------------------------------------------------------------------------------------- destruct H132 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
destruct H147 as [H148 H149].
apply (@lemma__equaltorightisright.lemma__equaltorightisright D A B B E D H79 H140).
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per A B E) as H143.
------------------------------------------------------------------------------------------------ destruct H132 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
apply (@lemma__equaltorightisright.lemma__equaltorightisright E D A A B E H131 H141).
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.SQ A B E D) as H144.
------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------- exact H134.
-------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------- exact H138.
--------------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------------- exact H139.
---------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------- exact H79.
----------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------ exact H143.
------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------- exact H142.
------------------------------------------------------------------------------------------------------- exact H131.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG B A D E) as H145.
-------------------------------------------------------------------------------------------------- destruct H132 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
apply (@lemma__PGsymmetric.lemma__PGsymmetric D E B A H75).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG A B E D) as H146.
--------------------------------------------------------------------------------------------------- destruct H132 as [H146 H147].
destruct H147 as [H148 H149].
destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
apply (@lemma__PGflip.lemma__PGflip B A D E H145).
--------------------------------------------------------------------------------------------------- exists E.
exists D.
split.
---------------------------------------------------------------------------------------------------- exact H144.
---------------------------------------------------------------------------------------------------- split.
----------------------------------------------------------------------------------------------------- exact H44.
----------------------------------------------------------------------------------------------------- exact H146.
Qed.
