Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__crossbar.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray2.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export logic.
Require Export proposition__16.
Definition proposition__17 : forall A B C, (euclidean__axioms.Triangle A B C) -> (exists X Y Z, euclidean__defs.SumA A B C B C A X Y Z).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (euclidean__axioms.nCol A B C) as H0 by exact H.
assert (* Cut *) (euclidean__axioms.neq B C) as H1.
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H1.
-- apply (@lemma__NCdistinct.lemma__NCdistinct A B C H0).
-- destruct H1 as [H2 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H4.
- assert (* Cut *) (exists D, (euclidean__axioms.BetS B C D) /\ (euclidean__axioms.Cong C D B C)) as H2.
-- apply (@lemma__extension.lemma__extension B C B C H1 H1).
-- destruct H2 as [D H3].
destruct H3 as [H4 H5].
assert (* Cut *) (euclidean__axioms.nCol B C A) as H6.
--- assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H6.
---- apply (@lemma__NCorder.lemma__NCorder A B C H0).
---- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H9.
--- assert (* Cut *) (euclidean__axioms.Col B C D) as H7.
---- right.
right.
right.
right.
left.
exact H4.
---- assert (* Cut *) (B = B) as H8.
----- apply (@logic.eq__refl Point B).
----- assert (* Cut *) (euclidean__axioms.Col B C B) as H9.
------ right.
left.
exact H8.
------ assert (* Cut *) (euclidean__axioms.neq B D) as H10.
------- assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D))) as H10.
-------- apply (@lemma__betweennotequal.lemma__betweennotequal B C D H4).
-------- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H14.
------- assert (* Cut *) (euclidean__axioms.nCol B D A) as H11.
-------- apply (@euclidean__tactics.nCol__notCol B D A).
---------apply (@euclidean__tactics.nCol__not__Col B D A).
----------apply (@lemma__NChelper.lemma__NChelper B C A B D H6 H9 H7 H10).


-------- assert (* Cut *) (euclidean__axioms.nCol A D B) as H12.
--------- assert (* Cut *) ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol B A D) /\ (euclidean__axioms.nCol A D B))))) as H12.
---------- apply (@lemma__NCorder.lemma__NCorder B D A H11).
---------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H20.
--------- assert (* Cut *) (euclidean__defs.LtA C B A A C D) as H13.
---------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA C0 B0 A0 A0 C0 D0))) as H13.
----------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
------------ apply (@proposition__16.proposition__16 A0 B0 C0 D0 __ __0).
------------ destruct __1 as [__1 __2].
exact __2.
----------- apply (@H13 A B C D H0 H4).
---------- assert (* Cut *) (euclidean__defs.CongA A B C C B A) as H14.
----------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A B C H0).
----------- assert (* Cut *) (euclidean__defs.LtA A B C A C D) as H15.
------------ apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 C B A A C D A B C H13 H14).
------------ assert (* Cut *) (exists a d e, (euclidean__axioms.BetS a e d) /\ ((euclidean__defs.Out C A a) /\ ((euclidean__defs.Out C D d) /\ (euclidean__defs.CongA A B C A C e)))) as H16.
------------- assert (exists U X V, (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out C A U) /\ ((euclidean__defs.Out C D V) /\ (euclidean__defs.CongA A B C A C X)))) as H16 by exact H15.
assert (exists U X V, (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out C A U) /\ ((euclidean__defs.Out C D V) /\ (euclidean__defs.CongA A B C A C X)))) as __TmpHyp by exact H16.
destruct __TmpHyp as [x H17].
destruct H17 as [x0 H18].
destruct H18 as [x1 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
assert (exists U X V, (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out C A U) /\ ((euclidean__defs.Out C D V) /\ (euclidean__defs.CongA C B A A C X)))) as H26 by exact H13.
assert (exists U X V, (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out C A U) /\ ((euclidean__defs.Out C D V) /\ (euclidean__defs.CongA C B A A C X)))) as __TmpHyp0 by exact H26.
destruct __TmpHyp0 as [x2 H27].
destruct H27 as [x3 H28].
destruct H28 as [x4 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exists x.
exists x1.
exists x0.
split.
-------------- exact H20.
-------------- split.
--------------- exact H22.
--------------- split.
---------------- exact H24.
---------------- exact H25.
------------- destruct H16 as [a H17].
destruct H17 as [d H18].
destruct H18 as [e H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
assert (* Cut *) (euclidean__defs.Out C a A) as H26.
-------------- apply (@lemma__ray5.lemma__ray5 C A a H22).
-------------- assert (* Cut *) (euclidean__defs.Out C d D) as H27.
--------------- apply (@lemma__ray5.lemma__ray5 C D d H24).
--------------- assert (euclidean__axioms.Col B C D) as H28 by exact H7.
assert (* Cut *) (C = C) as H29.
---------------- apply (@logic.eq__refl Point C).
---------------- assert (* Cut *) (euclidean__axioms.Col B C C) as H30.
----------------- right.
right.
left.
exact H29.
----------------- assert (* Cut *) (euclidean__axioms.nCol B C A) as H31.
------------------ assert (* Cut *) ((euclidean__axioms.nCol D A B) /\ ((euclidean__axioms.nCol D B A) /\ ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A B D) /\ (euclidean__axioms.nCol B D A))))) as H31.
------------------- apply (@lemma__NCorder.lemma__NCorder A D B H12).
------------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H6.
------------------ assert (* Cut *) (euclidean__axioms.neq C D) as H32.
------------------- assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B D))) as H32.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B C D H4).
-------------------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H33.
------------------- assert (* Cut *) (euclidean__axioms.nCol C D A) as H33.
-------------------- apply (@euclidean__tactics.nCol__notCol C D A).
---------------------apply (@euclidean__tactics.nCol__not__Col C D A).
----------------------apply (@lemma__NChelper.lemma__NChelper B C A C D H31 H30 H28 H32).


-------------------- assert (* Cut *) (euclidean__axioms.Col C D C) as H34.
--------------------- right.
left.
exact H29.
--------------------- assert (* Cut *) (euclidean__axioms.Col C D d) as H35.
---------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear C D d H24).
---------------------- assert (* Cut *) (euclidean__axioms.neq C d) as H36.
----------------------- apply (@lemma__ray2.lemma__ray2 C d D H27).
----------------------- assert (* Cut *) (euclidean__axioms.nCol C d A) as H37.
------------------------ apply (@euclidean__tactics.nCol__notCol C d A).
-------------------------apply (@euclidean__tactics.nCol__not__Col C d A).
--------------------------apply (@lemma__NChelper.lemma__NChelper C D A C d H33 H34 H35 H36).


------------------------ assert (* Cut *) (euclidean__axioms.nCol C A d) as H38.
------------------------- assert (* Cut *) ((euclidean__axioms.nCol d C A) /\ ((euclidean__axioms.nCol d A C) /\ ((euclidean__axioms.nCol A C d) /\ ((euclidean__axioms.nCol C A d) /\ (euclidean__axioms.nCol A d C))))) as H38.
-------------------------- apply (@lemma__NCorder.lemma__NCorder C d A H37).
-------------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H45.
------------------------- assert (* Cut *) (euclidean__axioms.Col C A a) as H39.
-------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear C A a H22).
-------------------------- assert (* Cut *) (euclidean__axioms.Col C A C) as H40.
--------------------------- right.
left.
exact H29.
--------------------------- assert (* Cut *) (euclidean__axioms.neq C a) as H41.
---------------------------- apply (@lemma__ray2.lemma__ray2 C a A H26).
---------------------------- assert (* Cut *) (euclidean__axioms.nCol C a d) as H42.
----------------------------- apply (@euclidean__tactics.nCol__notCol C a d).
------------------------------apply (@euclidean__tactics.nCol__not__Col C a d).
-------------------------------apply (@lemma__NChelper.lemma__NChelper C A d C a H38 H40 H39 H41).


----------------------------- assert (* Cut *) (euclidean__axioms.nCol a C d) as H43.
------------------------------ assert (* Cut *) ((euclidean__axioms.nCol a C d) /\ ((euclidean__axioms.nCol a d C) /\ ((euclidean__axioms.nCol d C a) /\ ((euclidean__axioms.nCol C d a) /\ (euclidean__axioms.nCol d a C))))) as H43.
------------------------------- apply (@lemma__NCorder.lemma__NCorder C a d H42).
------------------------------- destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H44.
------------------------------ assert (* Cut *) (euclidean__axioms.nCol D A C) as H44.
------------------------------- assert (* Cut *) ((euclidean__axioms.nCol D C A) /\ ((euclidean__axioms.nCol D A C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol C A D) /\ (euclidean__axioms.nCol A D C))))) as H44.
-------------------------------- apply (@lemma__NCorder.lemma__NCorder C D A H33).
-------------------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H47.
------------------------------- assert (euclidean__axioms.Triangle a C d) as H45 by exact H43.
assert (* Cut *) (exists E, (euclidean__defs.Out C e E) /\ (euclidean__axioms.BetS A E D)) as H46.
-------------------------------- apply (@lemma__crossbar.lemma__crossbar a C d e A D H45 H20 H26 H27).
-------------------------------- destruct H46 as [E H47].
destruct H47 as [H48 H49].
assert (* Cut *) (euclidean__defs.Out C E e) as H50.
--------------------------------- apply (@lemma__ray5.lemma__ray5 C e E H48).
--------------------------------- assert (* Cut *) (euclidean__axioms.Col A E D) as H51.
---------------------------------- right.
right.
right.
right.
left.
exact H49.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col D A E) as H52.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col E D A) /\ ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col A D E) /\ (euclidean__axioms.Col D E A))))) as H52.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A E D H51).
------------------------------------ destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H57.
----------------------------------- assert (* Cut *) (A = A) as H53.
------------------------------------ apply (@logic.eq__refl Point A).
------------------------------------ assert (* Cut *) (euclidean__axioms.Col D A A) as H54.
------------------------------------- right.
right.
left.
exact H53.
------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H55.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A D))) as H55.
--------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A E D H49).
--------------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H58.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq E A) as H56.
--------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A E H55).
--------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E A C) as H57.
---------------------------------------- apply (@euclidean__tactics.nCol__notCol E A C).
-----------------------------------------apply (@euclidean__tactics.nCol__not__Col E A C).
------------------------------------------apply (@lemma__NChelper.lemma__NChelper D A C E A H44 H52 H54 H56).


---------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A C E) as H58.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A E C) /\ ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol C E A) /\ ((euclidean__axioms.nCol E C A) /\ (euclidean__axioms.nCol C A E))))) as H58.
------------------------------------------ apply (@lemma__NCorder.lemma__NCorder E A C H57).
------------------------------------------ destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H61.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E A) as H59.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol C A E) /\ ((euclidean__axioms.nCol C E A) /\ ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol A E C) /\ (euclidean__axioms.nCol E C A))))) as H59.
------------------------------------------- apply (@lemma__NCorder.lemma__NCorder A C E H58).
------------------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H62.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C E e) as H60.
------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear C E e H50).
------------------------------------------- assert (C = C) as H61 by exact H29.
assert (* Cut *) (euclidean__axioms.Col C E C) as H62.
-------------------------------------------- right.
left.
exact H61.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C e) as H63.
--------------------------------------------- apply (@lemma__ray2.lemma__ray2 C e E H48).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C e A) as H64.
---------------------------------------------- apply (@euclidean__tactics.nCol__notCol C e A).
-----------------------------------------------apply (@euclidean__tactics.nCol__not__Col C e A).
------------------------------------------------apply (@lemma__NChelper.lemma__NChelper C E A C e H59 H62 H60 H63).


---------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A C e) as H65.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol e C A) /\ ((euclidean__axioms.nCol e A C) /\ ((euclidean__axioms.nCol A C e) /\ ((euclidean__axioms.nCol C A e) /\ (euclidean__axioms.nCol A e C))))) as H65.
------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder C e A H64).
------------------------------------------------ destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H70.
----------------------------------------------- assert (euclidean__axioms.Col C A a) as H66 by exact H39.
assert (* Cut *) (euclidean__axioms.Col A C a) as H67.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A C a) /\ ((euclidean__axioms.Col A a C) /\ ((euclidean__axioms.Col a C A) /\ ((euclidean__axioms.Col C a A) /\ (euclidean__axioms.Col a A C))))) as H67.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C A a H66).
------------------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H68.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col A C C) as H68.
------------------------------------------------- right.
right.
left.
exact H61.
------------------------------------------------- assert (euclidean__axioms.neq C a) as H69 by exact H41.
assert (* Cut *) (euclidean__axioms.neq a C) as H70.
-------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C a H69).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol a C e) as H71.
--------------------------------------------------- apply (@euclidean__tactics.nCol__notCol a C e).
----------------------------------------------------apply (@euclidean__tactics.nCol__not__Col a C e).
-----------------------------------------------------apply (@lemma__NChelper.lemma__NChelper A C e a C H65 H67 H68 H70).


--------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E C A) as H72.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E C A) /\ ((euclidean__axioms.nCol E A C) /\ ((euclidean__axioms.nCol A C E) /\ ((euclidean__axioms.nCol C A E) /\ (euclidean__axioms.nCol A E C))))) as H72.
----------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder C E A H59).
----------------------------------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H73.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA a C e a C e) as H73.
----------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive a C e H71).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA a C e A C E) as H74.
------------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper a C e a C e A E H73 H26 H48).
------------------------------------------------------ assert (* Cut *) (e = e) as H75.
------------------------------------------------------- apply (@logic.eq__refl Point e).
------------------------------------------------------- assert (euclidean__axioms.neq C e) as H76 by exact H63.
assert (* Cut *) (euclidean__defs.Out C e e) as H77.
-------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 C e e).
---------------------------------------------------------right.
left.
exact H75.

--------------------------------------------------------- exact H76.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A C e A C e) as H78.
--------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive A C e H65).
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A C e a C e) as H79.
---------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper A C e A C e a e H78 H22 H77).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C a C e) as H80.
----------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B C A C e a C e H25 H79).
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C A C E) as H81.
------------------------------------------------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B C a C e A C E H80 H74).
------------------------------------------------------------ assert (B = B) as H82 by exact H8.
assert (* Cut *) (exists F, (euclidean__axioms.BetS A F C) /\ (euclidean__axioms.BetS B F E)) as H83.
------------------------------------------------------------- apply (@euclidean__axioms.postulate__Pasch__inner A B D E C H49 H4 H12).
------------------------------------------------------------- destruct H83 as [F H84].
destruct H84 as [H85 H86].
assert (* Cut *) (euclidean__axioms.nCol A C B) as H87.
-------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C B A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol B A C) /\ (euclidean__axioms.nCol A C B))))) as H87.
--------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder B C A H31).
--------------------------------------------------------------- destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H95.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F C) as H88.
--------------------------------------------------------------- right.
right.
right.
right.
left.
exact H85.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C F) as H89.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F A C) /\ ((euclidean__axioms.Col F C A) /\ ((euclidean__axioms.Col C A F) /\ ((euclidean__axioms.Col A C F) /\ (euclidean__axioms.Col C F A))))) as H89.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A F C H88).
----------------------------------------------------------------- destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
exact H96.
---------------------------------------------------------------- assert (euclidean__axioms.Col A C C) as H90 by exact H68.
assert (* Cut *) (euclidean__axioms.neq F C) as H91.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq A F) /\ (euclidean__axioms.neq A C))) as H91.
------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A F C H85).
------------------------------------------------------------------ destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H92.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F C B) as H92.
------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol F C B).
-------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col F C B).
--------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper A C B F C H87 H89 H90 H91).


------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol B C F) as H93.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C F B) /\ ((euclidean__axioms.nCol C B F) /\ ((euclidean__axioms.nCol B F C) /\ ((euclidean__axioms.nCol F B C) /\ (euclidean__axioms.nCol B C F))))) as H93.
-------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder F C B H92).
-------------------------------------------------------------------- destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
exact H101.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS E F B) as H94.
-------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B F E H86).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A C E E C A) as H95.
--------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A C E H58).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C E C A) as H96.
---------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B C A C E E C A H81 H95).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA E C A E C A) as H97.
----------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive E C A H72).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C F A) as H98.
------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry A F C H85).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C F) as H99.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F A) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C A))) as H99.
-------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C F A H98).
-------------------------------------------------------------------------- destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
exact H102.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C F A) as H100.
-------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 C F A).
---------------------------------------------------------------------------right.
right.
exact H98.

--------------------------------------------------------------------------- exact H99.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C A F) as H101.
--------------------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 C F A H100).
--------------------------------------------------------------------------- assert (* Cut *) (E = E) as H102.
---------------------------------------------------------------------------- apply (@logic.eq__refl Point E).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C E) as H103.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A E)))))) as H103.
------------------------------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct E C A H72).
------------------------------------------------------------------------------ destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
exact H110.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C E E) as H104.
------------------------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 C E E).
-------------------------------------------------------------------------------right.
left.
exact H102.

------------------------------------------------------------------------------- exact H103.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA E C A E C F) as H105.
------------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper E C A E C A E F H97 H104 H101).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B C E C F) as H106.
-------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B C E C A E C F H96 H105).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C A) as H107.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C B F) /\ ((euclidean__axioms.nCol C F B) /\ ((euclidean__axioms.nCol F B C) /\ ((euclidean__axioms.nCol B F C) /\ (euclidean__axioms.nCol F C B))))) as H107.
---------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder B C F H93).
---------------------------------------------------------------------------------- destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
exact H31.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C A B C A) as H108.
---------------------------------------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive B C A H107).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H109.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A B)))))) as H109.
------------------------------------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct B C A H107).
------------------------------------------------------------------------------------ destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
destruct H117 as [H118 H119].
exact H116.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C B B) as H110.
------------------------------------------------------------------------------------ apply (@lemma__ray4.lemma__ray4 C B B).
-------------------------------------------------------------------------------------right.
left.
exact H82.

------------------------------------------------------------------------------------- exact H109.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA B C A B C F) as H111.
------------------------------------------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper B C A B C A B F H108 H110 H101).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C F F C B) as H112.
-------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B C F H93).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C A F C B) as H113.
--------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive B C A B C F F C B H111 H112).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.SumA A B C B C A E C B) as H114.
---------------------------------------------------------------------------------------- exists F.
split.
----------------------------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------ exact H113.
------------------------------------------------------------------------------------------ exact H94.
---------------------------------------------------------------------------------------- exists E.
exists C.
exists B.
exact H114.
Qed.
