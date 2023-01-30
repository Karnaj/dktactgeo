Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel2.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__ray1.
Require Export lemma__ray3.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export logic.
Require Export proposition__04.
Require Export proposition__10.
Require Export proposition__15.
Require Export proposition__27B.
Require Export proposition__37.
Definition proposition__39A : forall A B C D M, (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.ET A B C D B C) -> ((euclidean__axioms.BetS A M C) -> ((euclidean__defs.Out B D M) -> (euclidean__defs.Par A D B C)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro M.
intro H.
intro H0.
intro H1.
intro H2.
assert (euclidean__axioms.nCol A B C) as H3 by exact H.
assert (* Cut *) (euclidean__axioms.neq A B) as H4.
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H4.
-- apply (@lemma__NCdistinct.lemma__NCdistinct A B C H3).
-- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H5.
- assert (* Cut *) (exists m, (euclidean__axioms.BetS A m B) /\ (euclidean__axioms.Cong m A m B)) as H5.
-- apply (@proposition__10.proposition__10 A B H4).
-- destruct H5 as [m H6].
destruct H6 as [H7 H8].
assert (* Cut *) (euclidean__axioms.Col A m B) as H9.
--- right.
right.
right.
right.
left.
exact H7.
--- assert (* Cut *) (euclidean__axioms.Col A B m) as H10.
---- assert (* Cut *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H10.
----- apply (@lemma__collinearorder.lemma__collinearorder A m B H9).
----- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H17.
---- assert (* Cut *) (A = A) as H11.
----- apply (@logic.eq__refl Point A).
----- assert (* Cut *) (euclidean__axioms.Col A B A) as H12.
------ right.
left.
exact H11.
------ assert (* Cut *) (euclidean__axioms.neq A m) as H13.
------- assert (* Cut *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A B))) as H13.
-------- apply (@lemma__betweennotequal.lemma__betweennotequal A m B H7).
-------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H16.
------- assert (* Cut *) (euclidean__axioms.nCol A m C) as H14.
-------- apply (@euclidean__tactics.nCol__notCol A m C).
---------apply (@euclidean__tactics.nCol__not__Col A m C).
----------apply (@lemma__NChelper.lemma__NChelper A B C A m H3 H12 H10 H13).


-------- assert (* Cut *) (euclidean__axioms.neq m C) as H15.
--------- assert (* Cut *) ((euclidean__axioms.neq A m) /\ ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C A)))))) as H15.
---------- apply (@lemma__NCdistinct.lemma__NCdistinct A m C H14).
---------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H18.
--------- assert (* Cut *) (euclidean__axioms.neq C m) as H16.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric m C H15).
---------- assert (* Cut *) (exists H17, (euclidean__axioms.BetS C m H17) /\ (euclidean__axioms.Cong m H17 m C)) as H17.
----------- apply (@lemma__extension.lemma__extension C m m C H16 H15).
----------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
assert (* Cut *) (euclidean__axioms.BetS B m A) as H22.
------------ apply (@euclidean__axioms.axiom__betweennesssymmetry A m B H7).
------------ assert (* Cut *) (euclidean__axioms.BetS C M A) as H23.
------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A M C H1).
------------- assert (* Cut *) (euclidean__axioms.Cong m B m A) as H24.
-------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric m m A B H8).
-------------- assert (* Cut *) (euclidean__axioms.Cong B m A m) as H25.
--------------- assert (* Cut *) ((euclidean__axioms.Cong B m A m) /\ ((euclidean__axioms.Cong B m m A) /\ (euclidean__axioms.Cong m B A m))) as H25.
---------------- apply (@lemma__congruenceflip.lemma__congruenceflip m B m A H24).
---------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H26.
--------------- assert (* Cut *) (euclidean__axioms.Cong m C m H18) as H26.
---------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric m m H18 C H21).
---------------- assert (* Cut *) (~(euclidean__axioms.Col B A H18)) as H27.
----------------- intro H27.
assert (euclidean__axioms.Col A m B) as H28 by exact H9.
assert (* Cut *) (euclidean__axioms.Col B A m) as H29.
------------------ assert (* Cut *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H29.
------------------- apply (@lemma__collinearorder.lemma__collinearorder A m B H28).
------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H34.
------------------ assert (* Cut *) (euclidean__axioms.neq B A) as H30.
------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H4).
------------------- assert (* Cut *) (euclidean__axioms.Col A H18 m) as H31.
-------------------- apply (@euclidean__tactics.not__nCol__Col A H18 m).
---------------------intro H31.
apply (@euclidean__tactics.Col__nCol__False A H18 m H31).
----------------------apply (@lemma__collinear4.lemma__collinear4 B A H18 m H27 H29 H30).


-------------------- assert (* Cut *) (euclidean__axioms.Col H18 m A) as H32.
--------------------- assert (* Cut *) ((euclidean__axioms.Col H18 A m) /\ ((euclidean__axioms.Col H18 m A) /\ ((euclidean__axioms.Col m A H18) /\ ((euclidean__axioms.Col A m H18) /\ (euclidean__axioms.Col m H18 A))))) as H32.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder A H18 m H31).
---------------------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H35.
--------------------- assert (* Cut *) (euclidean__axioms.Col C m H18) as H33.
---------------------- right.
right.
right.
right.
left.
exact H20.
---------------------- assert (* Cut *) (euclidean__axioms.Col H18 m C) as H34.
----------------------- assert (* Cut *) ((euclidean__axioms.Col m C H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))))) as H34.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder C m H18 H33).
------------------------ destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H42.
----------------------- assert (* Cut *) (euclidean__axioms.neq m H18) as H35.
------------------------ assert (* Cut *) ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C H18))) as H35.
------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C m H18 H20).
------------------------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H36.
------------------------ assert (* Cut *) (euclidean__axioms.neq H18 m) as H36.
------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric m H18 H35).
------------------------- assert (* Cut *) (euclidean__axioms.Col m A C) as H37.
-------------------------- apply (@euclidean__tactics.not__nCol__Col m A C).
---------------------------intro H37.
apply (@euclidean__tactics.Col__nCol__False m A C H37).
----------------------------apply (@lemma__collinear4.lemma__collinear4 H18 m A C H32 H34 H36).


-------------------------- assert (* Cut *) (euclidean__axioms.Col m A B) as H38.
--------------------------- assert (* Cut *) ((euclidean__axioms.Col A B m) /\ ((euclidean__axioms.Col A m B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B m A) /\ (euclidean__axioms.Col m A B))))) as H38.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A m H29).
---------------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H46.
--------------------------- assert (* Cut *) (euclidean__axioms.neq A m) as H39.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq M A) /\ ((euclidean__axioms.neq C M) /\ (euclidean__axioms.neq C A))) as H39.
----------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C M A H23).
----------------------------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H13.
---------------------------- assert (* Cut *) (euclidean__axioms.neq m A) as H40.
----------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A m H39).
----------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H41.
------------------------------ apply (@euclidean__tactics.not__nCol__Col A B C).
-------------------------------intro H41.
apply (@euclidean__tactics.Col__nCol__False A B C H41).
--------------------------------apply (@lemma__collinear4.lemma__collinear4 m A B C H38 H37 H40).


------------------------------ apply (@euclidean__tactics.Col__nCol__False A m C H14).
-------------------------------apply (@euclidean__tactics.not__nCol__Col A m C).
--------------------------------intro H42.
apply (@euclidean__tactics.Col__nCol__False A B C H3 H41).


----------------- assert (* Cut *) (exists E, (euclidean__axioms.BetS B M E) /\ (euclidean__axioms.BetS H18 A E)) as H28.
------------------ apply (@euclidean__axioms.postulate__Euclid5 M B A C H18 m H20 H22 H23 H25 H26).
-------------------apply (@euclidean__tactics.nCol__notCol B A H18 H27).

------------------ destruct H28 as [E H29].
destruct H29 as [H30 H31].
assert (* Cut *) (euclidean__axioms.BetS H18 m C) as H32.
------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C m H18 H20).
------------------- assert (* Cut *) (euclidean__axioms.Col C m H18) as H33.
-------------------- right.
right.
right.
right.
left.
exact H20.
-------------------- assert (* Cut *) (euclidean__axioms.Col m C H18) as H34.
--------------------- assert (* Cut *) ((euclidean__axioms.Col m C H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))))) as H34.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder C m H18 H33).
---------------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H35.
--------------------- assert (* Cut *) (m = m) as H35.
---------------------- apply (@logic.eq__refl Point m).
---------------------- assert (* Cut *) (euclidean__axioms.Col m C m) as H36.
----------------------- right.
left.
exact H35.
----------------------- assert (* Cut *) (euclidean__axioms.nCol m C A) as H37.
------------------------ assert (* Cut *) ((euclidean__axioms.nCol m A C) /\ ((euclidean__axioms.nCol m C A) /\ ((euclidean__axioms.nCol C A m) /\ ((euclidean__axioms.nCol A C m) /\ (euclidean__axioms.nCol C m A))))) as H37.
------------------------- apply (@lemma__NCorder.lemma__NCorder A m C H14).
------------------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H40.
------------------------ assert (* Cut *) (euclidean__axioms.neq m H18) as H38.
------------------------- assert (* Cut *) ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C H18))) as H38.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C m H18 H20).
-------------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H39.
------------------------- assert (* Cut *) (euclidean__axioms.nCol m H18 A) as H39.
-------------------------- apply (@euclidean__tactics.nCol__notCol m H18 A).
---------------------------apply (@euclidean__tactics.nCol__not__Col m H18 A).
----------------------------apply (@lemma__NChelper.lemma__NChelper m C A m H18 H37 H36 H34 H38).


-------------------------- assert (* Cut *) (euclidean__axioms.nCol A m H18) as H40.
--------------------------- assert (* Cut *) ((euclidean__axioms.nCol H18 m A) /\ ((euclidean__axioms.nCol H18 A m) /\ ((euclidean__axioms.nCol A m H18) /\ ((euclidean__axioms.nCol m A H18) /\ (euclidean__axioms.nCol A H18 m))))) as H40.
---------------------------- apply (@lemma__NCorder.lemma__NCorder m H18 A H39).
---------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H45.
--------------------------- assert (* Cut *) (euclidean__defs.CongA A m H18 C m B) as H41.
---------------------------- apply (@proposition__15.proposition__15a A B H18 C m H7 H32 H40).
---------------------------- assert (* Cut *) (euclidean__axioms.nCol H18 m A) as H42.
----------------------------- assert (* Cut *) ((euclidean__axioms.nCol m A H18) /\ ((euclidean__axioms.nCol m H18 A) /\ ((euclidean__axioms.nCol H18 A m) /\ ((euclidean__axioms.nCol A H18 m) /\ (euclidean__axioms.nCol H18 m A))))) as H42.
------------------------------ apply (@lemma__NCorder.lemma__NCorder A m H18 H40).
------------------------------ destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H50.
----------------------------- assert (euclidean__axioms.Col A m B) as H43 by exact H9.
assert (* Cut *) (euclidean__axioms.Col A B m) as H44.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col m A B) /\ ((euclidean__axioms.Col m B A) /\ ((euclidean__axioms.Col B A m) /\ ((euclidean__axioms.Col A B m) /\ (euclidean__axioms.Col B m A))))) as H44.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A m B H43).
------------------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H51.
------------------------------ assert (* Cut *) (B = B) as H45.
------------------------------- apply (@logic.eq__refl Point B).
------------------------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H46.
-------------------------------- right.
right.
left.
exact H45.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq m B) as H47.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A B))) as H47.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A m B H7).
---------------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H48.
--------------------------------- assert (* Cut *) (euclidean__axioms.nCol m B C) as H48.
---------------------------------- apply (@euclidean__tactics.nCol__notCol m B C).
-----------------------------------apply (@euclidean__tactics.nCol__not__Col m B C).
------------------------------------apply (@lemma__NChelper.lemma__NChelper A B C m B H3 H44 H46 H47).


---------------------------------- assert (* Cut *) (euclidean__defs.CongA H18 m A A m H18) as H49.
----------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA H18 m A H42).
----------------------------------- assert (* Cut *) (euclidean__defs.CongA H18 m A C m B) as H50.
------------------------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive H18 m A A m H18 C m B H49 H41).
------------------------------------ assert (euclidean__axioms.Cong m A m B) as H51 by exact H8.
assert (* Cut *) (euclidean__defs.CongA m H18 A m C B) as H52.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong m H18 m C) -> ((euclidean__axioms.Cong m A m B) -> ((euclidean__defs.CongA H18 m A C m B) -> ((euclidean__defs.CongA m H18 A m C B) /\ (euclidean__defs.CongA m A H18 m B C))))) as H52.
-------------------------------------- intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong H18 A C B) /\ ((euclidean__defs.CongA m H18 A m C B) /\ (euclidean__defs.CongA m A H18 m B C))) as __2.
--------------------------------------- apply (@proposition__04.proposition__04 m H18 A m C B __ __0 __1).
--------------------------------------- destruct __2 as [__2 __3].
exact __3.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong m H18 m C) -> ((euclidean__axioms.Cong m A m B) -> ((euclidean__defs.CongA H18 m A C m B) -> (euclidean__defs.CongA m H18 A m C B)))) as H53.
--------------------------------------- intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA m H18 A m C B) /\ (euclidean__defs.CongA m A H18 m B C)) as __2.
---------------------------------------- apply (@H52 __ __0 __1).
---------------------------------------- destruct __2 as [__2 __3].
exact __2.
--------------------------------------- apply (@H53 H21 H51 H50).
------------------------------------- assert (B = B) as H53 by exact H45.
assert (* Cut *) (euclidean__axioms.neq B C) as H54.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq B m) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C m)))))) as H54.
--------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct m B C H48).
--------------------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H57.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H55.
--------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B C H54).
--------------------------------------- assert (* Cut *) (euclidean__defs.Out C B B) as H56.
---------------------------------------- apply (@lemma__ray4.lemma__ray4 C B B).
-----------------------------------------right.
left.
exact H53.

----------------------------------------- exact H55.
---------------------------------------- assert (* Cut *) (euclidean__defs.Out C m H18) as H57.
----------------------------------------- apply (@lemma__ray4.lemma__ray4 C m H18).
------------------------------------------right.
right.
exact H20.

------------------------------------------ exact H16.
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA m H18 A H18 C B) as H58.
------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper m H18 A m C B H18 B H52 H57 H56).
------------------------------------------ assert (* Cut *) (euclidean__defs.CongA H18 C B m H18 A) as H59.
------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric m H18 A H18 C B H58).
------------------------------------------- assert (A = A) as H60 by exact H11.
assert (* Cut *) (euclidean__axioms.neq H18 A) as H61.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H18 m) /\ ((euclidean__axioms.neq m A) /\ ((euclidean__axioms.neq H18 A) /\ ((euclidean__axioms.neq m H18) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A H18)))))) as H61.
--------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct H18 m A H42).
--------------------------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H66.
-------------------------------------------- assert (* Cut *) (euclidean__defs.Out H18 A A) as H62.
--------------------------------------------- apply (@lemma__ray4.lemma__ray4 H18 A A).
----------------------------------------------right.
left.
exact H60.

---------------------------------------------- exact H61.
--------------------------------------------- assert (euclidean__axioms.BetS H18 m C) as H63 by exact H32.
assert (* Cut *) (euclidean__axioms.neq H18 m) as H64.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq H18 m) /\ (euclidean__axioms.neq H18 C))) as H64.
----------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H18 m C H63).
----------------------------------------------- destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H67.
---------------------------------------------- assert (* Cut *) (euclidean__defs.Out H18 m C) as H65.
----------------------------------------------- apply (@lemma__ray4.lemma__ray4 H18 m C).
------------------------------------------------right.
right.
exact H63.

------------------------------------------------ exact H64.
----------------------------------------------- assert (* Cut *) (euclidean__defs.CongA H18 C B C H18 A) as H66.
------------------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper H18 C B m H18 A C A H59 H65 H62).
------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C H18 A H18 C B) as H67.
------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric H18 C B C H18 A H66).
------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A H18 C B C H18) as H68.
-------------------------------------------------- apply (@lemma__equalanglesflip.lemma__equalanglesflip C H18 A H18 C B H67).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C H18) as H69.
--------------------------------------------------- apply (@euclidean__tactics.nCol__notCol B C H18).
----------------------------------------------------apply (@euclidean__tactics.nCol__not__Col B C H18).
-----------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC A H18 C B C H18 H68).


--------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C H18 H18 C B) as H70.
---------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B C H18 H69).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A H18 C H18 C B) as H71.
----------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A H18 C B C H18 H18 C B H68 H70).
----------------------------------------------------- assert (euclidean__axioms.Col C m H18) as H72 by exact H33.
assert (* Cut *) (euclidean__axioms.Col H18 C m) as H73.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col m C H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 C m) /\ ((euclidean__axioms.Col C H18 m) /\ (euclidean__axioms.Col H18 m C))))) as H73.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C m H18 H72).
------------------------------------------------------- destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
exact H78.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H18 m C) as H74.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C H18 m) /\ ((euclidean__axioms.Col C m H18) /\ ((euclidean__axioms.Col m H18 C) /\ ((euclidean__axioms.Col H18 m C) /\ (euclidean__axioms.Col m C H18))))) as H74.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H18 C m H73).
-------------------------------------------------------- destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H81.
------------------------------------------------------- assert (* Cut *) (H18 = H18) as H75.
-------------------------------------------------------- apply (@logic.eq__refl Point H18).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H18 m H18) as H76.
--------------------------------------------------------- right.
left.
exact H75.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H18 C) as H77.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq H18 m) /\ (euclidean__axioms.neq H18 C))) as H77.
----------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H18 m C H63).
----------------------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
exact H81.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H18 C A) as H78.
----------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol H18 C A).
------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col H18 C A).
-------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper H18 m A H18 C H42 H76 H74 H77).


----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS A H18 C B) as H79.
------------------------------------------------------------ exists m.
split.
------------------------------------------------------------- exact H7.
------------------------------------------------------------- split.
-------------------------------------------------------------- exact H73.
-------------------------------------------------------------- exact H78.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par A H18 C B) as H80.
------------------------------------------------------------- apply (@proposition__27B.proposition__27B A B H18 C H71 H79).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H18 A E) as H81.
-------------------------------------------------------------- right.
right.
right.
right.
left.
exact H31.
-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H18 E) as H82.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A H18 E) /\ ((euclidean__axioms.Col A E H18) /\ ((euclidean__axioms.Col E H18 A) /\ ((euclidean__axioms.Col H18 E A) /\ (euclidean__axioms.Col E A H18))))) as H82.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H18 A E H81).
---------------------------------------------------------------- destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H83.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H18 A) as H83.
---------------------------------------------------------------- right.
left.
exact H60.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A E) as H84.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq H18 A) /\ (euclidean__axioms.neq H18 E))) as H84.
------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal H18 A E H31).
------------------------------------------------------------------ destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H85.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C B A H18) as H85.
------------------------------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A H18 C B H80).
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par C B A E) as H86.
------------------------------------------------------------------- apply (@lemma__collinearparallel2.lemma__collinearparallel2 C B A H18 A E H85 H83 H82 H84).
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A E C B) as H87.
-------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric C B A E H86).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A E B C) as H88.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par E A C B) /\ ((euclidean__defs.Par A E B C) /\ (euclidean__defs.Par E A B C))) as H88.
---------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip A E C B H87).
---------------------------------------------------------------------- destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
exact H91.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET A B C E B C) as H89.
---------------------------------------------------------------------- apply (@proposition__37.proposition__37 A B C E H88).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D B C A B C) as H90.
----------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric A B C D B C H0).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET D B C E B C) as H91.
------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__ETtransitive D B C E B C A B C H90 H89).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B M D) as H92.
------------------------------------------------------------------------- apply (@lemma__ray5.lemma__ray5 B D M H2).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B M) as H93.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B E))) as H93.
--------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B M E H30).
--------------------------------------------------------------------------- destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
exact H96.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B M E) as H94.
--------------------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 B M E).
----------------------------------------------------------------------------right.
right.
exact H30.

---------------------------------------------------------------------------- exact H93.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B D E) as H95.
---------------------------------------------------------------------------- apply (@lemma__ray3.lemma__ray3 B M D E H92 H94).
---------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS B E D) \/ ((D = E) \/ (euclidean__axioms.BetS B D E))) as H96.
----------------------------------------------------------------------------- apply (@lemma__ray1.lemma__ray1 B D E H95).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A D B C) as H97.
------------------------------------------------------------------------------ assert ((euclidean__axioms.BetS B E D) \/ ((D = E) \/ (euclidean__axioms.BetS B D E))) as H97 by exact H96.
assert ((euclidean__axioms.BetS B E D) \/ ((D = E) \/ (euclidean__axioms.BetS B D E))) as __TmpHyp by exact H97.
destruct __TmpHyp as [H98|H98].
------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Par A D B C))) as H99.
-------------------------------------------------------------------------------- intro H99.
assert (* Cut *) (~(euclidean__axioms.ET D B C E B C)) as H100.
--------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__deZolt1 B C D E H98).
--------------------------------------------------------------------------------- apply (@H27).
----------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col B A H18).
-----------------------------------------------------------------------------------intro H101.
apply (@H100 H91).


-------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Par A D B C)).
---------------------------------------------------------------------------------intro H100.
destruct H3 as [H101 H102].
destruct H14 as [H103 H104].
destruct H37 as [H105 H106].
destruct H39 as [H107 H108].
destruct H40 as [H109 H110].
destruct H42 as [H111 H112].
destruct H48 as [H113 H114].
destruct H69 as [H115 H116].
destruct H78 as [H117 H118].
destruct H102 as [H119 H120].
destruct H104 as [H121 H122].
destruct H106 as [H123 H124].
destruct H108 as [H125 H126].
destruct H110 as [H127 H128].
destruct H112 as [H129 H130].
destruct H114 as [H131 H132].
destruct H116 as [H133 H134].
destruct H118 as [H135 H136].
destruct H120 as [H137 H138].
destruct H122 as [H139 H140].
destruct H124 as [H141 H142].
destruct H126 as [H143 H144].
destruct H128 as [H145 H146].
destruct H130 as [H147 H148].
destruct H132 as [H149 H150].
destruct H134 as [H151 H152].
destruct H136 as [H153 H154].
destruct H138 as [H155 H156].
destruct H140 as [H157 H158].
destruct H142 as [H159 H160].
destruct H144 as [H161 H162].
destruct H146 as [H163 H164].
destruct H148 as [H165 H166].
destruct H150 as [H167 H168].
destruct H152 as [H169 H170].
destruct H154 as [H171 H172].
destruct H156 as [H173 H174].
destruct H158 as [H175 H176].
destruct H160 as [H177 H178].
destruct H162 as [H179 H180].
destruct H164 as [H181 H182].
destruct H166 as [H183 H184].
destruct H168 as [H185 H186].
destruct H170 as [H187 H188].
destruct H172 as [H189 H190].
assert (* Cut *) (False) as H191.
---------------------------------------------------------------------------------- apply (@H99 H100).
---------------------------------------------------------------------------------- contradiction H191.

------------------------------------------------------------------------------- destruct H98 as [H99|H99].
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A D B C) as H100.
--------------------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun D0 => (euclidean__axioms.ET A B C D0 B C) -> ((euclidean__defs.Out B D0 M) -> ((euclidean__axioms.ET D0 B C A B C) -> ((euclidean__axioms.ET D0 B C E B C) -> ((euclidean__defs.Out B M D0) -> ((euclidean__defs.Out B D0 E) -> (euclidean__defs.Par A D0 B C)))))))) with (x := D).
----------------------------------------------------------------------------------intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
exact H88.

---------------------------------------------------------------------------------- exact H99.
---------------------------------------------------------------------------------- exact H0.
---------------------------------------------------------------------------------- exact H2.
---------------------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------------------- exact H91.
---------------------------------------------------------------------------------- exact H92.
---------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------- exact H100.
-------------------------------------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Par A D B C))) as H100.
--------------------------------------------------------------------------------- intro H100.
assert (* Cut *) (~(euclidean__axioms.ET E B C D B C)) as H101.
---------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__deZolt1 B C E D H99).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.ET E B C D B C) as H102.
----------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__ETsymmetric D B C E B C H91).
----------------------------------------------------------------------------------- apply (@H27).
------------------------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col B A H18).
-------------------------------------------------------------------------------------intro H103.
apply (@H101 H102).


--------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Par A D B C)).
----------------------------------------------------------------------------------intro H101.
destruct H3 as [H102 H103].
destruct H14 as [H104 H105].
destruct H37 as [H106 H107].
destruct H39 as [H108 H109].
destruct H40 as [H110 H111].
destruct H42 as [H112 H113].
destruct H48 as [H114 H115].
destruct H69 as [H116 H117].
destruct H78 as [H118 H119].
destruct H103 as [H120 H121].
destruct H105 as [H122 H123].
destruct H107 as [H124 H125].
destruct H109 as [H126 H127].
destruct H111 as [H128 H129].
destruct H113 as [H130 H131].
destruct H115 as [H132 H133].
destruct H117 as [H134 H135].
destruct H119 as [H136 H137].
destruct H121 as [H138 H139].
destruct H123 as [H140 H141].
destruct H125 as [H142 H143].
destruct H127 as [H144 H145].
destruct H129 as [H146 H147].
destruct H131 as [H148 H149].
destruct H133 as [H150 H151].
destruct H135 as [H152 H153].
destruct H137 as [H154 H155].
destruct H139 as [H156 H157].
destruct H141 as [H158 H159].
destruct H143 as [H160 H161].
destruct H145 as [H162 H163].
destruct H147 as [H164 H165].
destruct H149 as [H166 H167].
destruct H151 as [H168 H169].
destruct H153 as [H170 H171].
destruct H155 as [H172 H173].
destruct H157 as [H174 H175].
destruct H159 as [H176 H177].
destruct H161 as [H178 H179].
destruct H163 as [H180 H181].
destruct H165 as [H182 H183].
destruct H167 as [H184 H185].
destruct H169 as [H186 H187].
destruct H171 as [H188 H189].
destruct H173 as [H190 H191].
assert (* Cut *) (False) as H192.
----------------------------------------------------------------------------------- apply (@H100 H101).
----------------------------------------------------------------------------------- contradiction H192.

------------------------------------------------------------------------------ exact H97.
Qed.
