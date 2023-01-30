Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__5b.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__28A.
Require Export proposition__29.
Definition proposition__30B : forall A B C D E F G H K, (euclidean__defs.Par A B E F) -> ((euclidean__defs.Par C D E F) -> ((euclidean__axioms.BetS G K H) -> ((euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS E H F) -> ((euclidean__axioms.BetS C K D) -> ((euclidean__axioms.TS A G H F) -> ((euclidean__axioms.TS C K H F) -> (euclidean__defs.Par A B C D)))))))).
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
assert (* Cut *) (euclidean__axioms.neq G H) as H8.
- assert (* Cut *) ((euclidean__axioms.neq K H) /\ ((euclidean__axioms.neq G K) /\ (euclidean__axioms.neq G H))) as H8.
-- apply (@lemma__betweennotequal.lemma__betweennotequal G K H H2).
-- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H12.
- assert (* Cut *) (euclidean__axioms.neq H G) as H9.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G H H8).
-- assert (* Cut *) (euclidean__axioms.neq K H) as H10.
--- assert (* Cut *) ((euclidean__axioms.neq K H) /\ ((euclidean__axioms.neq G K) /\ (euclidean__axioms.neq G H))) as H10.
---- apply (@lemma__betweennotequal.lemma__betweennotequal G K H H2).
---- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H11.
--- assert (* Cut *) (euclidean__axioms.neq H K) as H11.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric K H H10).
---- assert (* Cut *) (exists P, (euclidean__axioms.BetS H G P) /\ (euclidean__axioms.Cong G P G H)) as H12.
----- apply (@lemma__extension.lemma__extension H G G H H9 H8).
----- destruct H12 as [P H13].
destruct H13 as [H14 H15].
assert (* Cut *) (euclidean__axioms.BetS P G H) as H16.
------ apply (@euclidean__axioms.axiom__betweennesssymmetry H G P H14).
------ assert (* Cut *) (euclidean__defs.CongA A G H G H F) as H17.
------- assert (* Cut *) ((euclidean__defs.Par A B E F) -> ((euclidean__axioms.BetS A G B) -> ((euclidean__axioms.BetS E H F) -> ((euclidean__axioms.BetS P G H) -> ((euclidean__axioms.TS A G H F) -> (euclidean__defs.CongA A G H G H F)))))) as H17.
-------- intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.CongA A G H G H F) /\ ((euclidean__defs.CongA P G B G H F) /\ (euclidean__defs.RT B G H G H F))) as __4.
--------- apply (@proposition__29.proposition__29 A B E F P G H __ __0 __1 __2 __3).
--------- destruct __4 as [__4 __5].
exact __4.
-------- apply (@H17 H0 H3 H4 H16 H6).
------- assert (* Cut *) (euclidean__axioms.BetS P K H) as H18.
-------- apply (@lemma__3__5b.lemma__3__5b P G K H H16 H2).
-------- assert (* Cut *) (euclidean__defs.CongA C K H K H F) as H19.
--------- assert (* Cut *) (forall G0 H19, (euclidean__defs.Par C D E F) -> ((euclidean__axioms.BetS C G0 D) -> ((euclidean__axioms.BetS E H19 F) -> ((euclidean__axioms.BetS P G0 H19) -> ((euclidean__axioms.TS C G0 H19 F) -> (euclidean__defs.CongA C G0 H19 G0 H19 F)))))) as H19.
---------- intro G0.
intro H19.
intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.CongA C G0 H19 G0 H19 F) /\ ((euclidean__defs.CongA P G0 D G0 H19 F) /\ (euclidean__defs.RT D G0 H19 G0 H19 F))) as __4.
----------- apply (@proposition__29.proposition__29 C D E F P G0 H19 __ __0 __1 __2 __3).
----------- destruct __4 as [__4 __5].
exact __4.
---------- apply (@H19 K H H1 H5 H4 H18 H7).
--------- assert (* Cut *) (euclidean__axioms.BetS H K G) as H20.
---------- apply (@euclidean__axioms.axiom__betweennesssymmetry G K H H2).
---------- assert (* Cut *) (euclidean__defs.Out H K G) as H21.
----------- apply (@lemma__ray4.lemma__ray4 H K G).
------------right.
right.
exact H20.

------------ exact H11.
----------- assert (* Cut *) (euclidean__defs.Out H G K) as H22.
------------ apply (@lemma__ray5.lemma__ray5 H K G H21).
------------ assert (* Cut *) (F = F) as H23.
------------- apply (@logic.eq__refl Point F).
------------- assert (* Cut *) (euclidean__axioms.neq H F) as H24.
-------------- assert (* Cut *) ((euclidean__axioms.neq H F) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E F))) as H24.
--------------- apply (@lemma__betweennotequal.lemma__betweennotequal E H F H4).
--------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H25.
-------------- assert (* Cut *) (euclidean__defs.Out H F F) as H25.
--------------- apply (@lemma__ray4.lemma__ray4 H F F).
----------------right.
left.
exact H23.

---------------- exact H24.
--------------- assert (* Cut *) (euclidean__defs.CongA A G H K H F) as H26.
---------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper A G H G H F K F H17 H22 H25).
---------------- assert (* Cut *) (euclidean__defs.CongA K H F A G H) as H27.
----------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A G H K H F H26).
----------------- assert (* Cut *) (euclidean__defs.CongA C K H A G H) as H28.
------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive C K H K H F A G H H19 H27).
------------------ assert (* Cut *) (euclidean__axioms.neq G H) as H29.
------------------- assert (* Cut *) ((euclidean__axioms.neq K G) /\ ((euclidean__axioms.neq H K) /\ (euclidean__axioms.neq H G))) as H29.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H K G H20).
-------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H8.
------------------- assert (* Cut *) (euclidean__defs.Out G H K) as H30.
-------------------- apply (@lemma__ray4.lemma__ray4 G H K).
---------------------left.
exact H2.

--------------------- exact H29.
-------------------- assert (* Cut *) (euclidean__axioms.neq A G) as H31.
--------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A B))) as H31.
---------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A G B H3).
---------------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H34.
--------------------- assert (* Cut *) (euclidean__axioms.neq G A) as H32.
---------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A G H31).
---------------------- assert (* Cut *) (A = A) as H33.
----------------------- apply (@logic.eq__refl Point A).
----------------------- assert (* Cut *) (euclidean__defs.Out G A A) as H34.
------------------------ apply (@lemma__ray4.lemma__ray4 G A A).
-------------------------right.
left.
exact H33.

------------------------- exact H32.
------------------------ assert (* Cut *) (euclidean__defs.CongA C K H A G K) as H35.
------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper C K H A G H A K H28 H34 H30).
------------------------- assert (* Cut *) (euclidean__defs.CongA H K C K G A) as H36.
-------------------------- apply (@lemma__equalanglesflip.lemma__equalanglesflip C K H A G K H35).
-------------------------- assert (exists M, (euclidean__axioms.BetS A M F) /\ ((euclidean__axioms.Col G H M) /\ (euclidean__axioms.nCol G H A))) as H37 by exact H6.
destruct H37 as [M H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
assert (exists m, (euclidean__axioms.BetS C m F) /\ ((euclidean__axioms.Col K H m) /\ (euclidean__axioms.nCol K H C))) as H43 by exact H7.
destruct H43 as [m H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
assert (* Cut *) (euclidean__axioms.Col G K H) as H49.
--------------------------- right.
right.
right.
right.
left.
exact H2.
--------------------------- assert (* Cut *) (euclidean__axioms.Col H G K) as H50.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col K G H) /\ ((euclidean__axioms.Col K H G) /\ ((euclidean__axioms.Col H G K) /\ ((euclidean__axioms.Col G H K) /\ (euclidean__axioms.Col H K G))))) as H50.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder G K H H49).
----------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H55.
---------------------------- assert (* Cut *) (euclidean__axioms.Col H G M) as H51.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col H G M) /\ ((euclidean__axioms.Col H M G) /\ ((euclidean__axioms.Col M G H) /\ ((euclidean__axioms.Col G M H) /\ (euclidean__axioms.Col M H G))))) as H51.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder G H M H41).
------------------------------ destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H52.
----------------------------- assert (* Cut *) (euclidean__axioms.neq H G) as H52.
------------------------------ assert (* Cut *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C F))) as H52.
------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C m F H45).
------------------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H9.
------------------------------ assert (* Cut *) (euclidean__axioms.Col G K M) as H53.
------------------------------- apply (@euclidean__tactics.not__nCol__Col G K M).
--------------------------------intro H53.
apply (@euclidean__tactics.Col__nCol__False G K M H53).
---------------------------------apply (@lemma__collinear4.lemma__collinear4 H G K M H50 H51 H52).


------------------------------- assert (* Cut *) (euclidean__axioms.Col K G M) as H54.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col K G M) /\ ((euclidean__axioms.Col K M G) /\ ((euclidean__axioms.Col M G K) /\ ((euclidean__axioms.Col G M K) /\ (euclidean__axioms.Col M K G))))) as H54.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G K M H53).
--------------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H55.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col H K m) as H55.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col H K m) /\ ((euclidean__axioms.Col H m K) /\ ((euclidean__axioms.Col m K H) /\ ((euclidean__axioms.Col K m H) /\ (euclidean__axioms.Col m H K))))) as H55.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder K H m H47).
---------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H56.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col H K G) as H56.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col G H K) /\ ((euclidean__axioms.Col G K H) /\ ((euclidean__axioms.Col K H G) /\ ((euclidean__axioms.Col H K G) /\ (euclidean__axioms.Col K G H))))) as H56.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H G K H50).
----------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H63.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq H K) as H57.
----------------------------------- assert (* Cut *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C F))) as H57.
------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal C m F H45).
------------------------------------ destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H11.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col K m G) as H58.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col K m G).
-------------------------------------intro H58.
apply (@euclidean__tactics.Col__nCol__False K m G H58).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 H K m G H55 H56 H57).


------------------------------------ assert (* Cut *) (euclidean__axioms.Col K G m) as H59.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m K G) /\ ((euclidean__axioms.Col m G K) /\ ((euclidean__axioms.Col G K m) /\ ((euclidean__axioms.Col K G m) /\ (euclidean__axioms.Col G m K))))) as H59.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder K m G H58).
-------------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H66.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H K) as H60.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K H G) /\ ((euclidean__axioms.Col K G H) /\ ((euclidean__axioms.Col G H K) /\ ((euclidean__axioms.Col H G K) /\ (euclidean__axioms.Col G K H))))) as H60.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H K G H56).
--------------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H65.
-------------------------------------- assert (* Cut *) (G = G) as H61.
--------------------------------------- apply (@logic.eq__refl Point G).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col G H G) as H62.
---------------------------------------- right.
left.
exact H61.
---------------------------------------- assert (* Cut *) (euclidean__axioms.neq G K) as H63.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.neq K H) /\ ((euclidean__axioms.neq G K) /\ (euclidean__axioms.neq G H))) as H63.
------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal G K H H2).
------------------------------------------ destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H66.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol G K A) as H64.
------------------------------------------ apply (@euclidean__tactics.nCol__notCol G K A).
-------------------------------------------apply (@euclidean__tactics.nCol__not__Col G K A).
--------------------------------------------apply (@lemma__NChelper.lemma__NChelper G H A G K H42 H62 H60 H63).


------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol K G A) as H65.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol K G A) /\ ((euclidean__axioms.nCol K A G) /\ ((euclidean__axioms.nCol A G K) /\ ((euclidean__axioms.nCol G A K) /\ (euclidean__axioms.nCol A K G))))) as H65.
-------------------------------------------- apply (@lemma__NCorder.lemma__NCorder G K A H64).
-------------------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H66.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K H G) as H66.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H G K) /\ ((euclidean__axioms.Col H K G) /\ ((euclidean__axioms.Col K G H) /\ ((euclidean__axioms.Col G K H) /\ (euclidean__axioms.Col K H G))))) as H66.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G H K H60).
--------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H74.
-------------------------------------------- assert (* Cut *) (K = K) as H67.
--------------------------------------------- apply (@logic.eq__refl Point K).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K H K) as H68.
---------------------------------------------- right.
left.
exact H67.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G K) as H69.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m F) /\ ((euclidean__axioms.neq C m) /\ (euclidean__axioms.neq C F))) as H69.
------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal C m F H45).
------------------------------------------------ destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H63.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq K G) as H70.
------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G K H69).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol K G C) as H71.
------------------------------------------------- apply (@euclidean__tactics.nCol__notCol K G C).
--------------------------------------------------apply (@euclidean__tactics.nCol__not__Col K G C).
---------------------------------------------------apply (@lemma__NChelper.lemma__NChelper K H C K G H48 H68 H66 H70).


------------------------------------------------- assert (* Cut *) (euclidean__defs.OS A C K G) as H72.
-------------------------------------------------- exists F.
exists M.
exists m.
split.
--------------------------------------------------- exact H54.
--------------------------------------------------- split.
---------------------------------------------------- exact H59.
---------------------------------------------------- split.
----------------------------------------------------- exact H39.
----------------------------------------------------- split.
------------------------------------------------------ exact H45.
------------------------------------------------------ split.
------------------------------------------------------- exact H65.
------------------------------------------------------- exact H71.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.OS C A K G) as H73.
--------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS C A K G) /\ ((euclidean__defs.OS A C G K) /\ (euclidean__defs.OS C A G K))) as H73.
---------------------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric K G A C H72).
---------------------------------------------------- destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H74.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D K C) as H74.
---------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C K D H5).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B G A) as H75.
----------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A G B H3).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.Par D C B A) as H76.
------------------------------------------------------ apply (@proposition__28A.proposition__28A D C B A H K G H74 H75 H20 H36 H73).
------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par C D A B) as H77.
------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par C D B A) /\ ((euclidean__defs.Par D C A B) /\ (euclidean__defs.Par C D A B))) as H77.
-------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip D C B A H76).
-------------------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
exact H81.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H78.
-------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric C D A B H77).
-------------------------------------------------------- exact H78.
Qed.
