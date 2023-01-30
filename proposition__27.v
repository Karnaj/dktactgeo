Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7b.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angledistinct.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__angletrichotomy.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__planeseparation.
Require Export lemma__ray1.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__samesidesymmetric.
Require Export lemma__supplements.
Require Export logic.
Require Export proposition__16.
Definition proposition__27 : forall A B C D E F, (euclidean__axioms.BetS A E B) -> ((euclidean__axioms.BetS C F D) -> ((euclidean__defs.CongA A E F E F D) -> ((euclidean__axioms.TS A E F D) -> (euclidean__defs.Par A B C D)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.neq A B) as H3.
- assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H3.
-- apply (@lemma__betweennotequal.lemma__betweennotequal A E B H).
-- destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
exact H7.
- assert (* Cut *) (euclidean__axioms.neq C D) as H4.
-- assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H4.
--- apply (@lemma__betweennotequal.lemma__betweennotequal C F D H0).
--- destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
exact H8.
-- assert (exists H5, (euclidean__axioms.BetS A H5 D) /\ ((euclidean__axioms.Col E F H5) /\ (euclidean__axioms.nCol E F A))) as H5 by exact H2.
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
assert (* Cut *) (euclidean__axioms.Col A E B) as H12.
--- right.
right.
right.
right.
left.
exact H.
--- assert (* Cut *) (euclidean__axioms.neq A E) as H13.
---- assert (* Cut *) ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq A E) /\ (euclidean__axioms.neq A B))) as H13.
----- apply (@lemma__betweennotequal.lemma__betweennotequal A E B H).
----- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H16.
---- assert (* Cut *) (euclidean__axioms.Col C F D) as H14.
----- right.
right.
right.
right.
left.
exact H0.
----- assert (* Cut *) (euclidean__axioms.neq F D) as H15.
------ assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H15.
------- apply (@lemma__betweennotequal.lemma__betweennotequal C F D H0).
------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H16.
------ assert (* Cut *) (euclidean__defs.CongA E F D A E F) as H16.
------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A E F E F D H1).
------- assert (* Cut *) (euclidean__axioms.nCol E F D) as H17.
-------- assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H17 by exact H16.
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp by exact H17.
destruct __TmpHyp as [x H18].
destruct H18 as [x0 H19].
destruct H19 as [x1 H20].
destruct H20 as [x2 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
assert (exists U V u v, (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as H36 by exact H1.
assert (exists U V u v, (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as __TmpHyp0 by exact H36.
destruct __TmpHyp0 as [x3 H37].
destruct H37 as [x4 H38].
destruct H38 as [x5 H39].
destruct H39 as [x6 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H35.
-------- assert (* Cut *) (euclidean__axioms.neq E F) as H18.
--------- assert (* Cut *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq E D) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq A F)))))) as H18.
---------- apply (@lemma__angledistinct.lemma__angledistinct E F D A E F H16).
---------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H27.
--------- assert (* Cut *) (euclidean__axioms.neq F E) as H19.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E F H18).
---------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H20.
----------- intro H20.
assert (exists G, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B G) /\ (euclidean__axioms.Col C D G)))) as H21 by exact H20.
destruct H21 as [G H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
assert (* Cut *) (euclidean__axioms.Col B A G) as H29.
------------ assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H29.
------------- apply (@lemma__collinearorder.lemma__collinearorder A B G H27).
------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H30.
------------ assert (* Cut *) (euclidean__axioms.Col B A E) as H30.
------------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H30.
-------------- apply (@lemma__collinearorder.lemma__collinearorder A E B H12).
-------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H35.
------------- assert (* Cut *) (euclidean__axioms.neq B A) as H31.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H23).
-------------- assert (* Cut *) (euclidean__axioms.Col A G E) as H32.
--------------- apply (@euclidean__tactics.not__nCol__Col A G E).
----------------intro H32.
apply (@euclidean__tactics.Col__nCol__False A G E H32).
-----------------apply (@lemma__collinear4.lemma__collinear4 B A G E H29 H30 H31).


--------------- assert (* Cut *) (euclidean__axioms.Col A E G) as H33.
---------------- assert (* Cut *) ((euclidean__axioms.Col G A E) /\ ((euclidean__axioms.Col G E A) /\ ((euclidean__axioms.Col E A G) /\ ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A))))) as H33.
----------------- apply (@lemma__collinearorder.lemma__collinearorder A G E H32).
----------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H40.
---------------- assert (* Cut *) (F = F) as H34.
----------------- apply (@logic.eq__refl Point F).
----------------- assert (* Cut *) (euclidean__defs.Out E F F) as H35.
------------------ apply (@lemma__ray4.lemma__ray4 E F F).
-------------------right.
left.
exact H34.

------------------- exact H18.
------------------ assert (* Cut *) (euclidean__defs.Supp A E F F B) as H36.
------------------- split.
-------------------- exact H35.
-------------------- exact H.
------------------- assert (* Cut *) (E = E) as H37.
-------------------- apply (@logic.eq__refl Point E).
-------------------- assert (* Cut *) (euclidean__defs.Out F E E) as H38.
--------------------- apply (@lemma__ray4.lemma__ray4 F E E).
----------------------right.
left.
exact H37.

---------------------- exact H19.
--------------------- assert (* Cut *) (euclidean__axioms.BetS D F C) as H39.
---------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C F D H0).
---------------------- assert (* Cut *) (euclidean__defs.Supp D F E E C) as H40.
----------------------- split.
------------------------ exact H38.
------------------------ exact H39.
----------------------- assert (* Cut *) (euclidean__defs.CongA E F D D F E) as H41.
------------------------ apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA E F D H17).
------------------------ assert (* Cut *) (euclidean__defs.CongA A E F D F E) as H42.
------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A E F E F D D F E H1 H41).
------------------------- assert (* Cut *) (euclidean__defs.CongA F E B E F C) as H43.
-------------------------- apply (@lemma__supplements.lemma__supplements A E F F B D F E E C H42 H36 H40).
-------------------------- assert (* Cut *) (euclidean__defs.CongA B E F C F E) as H44.
--------------------------- apply (@lemma__equalanglesflip.lemma__equalanglesflip F E B E F C H43).
--------------------------- assert (* Cut *) (~(euclidean__axioms.BetS A E G)) as H45.
---------------------------- intro H45.
assert (E = E) as H46 by exact H37.
assert (* Cut *) (euclidean__axioms.Col E F E) as H47.
----------------------------- right.
left.
exact H46.
----------------------------- assert (* Cut *) (euclidean__axioms.BetS G E A) as H48.
------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry A E G H45).
------------------------------ assert (euclidean__axioms.Col C F D) as H49 by exact H14.
assert (* Cut *) (euclidean__axioms.Col C D F) as H50.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H50.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C F D H49).
-------------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H57.
------------------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H51.
-------------------------------- assert (* Cut *) ((euclidean__axioms.neq E A) /\ ((euclidean__axioms.neq G E) /\ (euclidean__axioms.neq G A))) as H51.
--------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal G E A H48).
--------------------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H25.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col D G F) as H52.
--------------------------------- apply (@euclidean__tactics.not__nCol__Col D G F).
----------------------------------intro H52.
apply (@euclidean__tactics.Col__nCol__False D G F H52).
-----------------------------------apply (@lemma__collinear4.lemma__collinear4 C D G F H28 H50 H51).


--------------------------------- assert (* Cut *) (euclidean__axioms.Col G F D) as H53.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col G D F) /\ ((euclidean__axioms.Col G F D) /\ ((euclidean__axioms.Col F D G) /\ ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D))))) as H53.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D G F H52).
----------------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H56.
---------------------------------- assert (* Cut *) (~(F = G)) as H54.
----------------------------------- intro H54.
assert (* Cut *) (euclidean__axioms.Col A E F) as H55.
------------------------------------ apply (@eq__ind__r euclidean__axioms.Point G (fun F0 => (euclidean__axioms.BetS C F0 D) -> ((euclidean__defs.CongA A E F0 E F0 D) -> ((euclidean__axioms.TS A E F0 D) -> ((euclidean__axioms.Col E F0 H6) -> ((euclidean__axioms.nCol E F0 A) -> ((euclidean__axioms.Col C F0 D) -> ((euclidean__axioms.neq F0 D) -> ((euclidean__defs.CongA E F0 D A E F0) -> ((euclidean__axioms.nCol E F0 D) -> ((euclidean__axioms.neq E F0) -> ((euclidean__axioms.neq F0 E) -> ((F0 = F0) -> ((euclidean__defs.Out E F0 F0) -> ((euclidean__defs.Supp A E F0 F0 B) -> ((euclidean__defs.Out F0 E E) -> ((euclidean__axioms.BetS D F0 C) -> ((euclidean__defs.Supp D F0 E E C) -> ((euclidean__defs.CongA E F0 D D F0 E) -> ((euclidean__defs.CongA A E F0 D F0 E) -> ((euclidean__defs.CongA F0 E B E F0 C) -> ((euclidean__defs.CongA B E F0 C F0 E) -> ((euclidean__axioms.Col E F0 E) -> ((euclidean__axioms.Col C F0 D) -> ((euclidean__axioms.Col C D F0) -> ((euclidean__axioms.Col D G F0) -> ((euclidean__axioms.Col G F0 D) -> (euclidean__axioms.Col A E F0)))))))))))))))))))))))))))) with (x := F).
-------------------------------------intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
exact H33.

------------------------------------- exact H54.
------------------------------------- exact H0.
------------------------------------- exact H1.
------------------------------------- exact H2.
------------------------------------- exact H10.
------------------------------------- exact H11.
------------------------------------- exact H14.
------------------------------------- exact H15.
------------------------------------- exact H16.
------------------------------------- exact H17.
------------------------------------- exact H18.
------------------------------------- exact H19.
------------------------------------- exact H34.
------------------------------------- exact H35.
------------------------------------- exact H36.
------------------------------------- exact H38.
------------------------------------- exact H39.
------------------------------------- exact H40.
------------------------------------- exact H41.
------------------------------------- exact H42.
------------------------------------- exact H43.
------------------------------------- exact H44.
------------------------------------- exact H47.
------------------------------------- exact H49.
------------------------------------- exact H50.
------------------------------------- exact H52.
------------------------------------- exact H53.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col E F A) as H56.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col A F E) /\ (euclidean__axioms.Col F E A))))) as H56.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A E F H55).
-------------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H59.
------------------------------------- apply (@euclidean__tactics.Col__nCol__False E F D H17).
--------------------------------------apply (@euclidean__tactics.not__nCol__Col E F D).
---------------------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False E F A H11 H56).


----------------------------------- assert (* Cut *) (euclidean__axioms.neq G F) as H55.
------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric F G H54).
------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col E F G)) as H56.
------------------------------------- intro H56.
assert (* Cut *) (euclidean__axioms.Col G F E) as H57.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))))) as H57.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E F G H56).
--------------------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H65.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col F E D) as H58.
--------------------------------------- apply (@euclidean__tactics.not__nCol__Col F E D).
----------------------------------------intro H58.
apply (@euclidean__tactics.Col__nCol__False F E D H58).
-----------------------------------------apply (@lemma__collinear4.lemma__collinear4 G F E D H57 H53 H55).


--------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F D) as H59.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col F D E) /\ (euclidean__axioms.Col D E F))))) as H59.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F E D H58).
----------------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H60.
---------------------------------------- apply (@euclidean__tactics.Col__nCol__False E F D H17 H59).
------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D H6 A) as H57.
-------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A H6 D H8).
-------------------------------------- assert (* Cut *) (euclidean__defs.OS D G E F) as H58.
--------------------------------------- exists A.
exists H6.
exists E.
split.
---------------------------------------- exact H10.
---------------------------------------- split.
----------------------------------------- exact H47.
----------------------------------------- split.
------------------------------------------ exact H57.
------------------------------------------ split.
------------------------------------------- exact H48.
------------------------------------------- split.
-------------------------------------------- exact H17.
-------------------------------------------- apply (@euclidean__tactics.nCol__notCol E F G H56).
--------------------------------------- assert (* Cut *) (euclidean__defs.OS G D E F) as H59.
---------------------------------------- assert (* Cut *) ((euclidean__defs.OS G D E F) /\ ((euclidean__defs.OS D G F E) /\ (euclidean__defs.OS G D F E))) as H59.
----------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric E F D G H58).
----------------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H60.
---------------------------------------- assert (F = F) as H60 by exact H34.
assert (* Cut *) (euclidean__axioms.Col E F F) as H61.
----------------------------------------- right.
right.
left.
exact H60.
----------------------------------------- assert (euclidean__axioms.BetS D F C) as H62 by exact H39.
assert (* Cut *) (euclidean__axioms.TS D E F C) as H63.
------------------------------------------ exists F.
split.
------------------------------------------- exact H62.
------------------------------------------- split.
-------------------------------------------- exact H61.
-------------------------------------------- exact H17.
------------------------------------------ assert (* Cut *) (euclidean__axioms.TS G E F C) as H64.
------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation E F G D C H59 H63).
------------------------------------------- assert (exists R, (euclidean__axioms.BetS G R C) /\ ((euclidean__axioms.Col E F R) /\ (euclidean__axioms.nCol E F G))) as H65 by exact H64.
destruct H65 as [R H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
assert (* Cut *) (~(euclidean__axioms.neq F R)) as H71.
-------------------------------------------- intro H71.
assert (* Cut *) (euclidean__axioms.Col G R C) as H72.
--------------------------------------------- right.
right.
right.
right.
left.
exact H67.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G D) as H73.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C))))) as H73.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D G H28).
----------------------------------------------- destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
exact H80.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G R) as H74.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col R G C) /\ ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C G R) /\ ((euclidean__axioms.Col G C R) /\ (euclidean__axioms.Col C R G))))) as H74.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder G R C H72).
------------------------------------------------ destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H79.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G C) as H75.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq R C) /\ ((euclidean__axioms.neq G R) /\ (euclidean__axioms.neq G C))) as H75.
------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal G R C H67).
------------------------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H79.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq C G) as H76.
------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G C H75).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G C R) as H77.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G C R) /\ ((euclidean__axioms.Col G R C) /\ ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C))))) as H77.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C G R H74).
--------------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H78.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G C D) as H78.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col C D G) /\ (euclidean__axioms.Col D G C))))) as H78.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C G D H73).
---------------------------------------------------- destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
exact H79.
--------------------------------------------------- assert (euclidean__axioms.neq G C) as H79 by exact H75.
assert (* Cut *) (euclidean__axioms.neq R F) as H80.
---------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric F R H71).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G R) as H81.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C G D) /\ ((euclidean__axioms.Col C D G) /\ ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G D C) /\ (euclidean__axioms.Col D C G))))) as H81.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder G C D H78).
------------------------------------------------------ destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H74.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D F) as H82.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col G C R) /\ ((euclidean__axioms.Col G R C) /\ ((euclidean__axioms.Col R C G) /\ ((euclidean__axioms.Col C R G) /\ (euclidean__axioms.Col R G C))))) as H82.
------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C G R H81).
------------------------------------------------------- destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H50.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D F G) as H83.
------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col D F G).
--------------------------------------------------------intro H83.
apply (@euclidean__tactics.Col__nCol__False D F G H83).
---------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 C D F G H82 H28 H51).


------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D F C) as H84.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))))) as H84.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D F H82).
--------------------------------------------------------- destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
exact H87.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F D) as H85.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq R C) /\ ((euclidean__axioms.neq G R) /\ (euclidean__axioms.neq G C))) as H85.
---------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal G R C H67).
---------------------------------------------------------- destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H15.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D F) as H86.
---------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric F D H85).
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F G C) as H87.
----------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col F G C).
------------------------------------------------------------intro H87.
apply (@euclidean__tactics.Col__nCol__False F G C H87).
-------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D F G C H83 H84 H86).


----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G F) as H88.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C F G) /\ ((euclidean__axioms.Col F C G) /\ (euclidean__axioms.Col C G F))))) as H88.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F G C H87).
------------------------------------------------------------- destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H96.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C G D) as H89.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C))))) as H89.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C G F H88).
-------------------------------------------------------------- destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
exact H73.
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col R F D) as H90.
-------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col R F D).
---------------------------------------------------------------intro H90.
apply (@euclidean__tactics.Col__nCol__False R F D H90).
----------------------------------------------------------------apply (@lemma__collinear5.lemma__collinear5 C G R F D H76 H81 H88 H89).


-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col R F E) as H91.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E R) /\ ((euclidean__axioms.Col F R E) /\ ((euclidean__axioms.Col R E F) /\ ((euclidean__axioms.Col E R F) /\ (euclidean__axioms.Col R F E))))) as H91.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E F R H69).
---------------------------------------------------------------- destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
exact H99.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F D E) as H92.
---------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col F D E).
-----------------------------------------------------------------intro H92.
apply (@euclidean__tactics.Col__nCol__False F D E H92).
------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 R F D E H90 H91 H80).


---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F D) as H93.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))))) as H93.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder F D E H92).
------------------------------------------------------------------ destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
exact H98.
----------------------------------------------------------------- apply (@H56).
------------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col E F G).
-------------------------------------------------------------------intro H94.
apply (@euclidean__tactics.Col__nCol__False E F D H17 H93).


-------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS G F C) as H72.
--------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point R (fun X => euclidean__axioms.BetS G X C)) with (x := F).
---------------------------------------------- exact H67.
----------------------------------------------apply (@euclidean__tactics.NNPP (F = R) H71).

--------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col E G F)) as H73.
---------------------------------------------- intro H73.
assert (* Cut *) (euclidean__axioms.Col E F G) as H74.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col G F E) /\ ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E))))) as H74.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder E G F H73).
------------------------------------------------ destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H81.
----------------------------------------------- apply (@H56 H74).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle E G F) as H74.
----------------------------------------------- apply (@euclidean__tactics.nCol__notCol E G F H73).
----------------------------------------------- assert (* Cut *) (euclidean__defs.LtA G E F E F C) as H75.
------------------------------------------------ assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA B0 A0 C0 A0 C0 D0))) as H75.
------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
-------------------------------------------------- apply (@proposition__16.proposition__16 A0 B0 C0 D0 __ __0).
-------------------------------------------------- destruct __1 as [__1 __2].
exact __1.
------------------------------------------------- apply (@H75 E G F C H74 H72).
------------------------------------------------ assert (* Cut *) (euclidean__defs.LtA G E F F E B) as H76.
------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence G E F E F C F E B H75 H43).
------------------------------------------------- assert (F = F) as H77 by exact H60.
assert (euclidean__defs.Out E F F) as H78 by exact H35.
assert (* Cut *) (euclidean__defs.Out E G B) as H79.
-------------------------------------------------- exists A.
split.
--------------------------------------------------- exact H.
--------------------------------------------------- exact H45.
-------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col G E F)) as H80.
--------------------------------------------------- intro H80.
assert (* Cut *) (euclidean__axioms.Col E G F) as H81.
---------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E G F) /\ ((euclidean__axioms.Col E F G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G F E) /\ (euclidean__axioms.Col F E G))))) as H81.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G E F H80).
----------------------------------------------------- destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H82.
---------------------------------------------------- apply (@H56).
-----------------------------------------------------apply (@euclidean__tactics.not__nCol__Col E F G).
------------------------------------------------------intro H82.
apply (@H73 H81).


--------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G E F G E F) as H81.
---------------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive G E F).
-----------------------------------------------------apply (@euclidean__tactics.nCol__notCol G E F H80).

---------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G E F B E F) as H82.
----------------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper G E F G E F B F H81 H79 H78).
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E F) as H83.
------------------------------------------------------ assert (exists U V u v, (euclidean__defs.Out E G U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E B u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol G E F)))))))) as H83 by exact H82.
assert (exists U V u v, (euclidean__defs.Out E G U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E B u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol G E F)))))))) as __TmpHyp by exact H83.
destruct __TmpHyp as [x H84].
destruct H84 as [x0 H85].
destruct H85 as [x1 H86].
destruct H86 as [x2 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
assert (exists U V u v, (euclidean__defs.Out E G U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol G E F)))))))) as H102 by exact H81.
assert (exists U V u v, (euclidean__defs.Out E G U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol G E F)))))))) as __TmpHyp0 by exact H102.
destruct __TmpHyp0 as [x3 H103].
destruct H103 as [x4 H104].
destruct H104 as [x5 H105].
destruct H105 as [x6 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
assert (exists U V u v, (euclidean__defs.Out E B U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B E F)))))))) as H121 by exact H44.
assert (exists U V u v, (euclidean__defs.Out E B U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B E F)))))))) as __TmpHyp1 by exact H121.
destruct __TmpHyp1 as [x7 H122].
destruct H122 as [x8 H123].
destruct H123 as [x9 H124].
destruct H124 as [x10 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
assert (exists U V u v, (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E B)))))))) as H140 by exact H43.
assert (exists U V u v, (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E B)))))))) as __TmpHyp2 by exact H140.
destruct __TmpHyp2 as [x11 H141].
destruct H141 as [x12 H142].
destruct H142 as [x13 H143].
destruct H143 as [x14 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
assert (exists U V u v, (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as H159 by exact H42.
assert (exists U V u v, (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as __TmpHyp3 by exact H159.
destruct __TmpHyp3 as [x15 H160].
destruct H160 as [x16 H161].
destruct H161 as [x17 H162].
destruct H162 as [x18 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F U F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H178 by exact H41.
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F U F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp4 by exact H178.
destruct __TmpHyp4 as [x19 H179].
destruct H179 as [x20 H180].
destruct H180 as [x21 H181].
destruct H181 as [x22 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H197 by exact H16.
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp5 by exact H197.
destruct __TmpHyp5 as [x23 H198].
destruct H198 as [x24 H199].
destruct H199 as [x25 H200].
destruct H200 as [x26 H201].
destruct H201 as [H202 H203].
destruct H203 as [H204 H205].
destruct H205 as [H206 H207].
destruct H207 as [H208 H209].
destruct H209 as [H210 H211].
destruct H211 as [H212 H213].
destruct H213 as [H214 H215].
assert (exists U V u v, (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as H216 by exact H1.
assert (exists U V u v, (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as __TmpHyp6 by exact H216.
destruct __TmpHyp6 as [x27 H217].
destruct H217 as [x28 H218].
destruct H218 as [x29 H219].
destruct H219 as [x30 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
destruct H232 as [H233 H234].
exact H139.
------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA B E F F E B) as H84.
------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B E F H83).
------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G E F F E B) as H85.
-------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive G E F B E F F E B H82 H84).
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F E B G E F) as H86.
--------------------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric G E F F E B H85).
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA F E B F E B) as H87.
---------------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 G E F F E B F E B H76 H86).
---------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.LtA F E B F E B)) as H88.
----------------------------------------------------------- apply (@lemma__angletrichotomy.lemma__angletrichotomy F E B F E B H87).
----------------------------------------------------------- apply (@H56).
------------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col E F G).
-------------------------------------------------------------intro H89.
apply (@H88 H87).


---------------------------- assert (* Cut *) (~(euclidean__defs.Out E A G)) as H46.
----------------------------- intro H46.
assert (F = F) as H47 by exact H34.
assert (euclidean__defs.Out E F F) as H48 by exact H35.
assert (* Cut *) (euclidean__defs.Out E G A) as H49.
------------------------------ apply (@lemma__ray5.lemma__ray5 E A G H46).
------------------------------ assert (euclidean__defs.CongA E F D A E F) as H50 by exact H16.
assert (* Cut *) (euclidean__defs.CongA E F D G E F) as H51.
------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper E F D A E F G F H50 H46 H48).
------------------------------- assert (* Cut *) (euclidean__axioms.BetS B E A) as H52.
-------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A E B H).
-------------------------------- assert (* Cut *) ((euclidean__axioms.BetS E A G) \/ ((G = A) \/ (euclidean__axioms.BetS E G A))) as H53.
--------------------------------- apply (@lemma__ray1.lemma__ray1 E G A H49).
--------------------------------- assert (* Cut *) (euclidean__axioms.BetS B E G) as H54.
---------------------------------- assert ((euclidean__axioms.BetS E A G) \/ ((G = A) \/ (euclidean__axioms.BetS E G A))) as H54 by exact H53.
assert ((euclidean__axioms.BetS E A G) \/ ((G = A) \/ (euclidean__axioms.BetS E G A))) as __TmpHyp by exact H54.
destruct __TmpHyp as [H55|H55].
----------------------------------- assert (* Cut *) (euclidean__axioms.BetS B E G) as H56.
------------------------------------ apply (@lemma__3__7b.lemma__3__7b B E A G H52 H55).
------------------------------------ exact H56.
----------------------------------- destruct H55 as [H56|H56].
------------------------------------ assert (* Cut *) (euclidean__axioms.BetS B E G) as H57.
------------------------------------- apply (@eq__ind__r euclidean__axioms.Point A (fun G0 => (euclidean__axioms.Col A B G0) -> ((euclidean__axioms.Col C D G0) -> ((euclidean__axioms.Col B A G0) -> ((euclidean__axioms.Col A G0 E) -> ((euclidean__axioms.Col A E G0) -> ((~(euclidean__axioms.BetS A E G0)) -> ((euclidean__defs.Out E A G0) -> ((euclidean__defs.Out E G0 A) -> ((euclidean__defs.CongA E F D G0 E F) -> (euclidean__axioms.BetS B E G0))))))))))) with (x := G).
--------------------------------------intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
exact H52.

-------------------------------------- exact H56.
-------------------------------------- exact H27.
-------------------------------------- exact H28.
-------------------------------------- exact H29.
-------------------------------------- exact H32.
-------------------------------------- exact H33.
-------------------------------------- exact H45.
-------------------------------------- exact H46.
-------------------------------------- exact H49.
-------------------------------------- exact H51.
------------------------------------- exact H57.
------------------------------------ assert (* Cut *) (euclidean__axioms.BetS B E G) as H57.
------------------------------------- apply (@euclidean__axioms.axiom__innertransitivity B E G A H52 H56).
------------------------------------- exact H57.
---------------------------------- assert (* Cut *) (euclidean__axioms.BetS G E B) as H55.
----------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B E G H54).
----------------------------------- assert (E = E) as H56 by exact H37.
assert (* Cut *) (euclidean__axioms.Col E F E) as H57.
------------------------------------ right.
left.
exact H56.
------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col E F G)) as H58.
------------------------------------- intro H58.
assert (* Cut *) (euclidean__axioms.Col B A G) as H59.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))))) as H59.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E F G H58).
--------------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H29.
-------------------------------------- assert (euclidean__axioms.Col A E B) as H60 by exact H12.
assert (* Cut *) (euclidean__axioms.Col B A E) as H61.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H61.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A E B H60).
---------------------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H66.
--------------------------------------- assert (euclidean__axioms.Col A G E) as H62 by exact H32.
assert (* Cut *) (euclidean__axioms.Col G E A) as H63.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G A E) /\ ((euclidean__axioms.Col G E A) /\ ((euclidean__axioms.Col E A G) /\ ((euclidean__axioms.Col A E G) /\ (euclidean__axioms.Col E G A))))) as H63.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A G E H62).
----------------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H66.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col G E F) as H64.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col F G E) /\ ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col E G F) /\ (euclidean__axioms.Col G F E))))) as H64.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder E F G H58).
------------------------------------------ destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H69.
----------------------------------------- assert (* Cut *) (euclidean__axioms.neq E G) as H65.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq E G) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B G))) as H65.
------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B E G H54).
------------------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H66.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq G E) as H66.
------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E G H65).
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E A F) as H67.
-------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E A F).
---------------------------------------------intro H67.
apply (@euclidean__tactics.Col__nCol__False E A F H67).
----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 G E A F H63 H64 H66).


-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H68.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E))))) as H68.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E A F H67).
---------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H75.
--------------------------------------------- apply (@euclidean__tactics.Col__nCol__False E F D H17).
----------------------------------------------apply (@euclidean__tactics.not__nCol__Col E F D).
-----------------------------------------------intro H69.
apply (@euclidean__tactics.Col__nCol__False E F A H11 H68).


------------------------------------- assert (* Cut *) (euclidean__defs.OS A G E F) as H59.
-------------------------------------- exists B.
exists E.
exists E.
split.
--------------------------------------- exact H57.
--------------------------------------- split.
---------------------------------------- exact H57.
---------------------------------------- split.
----------------------------------------- exact H.
----------------------------------------- split.
------------------------------------------ exact H55.
------------------------------------------ split.
------------------------------------------- exact H11.
------------------------------------------- apply (@euclidean__tactics.nCol__notCol E F G H58).
-------------------------------------- assert (* Cut *) (euclidean__defs.OS G A E F) as H60.
--------------------------------------- assert (* Cut *) ((euclidean__defs.OS G A E F) /\ ((euclidean__defs.OS A G F E) /\ (euclidean__defs.OS G A F E))) as H60.
---------------------------------------- apply (@lemma__samesidesymmetric.lemma__samesidesymmetric E F A G H59).
---------------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H61.
--------------------------------------- assert (* Cut *) (euclidean__axioms.TS G E F D) as H61.
---------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation E F G A D H60 H2).
---------------------------------------- assert (exists P, (euclidean__axioms.BetS G P D) /\ ((euclidean__axioms.Col E F P) /\ (euclidean__axioms.nCol E F G))) as H62 by exact H61.
destruct H62 as [P H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
assert (* Cut *) (euclidean__axioms.Col G P D) as H68.
----------------------------------------- right.
right.
right.
right.
left.
exact H64.
----------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq P F)) as H69.
------------------------------------------ intro H69.
assert (* Cut *) (euclidean__axioms.neq G D) as H70.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq P D) /\ ((euclidean__axioms.neq G P) /\ (euclidean__axioms.neq G D))) as H70.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal G P D H64).
-------------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H74.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G D P) as H71.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col P G D) /\ ((euclidean__axioms.Col P D G) /\ ((euclidean__axioms.Col D G P) /\ ((euclidean__axioms.Col G D P) /\ (euclidean__axioms.Col D P G))))) as H71.
--------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G P D H68).
--------------------------------------------- destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H78.
-------------------------------------------- assert (euclidean__axioms.Col C F D) as H72 by exact H14.
assert (* Cut *) (euclidean__axioms.Col C D F) as H73.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H73.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C F D H72).
---------------------------------------------- destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
exact H80.
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D G F) as H74.
---------------------------------------------- apply (@euclidean__tactics.not__nCol__Col D G F).
-----------------------------------------------intro H74.
apply (@euclidean__tactics.Col__nCol__False D G F H74).
------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 C D G F H28 H73 H25).


---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G D F) as H75.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G D F) /\ ((euclidean__axioms.Col G F D) /\ ((euclidean__axioms.Col F D G) /\ ((euclidean__axioms.Col D F G) /\ (euclidean__axioms.Col F G D))))) as H75.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder D G F H74).
------------------------------------------------ destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H76.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D P F) as H76.
------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col D P F).
-------------------------------------------------intro H76.
apply (@euclidean__tactics.Col__nCol__False D P F H76).
--------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 G D P F H71 H75 H70).


------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col P F D) as H77.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col P D F) /\ ((euclidean__axioms.Col P F D) /\ ((euclidean__axioms.Col F D P) /\ ((euclidean__axioms.Col D F P) /\ (euclidean__axioms.Col F P D))))) as H77.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D P F H76).
-------------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H80.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col P F E) as H78.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E P) /\ ((euclidean__axioms.Col F P E) /\ ((euclidean__axioms.Col P E F) /\ ((euclidean__axioms.Col E P F) /\ (euclidean__axioms.Col P F E))))) as H78.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E F P H66).
--------------------------------------------------- destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
exact H86.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F D E) as H79.
--------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col F D E).
----------------------------------------------------intro H79.
apply (@euclidean__tactics.Col__nCol__False F D E H79).
-----------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 P F D E H77 H78 H69).


--------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col F D E)) as H80.
---------------------------------------------------- intro H80.
assert (* Cut *) (euclidean__axioms.Col E F D) as H81.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))))) as H81.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder F D E H80).
------------------------------------------------------ destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H86.
----------------------------------------------------- apply (@H58).
------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col E F G).
-------------------------------------------------------intro H82.
apply (@euclidean__tactics.Col__nCol__False E F D H17 H81).


---------------------------------------------------- apply (@H58).
-----------------------------------------------------apply (@euclidean__tactics.not__nCol__Col E F G).
------------------------------------------------------intro H81.
apply (@H80 H79).


------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS G F D) as H70.
------------------------------------------- apply (@eq__ind euclidean__axioms.Point P (fun X => euclidean__axioms.BetS G X D)) with (y := F).
-------------------------------------------- exact H64.
--------------------------------------------apply (@euclidean__tactics.NNPP (P = F) H69).

------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col F E A)) as H71.
-------------------------------------------- intro H71.
assert (* Cut *) (euclidean__axioms.Col E F A) as H72.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F))))) as H72.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F E A H71).
---------------------------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H73.
--------------------------------------------- apply (@H58).
----------------------------------------------apply (@euclidean__tactics.not__nCol__Col E F G).
-----------------------------------------------intro H73.
apply (@euclidean__tactics.Col__nCol__False E F A H11 H72).


-------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F E A F E A) as H72.
--------------------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive F E A).
----------------------------------------------apply (@euclidean__tactics.nCol__notCol F E A H71).

--------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F E A F E G) as H73.
---------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper F E A F E A F G H72 H48 H46).
---------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F E G F E A) as H74.
----------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric F E A F E G H73).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F E G) as H75.
------------------------------------------------ assert (exists U V u v, (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E G V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E G)))))))) as H75 by exact H74.
assert (exists U V u v, (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E G V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E G)))))))) as __TmpHyp by exact H75.
destruct __TmpHyp as [x H76].
destruct H76 as [x0 H77].
destruct H77 as [x1 H78].
destruct H78 as [x2 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
assert (exists U V u v, (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E G v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E A)))))))) as H94 by exact H73.
assert (exists U V u v, (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E G v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E A)))))))) as __TmpHyp0 by exact H94.
destruct __TmpHyp0 as [x3 H95].
destruct H95 as [x4 H96].
destruct H96 as [x5 H97].
destruct H97 as [x6 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
assert (exists U V u v, (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E A)))))))) as H113 by exact H72.
assert (exists U V u v, (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E A V) /\ ((euclidean__defs.Out E F u) /\ ((euclidean__defs.Out E A v) /\ ((euclidean__axioms.Cong E U E u) /\ ((euclidean__axioms.Cong E V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E A)))))))) as __TmpHyp1 by exact H113.
destruct __TmpHyp1 as [x7 H114].
destruct H114 as [x8 H115].
destruct H115 as [x9 H116].
destruct H116 as [x10 H117].
destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H132 by exact H51.
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E G u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp2 by exact H132.
destruct __TmpHyp2 as [x11 H133].
destruct H133 as [x12 H134].
destruct H134 as [x13 H135].
destruct H135 as [x14 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H151 by exact H50.
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp3 by exact H151.
destruct __TmpHyp3 as [x15 H152].
destruct H152 as [x16 H153].
destruct H153 as [x17 H154].
destruct H154 as [x18 H155].
destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
assert (exists U V u v, (euclidean__defs.Out E B U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B E F)))))))) as H170 by exact H44.
assert (exists U V u v, (euclidean__defs.Out E B U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F C u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol B E F)))))))) as __TmpHyp4 by exact H170.
destruct __TmpHyp4 as [x19 H171].
destruct H171 as [x20 H172].
destruct H172 as [x21 H173].
destruct H173 as [x22 H174].
destruct H174 as [H175 H176].
destruct H176 as [H177 H178].
destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
assert (exists U V u v, (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E B)))))))) as H189 by exact H43.
assert (exists U V u v, (euclidean__defs.Out E F U) /\ ((euclidean__defs.Out E B V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F C v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol F E B)))))))) as __TmpHyp5 by exact H189.
destruct __TmpHyp5 as [x23 H190].
destruct H190 as [x24 H191].
destruct H191 as [x25 H192].
destruct H192 as [x26 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
destruct H199 as [H200 H201].
destruct H201 as [H202 H203].
destruct H203 as [H204 H205].
destruct H205 as [H206 H207].
assert (exists U V u v, (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as H208 by exact H42.
assert (exists U V u v, (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as __TmpHyp6 by exact H208.
destruct __TmpHyp6 as [x27 H209].
destruct H209 as [x28 H210].
destruct H210 as [x29 H211].
destruct H211 as [x30 H212].
destruct H212 as [H213 H214].
destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
destruct H218 as [H219 H220].
destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F U F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H227 by exact H41.
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out F D u) /\ ((euclidean__defs.Out F E v) /\ ((euclidean__axioms.Cong F U F u) /\ ((euclidean__axioms.Cong F V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp7 by exact H227.
destruct __TmpHyp7 as [x31 H228].
destruct H228 as [x32 H229].
destruct H229 as [x33 H230].
destruct H230 as [x34 H231].
destruct H231 as [H232 H233].
destruct H233 as [H234 H235].
destruct H235 as [H236 H237].
destruct H237 as [H238 H239].
destruct H239 as [H240 H241].
destruct H241 as [H242 H243].
destruct H243 as [H244 H245].
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as H246 by exact H16.
assert (exists U V u v, (euclidean__defs.Out F E U) /\ ((euclidean__defs.Out F D V) /\ ((euclidean__defs.Out E A u) /\ ((euclidean__defs.Out E F v) /\ ((euclidean__axioms.Cong F U E u) /\ ((euclidean__axioms.Cong F V E v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol E F D)))))))) as __TmpHyp8 by exact H246.
destruct __TmpHyp8 as [x35 H247].
destruct H247 as [x36 H248].
destruct H248 as [x37 H249].
destruct H249 as [x38 H250].
destruct H250 as [H251 H252].
destruct H252 as [H253 H254].
destruct H254 as [H255 H256].
destruct H256 as [H257 H258].
destruct H258 as [H259 H260].
destruct H260 as [H261 H262].
destruct H262 as [H263 H264].
assert (exists U V u v, (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as H265 by exact H1.
assert (exists U V u v, (euclidean__defs.Out E A U) /\ ((euclidean__defs.Out E F V) /\ ((euclidean__defs.Out F E u) /\ ((euclidean__defs.Out F D v) /\ ((euclidean__axioms.Cong E U F u) /\ ((euclidean__axioms.Cong E V F v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A E F)))))))) as __TmpHyp9 by exact H265.
destruct __TmpHyp9 as [x39 H266].
destruct H266 as [x40 H267].
destruct H267 as [x41 H268].
destruct H268 as [x42 H269].
destruct H269 as [H270 H271].
destruct H271 as [H272 H273].
destruct H273 as [H274 H275].
destruct H275 as [H276 H277].
destruct H277 as [H278 H279].
destruct H279 as [H280 H281].
destruct H281 as [H282 H283].
exact H93.
------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col E G F)) as H76.
------------------------------------------------- intro H76.
assert (* Cut *) (euclidean__axioms.Col F E G) as H77.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G E F) /\ ((euclidean__axioms.Col G F E) /\ ((euclidean__axioms.Col F E G) /\ ((euclidean__axioms.Col E F G) /\ (euclidean__axioms.Col F G E))))) as H77.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E G F H76).
--------------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H82.
-------------------------------------------------- apply (@H58).
---------------------------------------------------apply (@euclidean__tactics.not__nCol__Col E F G).
----------------------------------------------------intro H78.
apply (@euclidean__tactics.Col__nCol__False F E G H75 H77).


------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle E G F) as H77.
-------------------------------------------------- apply (@euclidean__tactics.nCol__notCol E G F H76).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA G E F E F D) as H78.
--------------------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA B0 A0 C0 A0 C0 D0))) as H78.
---------------------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
----------------------------------------------------- apply (@proposition__16.proposition__16 A0 B0 C0 D0 __ __0).
----------------------------------------------------- destruct __1 as [__1 __2].
exact __1.
---------------------------------------------------- apply (@H78 E G F D H77 H70).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA E F D E F D) as H79.
---------------------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 G E F E F D E F D H78 H51).
---------------------------------------------------- assert (* Cut *) (~(euclidean__defs.LtA E F D E F D)) as H80.
----------------------------------------------------- apply (@lemma__angletrichotomy.lemma__angletrichotomy E F D E F D H79).
----------------------------------------------------- apply (@H58).
------------------------------------------------------apply (@euclidean__tactics.not__nCol__Col E F G).
-------------------------------------------------------intro H81.
apply (@H80 H79).


----------------------------- assert ((A = E) \/ ((A = G) \/ ((E = G) \/ ((euclidean__axioms.BetS E A G) \/ ((euclidean__axioms.BetS A E G) \/ (euclidean__axioms.BetS A G E)))))) as H47 by exact H33.
assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H48.
------------------------------ assert ((A = E) \/ ((A = G) \/ ((E = G) \/ ((euclidean__axioms.BetS E A G) \/ ((euclidean__axioms.BetS A E G) \/ (euclidean__axioms.BetS A G E)))))) as H48 by exact H47.
assert ((A = E) \/ ((A = G) \/ ((E = G) \/ ((euclidean__axioms.BetS E A G) \/ ((euclidean__axioms.BetS A E G) \/ (euclidean__axioms.BetS A G E)))))) as __TmpHyp by exact H48.
destruct __TmpHyp as [H49|H49].
------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H50.
-------------------------------- intro H50.
apply (@H13 H49).
-------------------------------- exact H50.
------------------------------- destruct H49 as [H50|H50].
-------------------------------- assert (* Cut *) (~(euclidean__axioms.neq H6 F)) as H51.
--------------------------------- intro H51.
assert (* Cut *) (euclidean__axioms.Col C D F) as H52.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H52.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C F D H14).
----------------------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H59.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col D G F) as H53.
----------------------------------- apply (@euclidean__tactics.not__nCol__Col D G F).
------------------------------------intro H53.
apply (@euclidean__tactics.Col__nCol__False D G F H53).
-------------------------------------apply (@lemma__collinear4.lemma__collinear4 C D G F H28 H52 H25).


----------------------------------- assert (* Cut *) (euclidean__axioms.Col D A F) as H54.
------------------------------------ apply (@eq__ind__r euclidean__axioms.Point G (fun A0 => (euclidean__axioms.BetS A0 E B) -> ((euclidean__defs.CongA A0 E F E F D) -> ((euclidean__axioms.TS A0 E F D) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.BetS A0 H6 D) -> ((euclidean__axioms.nCol E F A0) -> ((euclidean__axioms.Col A0 E B) -> ((euclidean__axioms.neq A0 E) -> ((euclidean__defs.CongA E F D A0 E F) -> ((euclidean__defs.Meet A0 B C D) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Col A0 B G) -> ((euclidean__axioms.Col B A0 G) -> ((euclidean__axioms.Col B A0 E) -> ((euclidean__axioms.neq B A0) -> ((euclidean__axioms.Col A0 G E) -> ((euclidean__axioms.Col A0 E G) -> ((euclidean__defs.Supp A0 E F F B) -> ((euclidean__defs.CongA A0 E F D F E) -> ((~(euclidean__axioms.BetS A0 E G)) -> ((~(euclidean__defs.Out E A0 G)) -> (euclidean__axioms.Col D A0 F))))))))))))))))))))))) with (x := A).
-------------------------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
exact H53.

------------------------------------- exact H50.
------------------------------------- exact H.
------------------------------------- exact H1.
------------------------------------- exact H2.
------------------------------------- exact H3.
------------------------------------- exact H8.
------------------------------------- exact H11.
------------------------------------- exact H12.
------------------------------------- exact H13.
------------------------------------- exact H16.
------------------------------------- exact H20.
------------------------------------- exact H23.
------------------------------------- exact H27.
------------------------------------- exact H29.
------------------------------------- exact H30.
------------------------------------- exact H31.
------------------------------------- exact H32.
------------------------------------- exact H33.
------------------------------------- exact H36.
------------------------------------- exact H42.
------------------------------------- exact H45.
------------------------------------- exact H46.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col A H6 D) as H55.
------------------------------------- right.
right.
right.
right.
left.
exact H8.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col D A H6) as H56.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H6 A D) /\ ((euclidean__axioms.Col H6 D A) /\ ((euclidean__axioms.Col D A H6) /\ ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A))))) as H56.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A H6 D H55).
--------------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H61.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H57.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H57.
---------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A H6 D H8).
---------------------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H61.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq D A) as H58.
---------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A D H57).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col A F H6) as H59.
----------------------------------------- apply (@euclidean__tactics.not__nCol__Col A F H6).
------------------------------------------intro H59.
apply (@euclidean__tactics.Col__nCol__False A F H6 H59).
-------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D A F H6 H54 H56 H58).


----------------------------------------- assert (* Cut *) (euclidean__axioms.Col H6 F A) as H60.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col F A H6) /\ ((euclidean__axioms.Col F H6 A) /\ ((euclidean__axioms.Col H6 A F) /\ ((euclidean__axioms.Col A H6 F) /\ (euclidean__axioms.Col H6 F A))))) as H60.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A F H6 H59).
------------------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H68.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H6 F E) as H61.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E H6) /\ ((euclidean__axioms.Col F H6 E) /\ ((euclidean__axioms.Col H6 E F) /\ ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E))))) as H61.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E F H6 H10).
-------------------------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H69.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F A E) as H62.
-------------------------------------------- apply (@euclidean__tactics.not__nCol__Col F A E).
---------------------------------------------intro H62.
apply (@euclidean__tactics.Col__nCol__False F A E H62).
----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 H6 F A E H60 H61 H51).


-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H63.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H63.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F A E H62).
---------------------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H68.
--------------------------------------------- apply (@euclidean__tactics.Col__nCol__False E F D H17).
----------------------------------------------apply (@euclidean__tactics.not__nCol__Col E F D).
-----------------------------------------------intro H64.
apply (@euclidean__tactics.Col__nCol__False E F A H11 H63).


--------------------------------- assert (* Cut *) (euclidean__axioms.BetS A F D) as H52.
---------------------------------- apply (@eq__ind euclidean__axioms.Point H6 (fun X => euclidean__axioms.BetS A X D)) with (y := F).
----------------------------------- exact H8.
-----------------------------------apply (@euclidean__tactics.NNPP (H6 = F) H51).

---------------------------------- assert (* Cut *) (~(euclidean__axioms.Col E A F)) as H53.
----------------------------------- intro H53.
assert (* Cut *) (euclidean__axioms.Col E F A) as H54.
------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E F A) /\ (euclidean__axioms.Col F A E))))) as H54.
------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E A F H53).
------------------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H61.
------------------------------------ apply (@euclidean__tactics.Col__nCol__False E F D H17).
-------------------------------------apply (@euclidean__tactics.not__nCol__Col E F D).
--------------------------------------intro H55.
apply (@euclidean__tactics.Col__nCol__False E F A H11 H54).


----------------------------------- assert (* Cut *) (euclidean__axioms.Triangle E A F) as H54.
------------------------------------ apply (@euclidean__tactics.nCol__notCol E A F H53).
------------------------------------ assert (* Cut *) (euclidean__defs.LtA A E F E F D) as H55.
------------------------------------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA B0 A0 C0 A0 C0 D0))) as H55.
-------------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
--------------------------------------- apply (@proposition__16.proposition__16 A0 B0 C0 D0 __ __0).
--------------------------------------- destruct __1 as [__1 __2].
exact __1.
-------------------------------------- apply (@H55 E A F D H54 H52).
------------------------------------- assert (* Cut *) (euclidean__defs.CongA E F D A E F) as H56.
-------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun A0 => (euclidean__axioms.BetS A0 E B) -> ((euclidean__defs.CongA A0 E F E F D) -> ((euclidean__axioms.TS A0 E F D) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.BetS A0 H6 D) -> ((euclidean__axioms.nCol E F A0) -> ((euclidean__axioms.Col A0 E B) -> ((euclidean__axioms.neq A0 E) -> ((euclidean__defs.CongA E F D A0 E F) -> ((euclidean__defs.Meet A0 B C D) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Col A0 B G) -> ((euclidean__axioms.Col B A0 G) -> ((euclidean__axioms.Col B A0 E) -> ((euclidean__axioms.neq B A0) -> ((euclidean__axioms.Col A0 G E) -> ((euclidean__axioms.Col A0 E G) -> ((euclidean__defs.Supp A0 E F F B) -> ((euclidean__defs.CongA A0 E F D F E) -> ((~(euclidean__axioms.BetS A0 E G)) -> ((~(euclidean__defs.Out E A0 G)) -> ((euclidean__axioms.BetS A0 F D) -> ((~(euclidean__axioms.Col E A0 F)) -> ((euclidean__axioms.Triangle E A0 F) -> ((euclidean__defs.LtA A0 E F E F D) -> (euclidean__defs.CongA E F D A0 E F))))))))))))))))))))))))))) with (x := A).
---------------------------------------intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
exact H64.

--------------------------------------- exact H50.
--------------------------------------- exact H.
--------------------------------------- exact H1.
--------------------------------------- exact H2.
--------------------------------------- exact H3.
--------------------------------------- exact H8.
--------------------------------------- exact H11.
--------------------------------------- exact H12.
--------------------------------------- exact H13.
--------------------------------------- exact H16.
--------------------------------------- exact H20.
--------------------------------------- exact H23.
--------------------------------------- exact H27.
--------------------------------------- exact H29.
--------------------------------------- exact H30.
--------------------------------------- exact H31.
--------------------------------------- exact H32.
--------------------------------------- exact H33.
--------------------------------------- exact H36.
--------------------------------------- exact H42.
--------------------------------------- exact H45.
--------------------------------------- exact H46.
--------------------------------------- exact H52.
--------------------------------------- exact H53.
--------------------------------------- exact H54.
--------------------------------------- exact H55.
-------------------------------------- assert (* Cut *) (euclidean__defs.LtA E F D E F D) as H57.
--------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 A E F E F D E F D H55 H56).
--------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H58.
---------------------------------------- intro H58.
assert (* Cut *) (~(euclidean__defs.LtA E F D E F D)) as H59.
----------------------------------------- apply (@lemma__angletrichotomy.lemma__angletrichotomy E F D E F D H57).
----------------------------------------- apply (@H53).
------------------------------------------apply (@euclidean__tactics.not__nCol__Col E A F).
-------------------------------------------intro H60.
apply (@H59 H57).


---------------------------------------- exact H58.
-------------------------------- destruct H50 as [H51|H51].
--------------------------------- assert (* Cut *) (euclidean__axioms.Col C D E) as H52.
---------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun E0 => (euclidean__axioms.BetS A E0 B) -> ((euclidean__defs.CongA A E0 F E0 F D) -> ((euclidean__axioms.TS A E0 F D) -> ((euclidean__axioms.Col E0 F H6) -> ((euclidean__axioms.nCol E0 F A) -> ((euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__defs.CongA E0 F D A E0 F) -> ((euclidean__axioms.nCol E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col B A E0) -> ((euclidean__axioms.Col A G E0) -> ((euclidean__axioms.Col A E0 G) -> ((euclidean__defs.Out E0 F F) -> ((euclidean__defs.Supp A E0 F F B) -> ((E0 = E0) -> ((euclidean__defs.Out F E0 E0) -> ((euclidean__defs.Supp D F E0 E0 C) -> ((euclidean__defs.CongA E0 F D D F E0) -> ((euclidean__defs.CongA A E0 F D F E0) -> ((euclidean__defs.CongA F E0 B E0 F C) -> ((euclidean__defs.CongA B E0 F C F E0) -> ((~(euclidean__axioms.BetS A E0 G)) -> ((~(euclidean__defs.Out E0 A G)) -> (euclidean__axioms.Col C D E0))))))))))))))))))))))))))) with (x := E).
-----------------------------------intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
exact H28.

----------------------------------- exact H51.
----------------------------------- exact H.
----------------------------------- exact H1.
----------------------------------- exact H2.
----------------------------------- exact H10.
----------------------------------- exact H11.
----------------------------------- exact H12.
----------------------------------- exact H13.
----------------------------------- exact H16.
----------------------------------- exact H17.
----------------------------------- exact H18.
----------------------------------- exact H19.
----------------------------------- exact H30.
----------------------------------- exact H32.
----------------------------------- exact H33.
----------------------------------- exact H35.
----------------------------------- exact H36.
----------------------------------- exact H37.
----------------------------------- exact H38.
----------------------------------- exact H40.
----------------------------------- exact H41.
----------------------------------- exact H42.
----------------------------------- exact H43.
----------------------------------- exact H44.
----------------------------------- exact H45.
----------------------------------- exact H46.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col C D F) as H53.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H53.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder C F D H14).
------------------------------------ destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H60.
----------------------------------- assert (* Cut *) (euclidean__axioms.Col D E F) as H54.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col D E F).
-------------------------------------intro H54.
apply (@euclidean__tactics.Col__nCol__False D E F H54).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 C D E F H52 H53 H25).


------------------------------------ assert (* Cut *) (euclidean__axioms.Col E F D) as H55.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D))))) as H55.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D E F H54).
-------------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H58.
------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq E F)) as H56.
-------------------------------------- intro H56.
assert (* Cut *) (euclidean__axioms.Col F D H6) as H57.
--------------------------------------- apply (@euclidean__tactics.not__nCol__Col F D H6).
----------------------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False F D H6 H57).
-----------------------------------------apply (@lemma__collinear4.lemma__collinear4 E F D H6 H55 H10 H56).


--------------------------------------- assert (* Cut *) (euclidean__axioms.Col D H6 F) as H58.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D F H6) /\ ((euclidean__axioms.Col D H6 F) /\ ((euclidean__axioms.Col H6 F D) /\ ((euclidean__axioms.Col F H6 D) /\ (euclidean__axioms.Col H6 D F))))) as H58.
----------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F D H6 H57).
----------------------------------------- destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H61.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H6 D) as H59.
----------------------------------------- right.
right.
right.
right.
left.
exact H8.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col D H6 A) as H60.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col H6 A D) /\ ((euclidean__axioms.Col H6 D A) /\ ((euclidean__axioms.Col D A H6) /\ ((euclidean__axioms.Col A D H6) /\ (euclidean__axioms.Col D H6 A))))) as H60.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A H6 D H59).
------------------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H68.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq H6 D) as H61.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H61.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A H6 D H8).
-------------------------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H62.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D H6) as H62.
-------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric H6 D H61).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H6 F A) as H63.
--------------------------------------------- apply (@euclidean__tactics.not__nCol__Col H6 F A).
----------------------------------------------intro H63.
apply (@euclidean__tactics.Col__nCol__False H6 F A H63).
-----------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D H6 F A H58 H60 H62).


--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H6 F E) as H64.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F E H6) /\ ((euclidean__axioms.Col F H6 E) /\ ((euclidean__axioms.Col H6 E F) /\ ((euclidean__axioms.Col E H6 F) /\ (euclidean__axioms.Col H6 F E))))) as H64.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E F H6 H10).
----------------------------------------------- destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H72.
---------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq H6 F)) as H65.
----------------------------------------------- intro H65.
assert (* Cut *) (euclidean__axioms.Col F A E) as H66.
------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col F A E).
-------------------------------------------------intro H66.
apply (@euclidean__tactics.Col__nCol__False F A E H66).
--------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 H6 F A E H63 H64 H65).


------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E F A) as H67.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H67.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F A E H66).
-------------------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H72.
------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False E F D H17 H55).
----------------------------------------------- assert (euclidean__axioms.Col A H6 D) as H66 by exact H59.
assert (* Cut *) (euclidean__axioms.Col A F D) as H67.
------------------------------------------------ apply (@eq__ind euclidean__axioms.Point H6 (fun X => euclidean__axioms.Col A X D)) with (y := F).
------------------------------------------------- exact H66.
-------------------------------------------------apply (@euclidean__tactics.NNPP (H6 = F) H65).

------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D F A) as H68.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F A D) /\ ((euclidean__axioms.Col F D A) /\ ((euclidean__axioms.Col D A F) /\ ((euclidean__axioms.Col A D F) /\ (euclidean__axioms.Col D F A))))) as H68.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A F D H67).
-------------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H76.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D F C) as H69.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))))) as H69.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D F H53).
--------------------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H72.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H6 D) as H70.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F C) /\ ((euclidean__axioms.neq D F) /\ (euclidean__axioms.neq D C))) as H70.
---------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D F C H39).
---------------------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H61.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D H6) as H71.
---------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun E0 => (euclidean__axioms.BetS A E0 B) -> ((euclidean__defs.CongA A E0 F E0 F D) -> ((euclidean__axioms.TS A E0 F D) -> ((euclidean__axioms.Col E0 F H6) -> ((euclidean__axioms.nCol E0 F A) -> ((euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__defs.CongA E0 F D A E0 F) -> ((euclidean__axioms.nCol E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col B A E0) -> ((euclidean__axioms.Col A G E0) -> ((euclidean__axioms.Col A E0 G) -> ((euclidean__defs.Out E0 F F) -> ((euclidean__defs.Supp A E0 F F B) -> ((E0 = E0) -> ((euclidean__defs.Out F E0 E0) -> ((euclidean__defs.Supp D F E0 E0 C) -> ((euclidean__defs.CongA E0 F D D F E0) -> ((euclidean__defs.CongA A E0 F D F E0) -> ((euclidean__defs.CongA F E0 B E0 F C) -> ((euclidean__defs.CongA B E0 F C F E0) -> ((~(euclidean__axioms.BetS A E0 G)) -> ((~(euclidean__defs.Out E0 A G)) -> ((euclidean__axioms.Col C D E0) -> ((euclidean__axioms.Col D E0 F) -> ((euclidean__axioms.Col E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.Col H6 F E0) -> (euclidean__axioms.neq D H6)))))))))))))))))))))))))))))))) with (x := E).
-----------------------------------------------------intro H71.
intro H72.
intro H73.
intro H74.
intro H75.
intro H76.
intro H77.
intro H78.
intro H79.
intro H80.
intro H81.
intro H82.
intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
exact H62.

----------------------------------------------------- exact H51.
----------------------------------------------------- exact H.
----------------------------------------------------- exact H1.
----------------------------------------------------- exact H2.
----------------------------------------------------- exact H10.
----------------------------------------------------- exact H11.
----------------------------------------------------- exact H12.
----------------------------------------------------- exact H13.
----------------------------------------------------- exact H16.
----------------------------------------------------- exact H17.
----------------------------------------------------- exact H18.
----------------------------------------------------- exact H19.
----------------------------------------------------- exact H30.
----------------------------------------------------- exact H32.
----------------------------------------------------- exact H33.
----------------------------------------------------- exact H35.
----------------------------------------------------- exact H36.
----------------------------------------------------- exact H37.
----------------------------------------------------- exact H38.
----------------------------------------------------- exact H40.
----------------------------------------------------- exact H41.
----------------------------------------------------- exact H42.
----------------------------------------------------- exact H43.
----------------------------------------------------- exact H44.
----------------------------------------------------- exact H45.
----------------------------------------------------- exact H46.
----------------------------------------------------- exact H52.
----------------------------------------------------- exact H54.
----------------------------------------------------- exact H55.
----------------------------------------------------- exact H56.
----------------------------------------------------- exact H64.
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D F) as H72.
----------------------------------------------------- intro H72.
assert (* Cut *) (False) as H73.
------------------------------------------------------ assert (* Cut *) (~(H6 = F)) as H73.
------------------------------------------------------- intro H73.
apply (@H15).
--------------------------------------------------------apply (@logic.eq__sym Point D F H72).

------------------------------------------------------- apply (@H65 H73).
------------------------------------------------------ assert (False) as H74 by exact H73.
contradiction H74.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F A C) as H73.
------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col F A C).
-------------------------------------------------------intro H73.
apply (@euclidean__tactics.Col__nCol__False F A C H73).
--------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D F A C H68 H69 H72).


------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C F A) as H74.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A F C) /\ ((euclidean__axioms.Col A C F) /\ ((euclidean__axioms.Col C F A) /\ ((euclidean__axioms.Col F C A) /\ (euclidean__axioms.Col C A F))))) as H74.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F A C H73).
-------------------------------------------------------- destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H79.
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C G) as H75.
-------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C G) /\ ((euclidean__axioms.Col D G C) /\ ((euclidean__axioms.Col G C D) /\ ((euclidean__axioms.Col C G D) /\ (euclidean__axioms.Col G D C))))) as H75.
--------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D G H28).
--------------------------------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
exact H76.
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D F) as H76.
--------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C D G) /\ ((euclidean__axioms.Col C G D) /\ ((euclidean__axioms.Col G D C) /\ ((euclidean__axioms.Col D G C) /\ (euclidean__axioms.Col G C D))))) as H76.
---------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D C G H75).
---------------------------------------------------------- destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
exact H53.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D C F) as H77.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col D F C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C F D) /\ (euclidean__axioms.Col F D C))))) as H77.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D F H76).
----------------------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H78.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H78.
----------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C D H25).
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C G F) as H79.
------------------------------------------------------------ apply (@euclidean__tactics.not__nCol__Col C G F).
-------------------------------------------------------------intro H79.
apply (@euclidean__tactics.Col__nCol__False C G F H79).
--------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D C G F H75 H77 H78).


------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C F G) as H80.
------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col G F C) /\ ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col C F G) /\ (euclidean__axioms.Col F G C))))) as H80.
-------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C G F H79).
-------------------------------------------------------------- destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H87.
------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.neq C F)) as H81.
-------------------------------------------------------------- intro H81.
assert (* Cut *) (euclidean__axioms.Col F A G) as H82.
--------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col F A G).
----------------------------------------------------------------intro H82.
apply (@euclidean__tactics.Col__nCol__False F A G H82).
-----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 C F A G H74 H80 H81).


--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F A E) as H83.
---------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun E0 => (euclidean__axioms.BetS A E0 B) -> ((euclidean__defs.CongA A E0 F E0 F D) -> ((euclidean__axioms.TS A E0 F D) -> ((euclidean__axioms.Col E0 F H6) -> ((euclidean__axioms.nCol E0 F A) -> ((euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__defs.CongA E0 F D A E0 F) -> ((euclidean__axioms.nCol E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col B A E0) -> ((euclidean__axioms.Col A G E0) -> ((euclidean__axioms.Col A E0 G) -> ((euclidean__defs.Out E0 F F) -> ((euclidean__defs.Supp A E0 F F B) -> ((E0 = E0) -> ((euclidean__defs.Out F E0 E0) -> ((euclidean__defs.Supp D F E0 E0 C) -> ((euclidean__defs.CongA E0 F D D F E0) -> ((euclidean__defs.CongA A E0 F D F E0) -> ((euclidean__defs.CongA F E0 B E0 F C) -> ((euclidean__defs.CongA B E0 F C F E0) -> ((~(euclidean__axioms.BetS A E0 G)) -> ((~(euclidean__defs.Out E0 A G)) -> ((euclidean__axioms.Col C D E0) -> ((euclidean__axioms.Col D E0 F) -> ((euclidean__axioms.Col E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.Col H6 F E0) -> (euclidean__axioms.Col F A E0)))))))))))))))))))))))))))))))) with (x := E).
-----------------------------------------------------------------intro H83.
intro H84.
intro H85.
intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
exact H82.

----------------------------------------------------------------- exact H51.
----------------------------------------------------------------- exact H.
----------------------------------------------------------------- exact H1.
----------------------------------------------------------------- exact H2.
----------------------------------------------------------------- exact H10.
----------------------------------------------------------------- exact H11.
----------------------------------------------------------------- exact H12.
----------------------------------------------------------------- exact H13.
----------------------------------------------------------------- exact H16.
----------------------------------------------------------------- exact H17.
----------------------------------------------------------------- exact H18.
----------------------------------------------------------------- exact H19.
----------------------------------------------------------------- exact H30.
----------------------------------------------------------------- exact H32.
----------------------------------------------------------------- exact H33.
----------------------------------------------------------------- exact H35.
----------------------------------------------------------------- exact H36.
----------------------------------------------------------------- exact H37.
----------------------------------------------------------------- exact H38.
----------------------------------------------------------------- exact H40.
----------------------------------------------------------------- exact H41.
----------------------------------------------------------------- exact H42.
----------------------------------------------------------------- exact H43.
----------------------------------------------------------------- exact H44.
----------------------------------------------------------------- exact H45.
----------------------------------------------------------------- exact H46.
----------------------------------------------------------------- exact H52.
----------------------------------------------------------------- exact H54.
----------------------------------------------------------------- exact H55.
----------------------------------------------------------------- exact H56.
----------------------------------------------------------------- exact H64.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H84.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col A E F) /\ ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col F E A) /\ (euclidean__axioms.Col E A F))))) as H84.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder F A E H83).
------------------------------------------------------------------ destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
exact H89.
----------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False E F D H17 H55).
-------------------------------------------------------------- assert (euclidean__axioms.Col A H6 D) as H82 by exact H66.
assert (* Cut *) (euclidean__axioms.Col A C D) as H83.
--------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point H6 (fun X => euclidean__axioms.Col A X D)) with (y := C).
---------------------------------------------------------------- exact H82.
----------------------------------------------------------------apply (@logic.eq__trans Point H6 F C).
-----------------------------------------------------------------apply (@euclidean__tactics.NNPP (H6 = F) H65).

-----------------------------------------------------------------apply (@logic.eq__sym Point C F).
------------------------------------------------------------------apply (@euclidean__tactics.NNPP (C = F) H81).



--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D A) as H84.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H84.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A C D H83).
----------------------------------------------------------------- destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
exact H87.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F D A) as H85.
----------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point C (fun X => euclidean__axioms.Col X D A)) with (y := F).
------------------------------------------------------------------ exact H84.
------------------------------------------------------------------apply (@euclidean__tactics.NNPP (C = F) H81).

----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C D E) as H86.
------------------------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point G (fun E0 => (euclidean__axioms.BetS A E0 B) -> ((euclidean__defs.CongA A E0 F E0 F D) -> ((euclidean__axioms.TS A E0 F D) -> ((euclidean__axioms.Col E0 F H6) -> ((euclidean__axioms.nCol E0 F A) -> ((euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__defs.CongA E0 F D A E0 F) -> ((euclidean__axioms.nCol E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col B A E0) -> ((euclidean__axioms.Col A G E0) -> ((euclidean__axioms.Col A E0 G) -> ((euclidean__defs.Out E0 F F) -> ((euclidean__defs.Supp A E0 F F B) -> ((E0 = E0) -> ((euclidean__defs.Out F E0 E0) -> ((euclidean__defs.Supp D F E0 E0 C) -> ((euclidean__defs.CongA E0 F D D F E0) -> ((euclidean__defs.CongA A E0 F D F E0) -> ((euclidean__defs.CongA F E0 B E0 F C) -> ((euclidean__defs.CongA B E0 F C F E0) -> ((~(euclidean__axioms.BetS A E0 G)) -> ((~(euclidean__defs.Out E0 A G)) -> ((euclidean__axioms.Col C D E0) -> ((euclidean__axioms.Col D E0 F) -> ((euclidean__axioms.Col E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.Col H6 F E0) -> (euclidean__axioms.Col C D E0)))))))))))))))))))))))))))))))) with (x := E).
-------------------------------------------------------------------intro H86.
intro H87.
intro H88.
intro H89.
intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
exact H111.

------------------------------------------------------------------- exact H51.
------------------------------------------------------------------- exact H.
------------------------------------------------------------------- exact H1.
------------------------------------------------------------------- exact H2.
------------------------------------------------------------------- exact H10.
------------------------------------------------------------------- exact H11.
------------------------------------------------------------------- exact H12.
------------------------------------------------------------------- exact H13.
------------------------------------------------------------------- exact H16.
------------------------------------------------------------------- exact H17.
------------------------------------------------------------------- exact H18.
------------------------------------------------------------------- exact H19.
------------------------------------------------------------------- exact H30.
------------------------------------------------------------------- exact H32.
------------------------------------------------------------------- exact H33.
------------------------------------------------------------------- exact H35.
------------------------------------------------------------------- exact H36.
------------------------------------------------------------------- exact H37.
------------------------------------------------------------------- exact H38.
------------------------------------------------------------------- exact H40.
------------------------------------------------------------------- exact H41.
------------------------------------------------------------------- exact H42.
------------------------------------------------------------------- exact H43.
------------------------------------------------------------------- exact H44.
------------------------------------------------------------------- exact H45.
------------------------------------------------------------------- exact H46.
------------------------------------------------------------------- exact H52.
------------------------------------------------------------------- exact H54.
------------------------------------------------------------------- exact H55.
------------------------------------------------------------------- exact H56.
------------------------------------------------------------------- exact H64.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col F D E) as H87.
------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point C (fun X => euclidean__axioms.Col X D E)) with (y := F).
-------------------------------------------------------------------- exact H86.
--------------------------------------------------------------------apply (@euclidean__tactics.NNPP (C = F) H81).

------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D F E) as H88.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F E D) /\ (euclidean__axioms.Col E D F))))) as H88.
--------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F D E H87).
--------------------------------------------------------------------- destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H89.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D F A) as H89.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col F E D) /\ ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col D E F) /\ (euclidean__axioms.Col E F D))))) as H89.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D F E H88).
---------------------------------------------------------------------- destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
exact H68.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D F) as H90.
---------------------------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point G (fun E0 => (euclidean__axioms.BetS A E0 B) -> ((euclidean__defs.CongA A E0 F E0 F D) -> ((euclidean__axioms.TS A E0 F D) -> ((euclidean__axioms.Col E0 F H6) -> ((euclidean__axioms.nCol E0 F A) -> ((euclidean__axioms.Col A E0 B) -> ((euclidean__axioms.neq A E0) -> ((euclidean__defs.CongA E0 F D A E0 F) -> ((euclidean__axioms.nCol E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.neq F E0) -> ((euclidean__axioms.Col B A E0) -> ((euclidean__axioms.Col A G E0) -> ((euclidean__axioms.Col A E0 G) -> ((euclidean__defs.Out E0 F F) -> ((euclidean__defs.Supp A E0 F F B) -> ((E0 = E0) -> ((euclidean__defs.Out F E0 E0) -> ((euclidean__defs.Supp D F E0 E0 C) -> ((euclidean__defs.CongA E0 F D D F E0) -> ((euclidean__defs.CongA A E0 F D F E0) -> ((euclidean__defs.CongA F E0 B E0 F C) -> ((euclidean__defs.CongA B E0 F C F E0) -> ((~(euclidean__axioms.BetS A E0 G)) -> ((~(euclidean__defs.Out E0 A G)) -> ((euclidean__axioms.Col C D E0) -> ((euclidean__axioms.Col D E0 F) -> ((euclidean__axioms.Col E0 F D) -> ((euclidean__axioms.neq E0 F) -> ((euclidean__axioms.Col H6 F E0) -> ((euclidean__axioms.Col C D E0) -> ((euclidean__axioms.Col F D E0) -> ((euclidean__axioms.Col D F E0) -> (euclidean__axioms.neq D F))))))))))))))))))))))))))))))))))) with (x := E).
-----------------------------------------------------------------------intro H90.
intro H91.
intro H92.
intro H93.
intro H94.
intro H95.
intro H96.
intro H97.
intro H98.
intro H99.
intro H100.
intro H101.
intro H102.
intro H103.
intro H104.
intro H105.
intro H106.
intro H107.
intro H108.
intro H109.
intro H110.
intro H111.
intro H112.
intro H113.
intro H114.
intro H115.
intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
exact H72.

----------------------------------------------------------------------- exact H51.
----------------------------------------------------------------------- exact H.
----------------------------------------------------------------------- exact H1.
----------------------------------------------------------------------- exact H2.
----------------------------------------------------------------------- exact H10.
----------------------------------------------------------------------- exact H11.
----------------------------------------------------------------------- exact H12.
----------------------------------------------------------------------- exact H13.
----------------------------------------------------------------------- exact H16.
----------------------------------------------------------------------- exact H17.
----------------------------------------------------------------------- exact H18.
----------------------------------------------------------------------- exact H19.
----------------------------------------------------------------------- exact H30.
----------------------------------------------------------------------- exact H32.
----------------------------------------------------------------------- exact H33.
----------------------------------------------------------------------- exact H35.
----------------------------------------------------------------------- exact H36.
----------------------------------------------------------------------- exact H37.
----------------------------------------------------------------------- exact H38.
----------------------------------------------------------------------- exact H40.
----------------------------------------------------------------------- exact H41.
----------------------------------------------------------------------- exact H42.
----------------------------------------------------------------------- exact H43.
----------------------------------------------------------------------- exact H44.
----------------------------------------------------------------------- exact H45.
----------------------------------------------------------------------- exact H46.
----------------------------------------------------------------------- exact H52.
----------------------------------------------------------------------- exact H54.
----------------------------------------------------------------------- exact H55.
----------------------------------------------------------------------- exact H56.
----------------------------------------------------------------------- exact H64.
----------------------------------------------------------------------- exact H86.
----------------------------------------------------------------------- exact H87.
----------------------------------------------------------------------- exact H88.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F E A) as H91.
----------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col F E A).
------------------------------------------------------------------------intro H91.
apply (@euclidean__tactics.Col__nCol__False F E A H91).
-------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D F E A H88 H89 H90).


----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H92.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col E F A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A F E) /\ ((euclidean__axioms.Col F A E) /\ (euclidean__axioms.Col A E F))))) as H92.
------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F E A H91).
------------------------------------------------------------------------- destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
exact H93.
------------------------------------------------------------------------ apply (@euclidean__tactics.Col__nCol__False E F D H17 H55).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F A) as H57.
--------------------------------------- assert (* Cut *) (False) as H57.
---------------------------------------- apply (@H56 H18).
---------------------------------------- contradiction H57.
--------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H58.
---------------------------------------- intro H58.
apply (@H56 H18).
---------------------------------------- exact H58.
--------------------------------- destruct H51 as [H52|H52].
---------------------------------- assert (* Cut *) (euclidean__axioms.neq E A) as H53.
----------------------------------- assert (* Cut *) ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq E A) /\ (euclidean__axioms.neq E G))) as H53.
------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal E A G H52).
------------------------------------ destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H56.
----------------------------------- assert (* Cut *) (euclidean__defs.Out E A G) as H54.
------------------------------------ apply (@lemma__ray4.lemma__ray4 E A G).
-------------------------------------right.
right.
exact H52.

------------------------------------- exact H53.
------------------------------------ assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H55.
------------------------------------- intro H55.
apply (@H46 H54).
------------------------------------- exact H55.
---------------------------------- destruct H52 as [H53|H53].
----------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H54.
------------------------------------ intro H54.
apply (@H45 H53).
------------------------------------ exact H54.
----------------------------------- assert (* Cut *) (euclidean__axioms.BetS E G A) as H54.
------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry A G E H53).
------------------------------------ assert (* Cut *) (euclidean__axioms.neq E A) as H55.
------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq E G) /\ (euclidean__axioms.neq E A))) as H55.
-------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E G A H54).
-------------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H59.
------------------------------------- assert (* Cut *) (euclidean__defs.Out E A G) as H56.
-------------------------------------- apply (@lemma__ray4.lemma__ray4 E A G).
---------------------------------------left.
exact H54.

--------------------------------------- exact H55.
-------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H57.
--------------------------------------- intro H57.
apply (@H46 H56).
--------------------------------------- exact H57.
------------------------------ apply (@H48 H20).
----------- assert (* Cut *) (A = A) as H21.
------------ apply (@logic.eq__refl Point A).
------------ assert (* Cut *) (euclidean__axioms.Col A B A) as H22.
------------- right.
left.
exact H21.
------------- assert (* Cut *) (euclidean__axioms.Col A B E) as H23.
-------------- right.
right.
right.
right.
right.
exact H.
-------------- assert (* Cut *) (D = D) as H24.
--------------- apply (@logic.eq__refl Point D).
--------------- assert (* Cut *) (euclidean__axioms.Col C D D) as H25.
---------------- right.
right.
left.
exact H24.
---------------- assert (* Cut *) (euclidean__axioms.Col C D F) as H26.
----------------- right.
right.
right.
right.
right.
exact H0.
----------------- assert (* Cut *) (euclidean__axioms.neq A E) as H27.
------------------ assert (* Cut *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H27.
------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A H6 D H8).
------------------- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H13.
------------------ assert (* Cut *) (euclidean__axioms.neq F D) as H28.
------------------- assert (* Cut *) ((euclidean__axioms.neq H6 D) /\ ((euclidean__axioms.neq A H6) /\ (euclidean__axioms.neq A D))) as H28.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A H6 D H8).
-------------------- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H15.
------------------- assert (* Cut *) (euclidean__axioms.BetS E H6 F) as H29.
-------------------- apply (@lemma__collinearbetween.lemma__collinearbetween A B C D E F H6 H12 H14 H3 H4 H27 H28 H20 H8 H10).
-------------------- assert (* Cut *) (euclidean__axioms.BetS F H6 E) as H30.
--------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E H6 F H29).
--------------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H31.
---------------------- exists A.
exists E.
exists F.
exists D.
exists H6.
split.
----------------------- exact H3.
----------------------- split.
------------------------ exact H4.
------------------------ split.
------------------------- exact H22.
------------------------- split.
-------------------------- exact H23.
-------------------------- split.
--------------------------- exact H27.
--------------------------- split.
---------------------------- exact H26.
---------------------------- split.
----------------------------- exact H25.
----------------------------- split.
------------------------------ exact H28.
------------------------------ split.
------------------------------- exact H20.
------------------------------- split.
-------------------------------- exact H8.
-------------------------------- exact H30.
---------------------- exact H31.
Qed.
