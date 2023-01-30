Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__3.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__PGrectangle.
Require Export lemma__PGrotate.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__collinearright.
Require Export lemma__congruencesymmetric.
Require Export lemma__equaltorightisright.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__oppositesideflip.
Require Export lemma__paste5.
Require Export lemma__rectanglerotate.
Require Export lemma__rightangleNC.
Require Export lemma__squaresequal.
Require Export logic.
Require Export proposition__08.
Require Export proposition__11B.
Require Export proposition__46.
Require Export proposition__47.
Require Export proposition__48A.
Definition proposition__48 : forall A B C D E F G H K L M, (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.SQ A B F G) -> ((euclidean__defs.SQ A C K H) -> ((euclidean__defs.SQ B C E D) -> ((euclidean__axioms.BetS B M C) -> ((euclidean__axioms.BetS E L D) -> ((euclidean__axioms.EF A B F G B M L D) -> ((euclidean__axioms.EF A C K H M C E L) -> ((euclidean__defs.RE M C E L) -> (euclidean__defs.Per B A C))))))))).
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
intro L.
intro M.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
intro H6.
intro H7.
intro H8.
assert (euclidean__axioms.nCol A B C) as H9 by exact H0.
assert (* Cut *) (euclidean__axioms.neq A C) as H10.
- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H10.
-- apply (@lemma__NCdistinct.lemma__NCdistinct A B C H9).
-- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H15.
- assert (* Cut *) (euclidean__axioms.neq A B) as H11.
-- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H11.
--- apply (@lemma__NCdistinct.lemma__NCdistinct A B C H9).
--- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H12.
-- assert (* Cut *) (euclidean__axioms.neq B A) as H12.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H11).
--- assert (* Cut *) (exists R, (euclidean__axioms.BetS B A R) /\ (euclidean__axioms.Cong A R A B)) as H13.
---- apply (@lemma__extension.lemma__extension B A A B H12 H11).
---- destruct H13 as [R H14].
destruct H14 as [H15 H16].
assert (* Cut *) (euclidean__axioms.Col B A R) as H17.
----- right.
right.
right.
right.
left.
exact H15.
----- assert (* Cut *) (euclidean__axioms.Col A B R) as H18.
------ assert (* Cut *) ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col A R B) /\ ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B R A) /\ (euclidean__axioms.Col R A B))))) as H18.
------- apply (@lemma__collinearorder.lemma__collinearorder B A R H17).
------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H19.
------ assert (* Cut *) (B = B) as H19.
------- apply (@logic.eq__refl Point B).
------- assert (* Cut *) (euclidean__axioms.Col A B B) as H20.
-------- right.
right.
left.
exact H19.
-------- assert (* Cut *) (euclidean__axioms.neq B R) as H21.
--------- assert (* Cut *) ((euclidean__axioms.neq A R) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B R))) as H21.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal B A R H15).
---------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H25.
--------- assert (* Cut *) (euclidean__axioms.neq R B) as H22.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B R H21).
---------- assert (* Cut *) (euclidean__axioms.nCol R B C) as H23.
----------- apply (@euclidean__tactics.nCol__notCol R B C).
------------apply (@euclidean__tactics.nCol__not__Col R B C).
-------------apply (@lemma__NChelper.lemma__NChelper A B C R B H9 H18 H20 H22).


----------- assert (* Cut *) (euclidean__axioms.nCol B R C) as H24.
------------ assert (* Cut *) ((euclidean__axioms.nCol B R C) /\ ((euclidean__axioms.nCol B C R) /\ ((euclidean__axioms.nCol C R B) /\ ((euclidean__axioms.nCol R C B) /\ (euclidean__axioms.nCol C B R))))) as H24.
------------- apply (@lemma__NCorder.lemma__NCorder R B C H23).
------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H25.
------------ assert (* Cut *) (exists Q, (euclidean__defs.Per B A Q) /\ (euclidean__axioms.TS Q B R C)) as H25.
------------- apply (@proposition__11B.proposition__11B B R A C H15 H24).
------------- destruct H25 as [Q H26].
destruct H26 as [H27 H28].
assert (* Cut *) (euclidean__axioms.nCol B A Q) as H29.
-------------- apply (@lemma__rightangleNC.lemma__rightangleNC B A Q H27).
-------------- assert (* Cut *) (euclidean__axioms.neq A Q) as H30.
--------------- assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq Q A) /\ (euclidean__axioms.neq Q B)))))) as H30.
---------------- apply (@lemma__NCdistinct.lemma__NCdistinct B A Q H29).
---------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H33.
--------------- assert (* Cut *) (exists c, (euclidean__defs.Out A Q c) /\ (euclidean__axioms.Cong A c A C)) as H31.
---------------- apply (@lemma__layoff.lemma__layoff A Q A C H30 H10).
---------------- destruct H31 as [c H32].
destruct H32 as [H33 H34].
assert (* Cut *) (euclidean__defs.Per B A c) as H35.
----------------- apply (@lemma__8__3.lemma__8__3 B A Q c H27 H33).
----------------- assert (* Cut *) (euclidean__axioms.nCol B A c) as H36.
------------------ apply (@lemma__rightangleNC.lemma__rightangleNC B A c H35).
------------------ assert (* Cut *) (euclidean__axioms.nCol A B c) as H37.
------------------- assert (* Cut *) ((euclidean__axioms.nCol A B c) /\ ((euclidean__axioms.nCol A c B) /\ ((euclidean__axioms.nCol c B A) /\ ((euclidean__axioms.nCol B c A) /\ (euclidean__axioms.nCol c A B))))) as H37.
-------------------- apply (@lemma__NCorder.lemma__NCorder B A c H36).
-------------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H38.
------------------- assert (* Cut *) (exists f g, (euclidean__defs.SQ A B f g) /\ ((euclidean__axioms.TS g A B c) /\ (euclidean__defs.PG A B f g))) as H38.
-------------------- apply (@proposition__46.proposition__46 A B c H11 H37).
-------------------- destruct H38 as [f H39].
destruct H39 as [g H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
assert (* Cut *) (euclidean__axioms.neq A c) as H45.
--------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B c) /\ ((euclidean__axioms.neq A c) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq c B) /\ (euclidean__axioms.neq c A)))))) as H45.
---------------------- apply (@lemma__NCdistinct.lemma__NCdistinct A B c H37).
---------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H50.
--------------------- assert (* Cut *) (euclidean__axioms.nCol A c B) as H46.
---------------------- assert (* Cut *) ((euclidean__axioms.nCol B A c) /\ ((euclidean__axioms.nCol B c A) /\ ((euclidean__axioms.nCol c A B) /\ ((euclidean__axioms.nCol A c B) /\ (euclidean__axioms.nCol c B A))))) as H46.
----------------------- apply (@lemma__NCorder.lemma__NCorder A B c H37).
----------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H53.
---------------------- assert (* Cut *) (exists k h, (euclidean__defs.SQ A c k h) /\ ((euclidean__axioms.TS h A c B) /\ (euclidean__defs.PG A c k h))) as H47.
----------------------- apply (@proposition__46.proposition__46 A c B H45 H46).
----------------------- destruct H47 as [k H48].
destruct H48 as [h H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
assert (* Cut *) (euclidean__axioms.neq B c) as H54.
------------------------ assert (* Cut *) ((euclidean__axioms.neq A c) /\ ((euclidean__axioms.neq c B) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c A) /\ ((euclidean__axioms.neq B c) /\ (euclidean__axioms.neq B A)))))) as H54.
------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct A c B H46).
------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H63.
------------------------ assert (* Cut *) (euclidean__axioms.nCol B c A) as H55.
------------------------- assert (* Cut *) ((euclidean__axioms.nCol c A B) /\ ((euclidean__axioms.nCol c B A) /\ ((euclidean__axioms.nCol B A c) /\ ((euclidean__axioms.nCol A B c) /\ (euclidean__axioms.nCol B c A))))) as H55.
-------------------------- apply (@lemma__NCorder.lemma__NCorder A c B H46).
-------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H63.
------------------------- assert (* Cut *) (exists e d, (euclidean__defs.SQ B c e d) /\ ((euclidean__axioms.TS d B c A) /\ (euclidean__defs.PG B c e d))) as H56.
-------------------------- apply (@proposition__46.proposition__46 B c A H54 H55).
-------------------------- destruct H56 as [e H57].
destruct H57 as [d H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
assert (euclidean__axioms.Triangle A B c) as H63 by exact H37.
assert (* Cut *) (euclidean__axioms.TS g B A c) as H64.
--------------------------- apply (@lemma__oppositesideflip.lemma__oppositesideflip A B g c H43).
--------------------------- assert (* Cut *) (euclidean__axioms.TS h c A B) as H65.
---------------------------- apply (@lemma__oppositesideflip.lemma__oppositesideflip A c h B H52).
---------------------------- assert (* Cut *) (euclidean__axioms.TS d c B A) as H66.
----------------------------- apply (@lemma__oppositesideflip.lemma__oppositesideflip B c d A H61).
----------------------------- assert (* Cut *) (exists m l, (euclidean__defs.PG B m l d) /\ ((euclidean__axioms.BetS B m c) /\ ((euclidean__defs.PG m c e l) /\ ((euclidean__axioms.BetS d l e) /\ ((euclidean__axioms.EF A B f g B m l d) /\ (euclidean__axioms.EF A c k h m c e l)))))) as H67.
------------------------------ apply (@proposition__47.proposition__47 A B c d e f g h k H63 H35 H41 H64 H50 H65 H59 H66).
------------------------------ destruct H67 as [m H68].
destruct H68 as [l H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
assert (* Cut *) (euclidean__axioms.Cong A C A c) as H80.
------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A c C H34).
------------------------------- assert (* Cut *) (euclidean__axioms.EF A C K H A c k h) as H81.
-------------------------------- apply (@lemma__squaresequal.lemma__squaresequal A C K H A c k h H80 H2 H50).
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B A B) as H82.
--------------------------------- apply (@euclidean__axioms.cn__congruencereflexive A B).
--------------------------------- assert (* Cut *) (euclidean__axioms.EF A B F G A B f g) as H83.
---------------------------------- apply (@lemma__squaresequal.lemma__squaresequal A B F G A B f g H82 H1 H41).
---------------------------------- assert (* Cut *) (euclidean__axioms.EF A B F G B m l d) as H84.
----------------------------------- apply (@euclidean__axioms.axiom__EFtransitive A B F G B m l d A B f g H83 H78).
----------------------------------- assert (* Cut *) (euclidean__axioms.EF B M L D A B F G) as H85.
------------------------------------ apply (@euclidean__axioms.axiom__EFsymmetric A B F G B M L D H6).
------------------------------------ assert (* Cut *) (euclidean__axioms.EF B M L D B m l d) as H86.
------------------------------------- apply (@euclidean__axioms.axiom__EFtransitive B M L D B m l d A B F G H85 H84).
------------------------------------- assert (* Cut *) (euclidean__axioms.EF M C E L A C K H) as H87.
-------------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric A C K H M C E L H7).
-------------------------------------- assert (* Cut *) (euclidean__axioms.EF M C E L A c k h) as H88.
--------------------------------------- apply (@euclidean__axioms.axiom__EFtransitive M C E L A c k h A C K H H87 H81).
--------------------------------------- assert (* Cut *) (euclidean__axioms.EF M C E L m c e l) as H89.
---------------------------------------- apply (@euclidean__axioms.axiom__EFtransitive M C E L m c e l A c k h H88 H79).
---------------------------------------- assert (* Cut *) (euclidean__axioms.BetS e l d) as H90.
----------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry d l e H76).
----------------------------------------- assert (* Cut *) (euclidean__defs.Per B c e) as H91.
------------------------------------------ destruct H59 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H50 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H41 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H3 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
destruct H2 as [H139 H140].
destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
destruct H1 as [H151 H152].
destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
exact H99.
------------------------------------------ assert (* Cut *) (euclidean__axioms.neq m c) as H92.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq B m) /\ (euclidean__axioms.neq B c))) as H92.
-------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B m c H72).
-------------------------------------------- destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H93.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B m c) as H93.
-------------------------------------------- right.
right.
right.
right.
left.
exact H72.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B c m) as H94.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col m B c) /\ ((euclidean__axioms.Col m c B) /\ ((euclidean__axioms.Col c B m) /\ ((euclidean__axioms.Col B c m) /\ (euclidean__axioms.Col c m B))))) as H94.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B m c H93).
---------------------------------------------- destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
exact H101.
--------------------------------------------- assert (* Cut *) (euclidean__defs.Per m c e) as H95.
---------------------------------------------- apply (@lemma__collinearright.lemma__collinearright B c m e H91 H94 H92).
---------------------------------------------- assert (* Cut *) (euclidean__defs.PG c e l m) as H96.
----------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate m c e l H74).
----------------------------------------------- assert (* Cut *) (euclidean__defs.RE c e l m) as H97.
------------------------------------------------ apply (@lemma__PGrectangle.lemma__PGrectangle c m e l H96 H95).
------------------------------------------------ assert (* Cut *) (euclidean__defs.RE e l m c) as H98.
------------------------------------------------- apply (@lemma__rectanglerotate.lemma__rectanglerotate c e l m H97).
------------------------------------------------- assert (* Cut *) (euclidean__defs.RE l m c e) as H99.
-------------------------------------------------- apply (@lemma__rectanglerotate.lemma__rectanglerotate e l m c H98).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.RE m c e l) as H100.
--------------------------------------------------- apply (@lemma__rectanglerotate.lemma__rectanglerotate l m c e H99).
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B C E D B c e d) as H101.
---------------------------------------------------- apply (@lemma__paste5.lemma__paste5 B C D E L M B c d e l m H86 H89 H4 H72 H5 H90 H8 H100).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C B c) as H102.
----------------------------------------------------- apply (@proposition__48A.proposition__48A B C E D B c e d H3 H59 H101).
----------------------------------------------------- assert (euclidean__axioms.Cong A C A c) as H103 by exact H80.
assert (euclidean__axioms.Triangle A B c) as H104 by exact H63.
assert (* Cut *) (euclidean__defs.CongA B A C B A c) as H105.
------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.Triangle A B c) -> ((euclidean__axioms.Cong A B A B) -> ((euclidean__axioms.Cong A C A c) -> ((euclidean__axioms.Cong B C B c) -> (euclidean__defs.CongA B A C B A c)))))) as H105.
------------------------------------------------------- intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.CongA B A C B A c) /\ ((euclidean__defs.CongA C B A c B A) /\ (euclidean__defs.CongA A C B A c B))) as __4.
-------------------------------------------------------- apply (@proposition__08.proposition__08 A B C A B c __ __0 __1 __2 __3).
-------------------------------------------------------- destruct __4 as [__4 __5].
exact __4.
------------------------------------------------------- apply (@H105 H0 H104 H82 H103 H102).
------------------------------------------------------ assert (* Cut *) (euclidean__defs.Per B A C) as H106.
------------------------------------------------------- apply (@lemma__equaltorightisright.lemma__equaltorightisright B A c B A C H35 H105).
------------------------------------------------------- exact H106.
Qed.
