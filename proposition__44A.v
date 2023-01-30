Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__PGflip.
Require Export lemma__PGrotate.
Require Export lemma__Playfair.
Require Export lemma__betweennotequal.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__collinearparallel2.
Require Export lemma__congruenceflip.
Require Export lemma__congruencetransitive.
Require Export lemma__diagonalsbisect.
Require Export lemma__diagonalsmeet.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelbetween.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__samesidecollinear.
Require Export lemma__samesideflip.
Require Export lemma__samesidetransitive.
Require Export lemma__triangletoparallelogram.
Require Export logic.
Require Export proposition__15.
Require Export proposition__30.
Require Export proposition__31.
Require Export proposition__33B.
Require Export proposition__34.
Require Export proposition__43.
Require Export proposition__43B.
Definition proposition__44A : forall A B D E F G J N, (euclidean__defs.PG B E F G) -> ((euclidean__defs.CongA E B G J D N) -> ((euclidean__axioms.BetS A B E) -> (exists X Y, (euclidean__defs.PG A B X Y) /\ ((euclidean__defs.CongA A B X J D N) /\ ((euclidean__axioms.EF B E F G Y X B A) /\ (euclidean__axioms.BetS G B X)))))).
Proof.
intro A.
intro B.
intro D.
intro E.
intro F.
intro G.
intro J.
intro N.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__defs.PG E F G B) as H2.
- apply (@lemma__PGrotate.lemma__PGrotate B E F G H).
- assert (* Cut *) (euclidean__defs.PG F G B E) as H3.
-- apply (@lemma__PGrotate.lemma__PGrotate E F G B H2).
-- assert (* Cut *) (euclidean__defs.PG G B E F) as H4.
--- apply (@lemma__PGrotate.lemma__PGrotate F G B E H3).
--- assert (* Cut *) (euclidean__defs.Par G F B E) as H5.
---- destruct H4 as [H5 H6].
destruct H3 as [H7 H8].
destruct H2 as [H9 H10].
destruct H as [H11 H12].
exact H6.
---- assert (* Cut *) (euclidean__axioms.nCol G B E) as H6.
----- assert (* Cut *) ((euclidean__axioms.nCol G F B) /\ ((euclidean__axioms.nCol G B E) /\ ((euclidean__axioms.nCol F B E) /\ (euclidean__axioms.nCol G F E)))) as H6.
------ apply (@lemma__parallelNC.lemma__parallelNC G F B E H5).
------ destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H9.
----- assert (* Cut *) (euclidean__axioms.neq G B) as H7.
------ assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq G E) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E G)))))) as H7.
------- apply (@lemma__NCdistinct.lemma__NCdistinct G B E H6).
------- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H8.
------ assert (* Cut *) (exists q, (euclidean__axioms.BetS G B q) /\ (euclidean__axioms.Cong B q G B)) as H8.
------- apply (@lemma__extension.lemma__extension G B G B H7 H7).
------- destruct H8 as [q H9].
destruct H9 as [H10 H11].
assert (* Cut *) (euclidean__axioms.nCol E B G) as H12.
-------- assert (* Cut *) ((euclidean__axioms.nCol B G E) /\ ((euclidean__axioms.nCol B E G) /\ ((euclidean__axioms.nCol E G B) /\ ((euclidean__axioms.nCol G E B) /\ (euclidean__axioms.nCol E B G))))) as H12.
--------- apply (@lemma__NCorder.lemma__NCorder G B E H6).
--------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H20.
-------- assert (* Cut *) (euclidean__axioms.Col A B E) as H13.
--------- right.
right.
right.
right.
left.
exact H1.
--------- assert (* Cut *) (euclidean__axioms.Col E B A) as H14.
---------- assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H14.
----------- apply (@lemma__collinearorder.lemma__collinearorder A B E H13).
----------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H22.
---------- assert (* Cut *) (B = B) as H15.
----------- apply (@logic.eq__refl Point B).
----------- assert (* Cut *) (euclidean__axioms.Col E B B) as H16.
------------ right.
right.
left.
exact H15.
------------ assert (* Cut *) (euclidean__axioms.neq A B) as H17.
------------- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H17.
-------------- apply (@lemma__betweennotequal.lemma__betweennotequal A B E H1).
-------------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H20.
------------- assert (* Cut *) (euclidean__axioms.nCol A B G) as H18.
-------------- apply (@euclidean__tactics.nCol__notCol A B G).
---------------apply (@euclidean__tactics.nCol__not__Col A B G).
----------------apply (@lemma__NChelper.lemma__NChelper E B G A B H12 H14 H16 H17).


-------------- assert (* Cut *) (euclidean__axioms.Col G B q) as H19.
--------------- right.
right.
right.
right.
left.
exact H10.
--------------- assert (* Cut *) (euclidean__axioms.nCol G B A) as H20.
---------------- assert (* Cut *) ((euclidean__axioms.nCol B A G) /\ ((euclidean__axioms.nCol B G A) /\ ((euclidean__axioms.nCol G A B) /\ ((euclidean__axioms.nCol A G B) /\ (euclidean__axioms.nCol G B A))))) as H20.
----------------- apply (@lemma__NCorder.lemma__NCorder A B G H18).
----------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H28.
---------------- assert (* Cut *) (euclidean__axioms.neq G q) as H21.
----------------- assert (* Cut *) ((euclidean__axioms.neq B q) /\ ((euclidean__axioms.neq G B) /\ (euclidean__axioms.neq G q))) as H21.
------------------ apply (@lemma__betweennotequal.lemma__betweennotequal G B q H10).
------------------ destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H25.
----------------- assert (* Cut *) (euclidean__axioms.neq q G) as H22.
------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric G q H21).
------------------ assert (* Cut *) (G = G) as H23.
------------------- apply (@logic.eq__refl Point G).
------------------- assert (* Cut *) (euclidean__axioms.Col G B G) as H24.
-------------------- right.
left.
exact H23.
-------------------- assert (* Cut *) (euclidean__axioms.nCol q G A) as H25.
--------------------- apply (@euclidean__tactics.nCol__notCol q G A).
----------------------apply (@euclidean__tactics.nCol__not__Col q G A).
-----------------------apply (@lemma__NChelper.lemma__NChelper G B A q G H20 H19 H24 H22).


--------------------- assert (* Cut *) (euclidean__axioms.nCol G q A) as H26.
---------------------- assert (* Cut *) ((euclidean__axioms.nCol G q A) /\ ((euclidean__axioms.nCol G A q) /\ ((euclidean__axioms.nCol A q G) /\ ((euclidean__axioms.nCol q A G) /\ (euclidean__axioms.nCol A G q))))) as H26.
----------------------- apply (@lemma__NCorder.lemma__NCorder q G A H25).
----------------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H27.
---------------------- assert (* Cut *) (exists H27 h T, (euclidean__axioms.BetS H27 A h) /\ ((euclidean__defs.CongA h A B A B G) /\ ((euclidean__defs.CongA h A B G B A) /\ ((euclidean__defs.CongA B A h G B A) /\ ((euclidean__defs.CongA H27 A B A B q) /\ ((euclidean__defs.CongA H27 A B q B A) /\ ((euclidean__defs.CongA B A H27 q B A) /\ ((euclidean__defs.Par H27 h G q) /\ ((euclidean__axioms.Cong H27 A B q) /\ ((euclidean__axioms.Cong A h G B) /\ ((euclidean__axioms.Cong A T T B) /\ ((euclidean__axioms.Cong H27 T T q) /\ ((euclidean__axioms.Cong G T T h) /\ ((euclidean__axioms.BetS H27 T q) /\ ((euclidean__axioms.BetS G T h) /\ (euclidean__axioms.BetS A T B)))))))))))))))) as H27.
----------------------- apply (@proposition__31.proposition__31 A G q B H10 H26).
----------------------- destruct H27 as [H28 H29].
destruct H29 as [h H30].
destruct H30 as [T H31].
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
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
assert (* Cut *) (euclidean__defs.Par H28 h q G) as H62.
------------------------ assert (* Cut *) ((euclidean__defs.Par h H28 G q) /\ ((euclidean__defs.Par H28 h q G) /\ (euclidean__defs.Par h H28 q G))) as H62.
------------------------- apply (@lemma__parallelflip.lemma__parallelflip H28 h G q H46).
------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H65.
------------------------ assert (euclidean__axioms.Col G B q) as H63 by exact H19.
assert (* Cut *) (euclidean__axioms.Col q G B) as H64.
------------------------- assert (* Cut *) ((euclidean__axioms.Col B G q) /\ ((euclidean__axioms.Col B q G) /\ ((euclidean__axioms.Col q G B) /\ ((euclidean__axioms.Col G q B) /\ (euclidean__axioms.Col q B G))))) as H64.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder G B q H63).
-------------------------- destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H69.
------------------------- assert (* Cut *) (euclidean__axioms.neq B G) as H65.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq G A) /\ ((euclidean__axioms.neq B G) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A G)))))) as H65.
--------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct G B A H20).
--------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H72.
-------------------------- assert (* Cut *) (euclidean__defs.Par H28 h B G) as H66.
--------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel H28 h B q G H62 H64 H65).
--------------------------- assert (* Cut *) (euclidean__defs.Par H28 h G B) as H67.
---------------------------- assert (* Cut *) ((euclidean__defs.Par h H28 B G) /\ ((euclidean__defs.Par H28 h G B) /\ (euclidean__defs.Par h H28 G B))) as H67.
----------------------------- apply (@lemma__parallelflip.lemma__parallelflip H28 h B G H66).
----------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H70.
---------------------------- assert (* Cut *) (euclidean__defs.Par G B H28 h) as H68.
----------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric H28 h G B H67).
----------------------------- assert (* Cut *) (euclidean__defs.Par G B h H28) as H69.
------------------------------ assert (* Cut *) ((euclidean__defs.Par B G H28 h) /\ ((euclidean__defs.Par G B h H28) /\ (euclidean__defs.Par B G h H28))) as H69.
------------------------------- apply (@lemma__parallelflip.lemma__parallelflip G B H28 h H68).
------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H72.
------------------------------ assert (* Cut *) (euclidean__axioms.Col H28 A h) as H70.
------------------------------- right.
right.
right.
right.
left.
exact H32.
------------------------------- assert (* Cut *) (euclidean__axioms.Col h H28 A) as H71.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col A H28 h) /\ ((euclidean__axioms.Col A h H28) /\ ((euclidean__axioms.Col h H28 A) /\ ((euclidean__axioms.Col H28 h A) /\ (euclidean__axioms.Col h A H28))))) as H71.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H28 A h H70).
--------------------------------- destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H76.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq H28 A) as H72.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq A h) /\ ((euclidean__axioms.neq H28 A) /\ (euclidean__axioms.neq H28 h))) as H72.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H28 A h H32).
---------------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H75.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq A H28) as H73.
---------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric H28 A H72).
---------------------------------- assert (* Cut *) (euclidean__defs.Par G B A H28) as H74.
----------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel G B A h H28 H69 H71 H73).
----------------------------------- assert (* Cut *) (euclidean__defs.Par G B H28 A) as H75.
------------------------------------ assert (* Cut *) ((euclidean__defs.Par B G A H28) /\ ((euclidean__defs.Par G B H28 A) /\ (euclidean__defs.Par B G H28 A))) as H75.
------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip G B A H28 H74).
------------------------------------- destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H78.
------------------------------------ assert (* Cut *) (euclidean__defs.Par H28 A G B) as H76.
------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric G B H28 A H75).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H28 A G B) as H77.
-------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive H28 A B q G B H48 H11).
-------------------------------------- assert (B = B) as H78 by exact H15.
assert (* Cut *) (euclidean__axioms.Col A B B) as H79.
--------------------------------------- right.
right.
left.
exact H78.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col A T B) as H80.
---------------------------------------- right.
right.
right.
right.
left.
exact H61.
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B T) as H81.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Col T A B) /\ ((euclidean__axioms.Col T B A) /\ ((euclidean__axioms.Col B A T) /\ ((euclidean__axioms.Col A B T) /\ (euclidean__axioms.Col B T A))))) as H81.
------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A T B H80).
------------------------------------------ destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
exact H88.
----------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B H28 A) as H82.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol G B H28) /\ ((euclidean__axioms.nCol G H28 A) /\ ((euclidean__axioms.nCol B H28 A) /\ (euclidean__axioms.nCol G B A)))) as H82.
------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC G B H28 A H75).
------------------------------------------- destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
exact H87.
------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A B H28) as H83.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H28 B A) /\ ((euclidean__axioms.nCol H28 A B) /\ ((euclidean__axioms.nCol A B H28) /\ ((euclidean__axioms.nCol B A H28) /\ (euclidean__axioms.nCol A H28 B))))) as H83.
-------------------------------------------- apply (@lemma__NCorder.lemma__NCorder B H28 A H82).
-------------------------------------------- destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
exact H88.
------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H28 A B) as H84.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H28 A G) /\ ((euclidean__axioms.nCol H28 G B) /\ ((euclidean__axioms.nCol A G B) /\ (euclidean__axioms.nCol H28 A B)))) as H84.
--------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC H28 A G B H76).
--------------------------------------------- destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H90.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol A B H28) as H85.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A H28 B) /\ ((euclidean__axioms.nCol A B H28) /\ ((euclidean__axioms.nCol B H28 A) /\ ((euclidean__axioms.nCol H28 B A) /\ (euclidean__axioms.nCol B A H28))))) as H85.
---------------------------------------------- apply (@lemma__NCorder.lemma__NCorder H28 A B H84).
---------------------------------------------- destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
exact H88.
--------------------------------------------- assert (* Cut *) (euclidean__defs.OS H28 G A B) as H86.
---------------------------------------------- exists q.
exists T.
exists B.
split.
----------------------------------------------- exact H81.
----------------------------------------------- split.
------------------------------------------------ exact H79.
------------------------------------------------ split.
------------------------------------------------- exact H58.
------------------------------------------------- split.
-------------------------------------------------- exact H10.
-------------------------------------------------- split.
--------------------------------------------------- exact H85.
--------------------------------------------------- exact H18.
---------------------------------------------- assert (* Cut *) ((euclidean__defs.Par H28 G A B) /\ (euclidean__axioms.Cong H28 G A B)) as H87.
----------------------------------------------- apply (@proposition__33B.proposition__33B H28 A G B H76 H77 H86).
----------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B H28 G) as H88.
------------------------------------------------ destruct H87 as [H88 H89].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric H28 G A B H88).
------------------------------------------------ assert (* Cut *) (euclidean__defs.Par A B G H28) as H89.
------------------------------------------------- destruct H87 as [H89 H90].
assert (* Cut *) ((euclidean__defs.Par B A H28 G) /\ ((euclidean__defs.Par A B G H28) /\ (euclidean__defs.Par B A G H28))) as H91.
-------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip A B H28 G H88).
-------------------------------------------------- destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H94.
------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par G B E F) /\ (euclidean__defs.Par G F B E)) as H90.
-------------------------------------------------- assert ((euclidean__defs.Par H28 G A B) /\ (euclidean__axioms.Cong H28 G A B)) as H90 by exact H87.
assert ((euclidean__defs.Par H28 G A B) /\ (euclidean__axioms.Cong H28 G A B)) as __TmpHyp by exact H90.
destruct __TmpHyp as [H91 H92].
assert ((euclidean__defs.Par G B E F) /\ (euclidean__defs.Par G F B E)) as H93 by exact H4.
assert ((euclidean__defs.Par G B E F) /\ (euclidean__defs.Par G F B E)) as __TmpHyp0 by exact H93.
destruct __TmpHyp0 as [H94 H95].
assert ((euclidean__defs.Par F G B E) /\ (euclidean__defs.Par F E G B)) as H96 by exact H3.
assert ((euclidean__defs.Par F G B E) /\ (euclidean__defs.Par F E G B)) as __TmpHyp1 by exact H96.
destruct __TmpHyp1 as [H97 H98].
assert ((euclidean__defs.Par E F G B) /\ (euclidean__defs.Par E B F G)) as H99 by exact H2.
assert ((euclidean__defs.Par E F G B) /\ (euclidean__defs.Par E B F G)) as __TmpHyp2 by exact H99.
destruct __TmpHyp2 as [H100 H101].
assert ((euclidean__defs.Par B E F G) /\ (euclidean__defs.Par B G E F)) as H102 by exact H.
assert ((euclidean__defs.Par B E F G) /\ (euclidean__defs.Par B G E F)) as __TmpHyp3 by exact H102.
destruct __TmpHyp3 as [H103 H104].
split.
--------------------------------------------------- exact H94.
--------------------------------------------------- exact H95.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G F E B) as H91.
--------------------------------------------------- destruct H90 as [H91 H92].
destruct H87 as [H93 H94].
assert (* Cut *) ((euclidean__defs.Par F G B E) /\ ((euclidean__defs.Par G F E B) /\ (euclidean__defs.Par F G E B))) as H95.
---------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip G F B E H92).
---------------------------------------------------- destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
exact H98.
--------------------------------------------------- assert (euclidean__axioms.Col A B E) as H92 by exact H13.
assert (* Cut *) (euclidean__axioms.Col E B A) as H93.
---------------------------------------------------- destruct H90 as [H93 H94].
destruct H87 as [H95 H96].
assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H97.
----------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B E H92).
----------------------------------------------------- destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H105.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G F A B) as H94.
----------------------------------------------------- destruct H90 as [H94 H95].
destruct H87 as [H96 H97].
apply (@lemma__collinearparallel.lemma__collinearparallel G F A E B H91 H93 H17).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B G F) as H95.
------------------------------------------------------ destruct H90 as [H95 H96].
destruct H87 as [H97 H98].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric G F A B H94).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col G H28 F) as H96.
------------------------------------------------------- destruct H90 as [H96 H97].
destruct H87 as [H98 H99].
apply (@euclidean__tactics.not__nCol__Col G H28 F).
--------------------------------------------------------intro H100.
apply (@euclidean__tactics.Col__nCol__False G H28 F H100).
---------------------------------------------------------apply (@lemma__Playfair.lemma__Playfair A B G H28 F H89 H95).


------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H28 A B G) as H97.
-------------------------------------------------------- destruct H90 as [H97 H98].
destruct H87 as [H99 H100].
assert (* Cut *) ((euclidean__defs.Par A H28 G B) /\ ((euclidean__defs.Par H28 A B G) /\ (euclidean__defs.Par A H28 B G))) as H101.
--------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip H28 A G B H76).
--------------------------------------------------------- destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H104.
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G B F E) as H98.
--------------------------------------------------------- destruct H90 as [H98 H99].
destruct H87 as [H100 H101].
assert (* Cut *) ((euclidean__defs.Par B G E F) /\ ((euclidean__defs.Par G B F E) /\ (euclidean__defs.Par B G F E))) as H102.
---------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip G B E F H98).
---------------------------------------------------------- destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
exact H105.
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F E G B) as H99.
---------------------------------------------------------- destruct H90 as [H99 H100].
destruct H87 as [H101 H102].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric G B F E H98).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG H28 A B G) as H100.
----------------------------------------------------------- destruct H87 as [H100 H101].
destruct H90 as [H102 H103].
split.
------------------------------------------------------------ exact H97.
------------------------------------------------------------ exact H100.
----------------------------------------------------------- assert (* Cut *) (exists j, (euclidean__axioms.BetS H28 j B) /\ (euclidean__axioms.BetS A j G)) as H101.
------------------------------------------------------------ destruct H90 as [H101 H102].
destruct H87 as [H103 H104].
apply (@lemma__diagonalsmeet.lemma__diagonalsmeet H28 A B G H100).
------------------------------------------------------------ destruct H101 as [j H102].
destruct H102 as [H103 H104].
destruct H90 as [H105 H106].
destruct H87 as [H107 H108].
assert (* Cut *) (exists k, (euclidean__axioms.BetS G k E) /\ (euclidean__axioms.BetS B k F)) as H109.
------------------------------------------------------------- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet G B E F H4).
------------------------------------------------------------- destruct H109 as [k H110].
destruct H110 as [H111 H112].
assert (* Cut *) (euclidean__axioms.BetS E B A) as H113.
-------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry A B E H1).
-------------------------------------------------------------- assert (* Cut *) (E = E) as H114.
--------------------------------------------------------------- apply (@logic.eq__refl Point E).
--------------------------------------------------------------- assert (B = B) as H115 by exact H78.
assert (* Cut *) (A = A) as H116.
---------------------------------------------------------------- apply (@logic.eq__refl Point A).
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F E E) as H117.
----------------------------------------------------------------- right.
right.
left.
exact H114.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G B B) as H118.
------------------------------------------------------------------ right.
right.
left.
exact H115.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H28 A A) as H119.
------------------------------------------------------------------- right.
right.
left.
exact H116.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol F E B) as H120.
-------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F E G) /\ ((euclidean__axioms.nCol F G B) /\ ((euclidean__axioms.nCol E G B) /\ (euclidean__axioms.nCol F E B)))) as H120.
--------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC F E G B H99).
--------------------------------------------------------------------- destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
exact H126.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F E) as H121.
--------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B F)))))) as H121.
---------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct F E B H120).
---------------------------------------------------------------------- destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
exact H122.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G B) as H122.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F E) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq B E) /\ (euclidean__axioms.neq B F)))))) as H122.
----------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct F E B H120).
----------------------------------------------------------------------- destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
exact H7.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H28 A G) as H123.
----------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H28 A B) /\ ((euclidean__axioms.nCol H28 B G) /\ ((euclidean__axioms.nCol A B G) /\ (euclidean__axioms.nCol H28 A G)))) as H123.
------------------------------------------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC H28 A B G H97).
------------------------------------------------------------------------ destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
exact H129.
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H28 A) as H124.
------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq H28 A) /\ ((euclidean__axioms.neq A G) /\ ((euclidean__axioms.neq H28 G) /\ ((euclidean__axioms.neq A H28) /\ ((euclidean__axioms.neq G A) /\ (euclidean__axioms.neq G H28)))))) as H124.
------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct H28 A G H123).
------------------------------------------------------------------------- destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
exact H125.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par H28 A F E) as H125.
------------------------------------------------------------------------- apply (@proposition__30.proposition__30 H28 A F E G B A B E H76 H99 H1 H119 H118 H117 H124 H122 H121).
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G B F E) as H126.
-------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong G F B E) /\ ((euclidean__axioms.Cong G B F E) /\ ((euclidean__defs.CongA B G F F E B) /\ ((euclidean__defs.CongA G F E E B G) /\ (euclidean__axioms.Cong__3 B G F F E B))))) as H126.
--------------------------------------------------------------------------- apply (@proposition__34.proposition__34 G F B E H4).
--------------------------------------------------------------------------- destruct H126 as [H127 H128].
destruct H128 as [H129 H130].
destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
exact H129.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H28 A F E) as H127.
--------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive H28 A G B F E H77 H126).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G F B E) as H128.
---------------------------------------------------------------------------- destruct H100 as [H128 H129].
destruct H4 as [H130 H131].
destruct H3 as [H132 H133].
destruct H2 as [H134 H135].
destruct H as [H136 H137].
exact H106.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H28 G A B) as H129.
----------------------------------------------------------------------------- destruct H100 as [H129 H130].
destruct H4 as [H131 H132].
destruct H3 as [H133 H134].
destruct H2 as [H135 H136].
destruct H as [H137 H138].
exact H130.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B E G F) as H130.
------------------------------------------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric G F B E H128).
------------------------------------------------------------------------------ assert (euclidean__defs.Par A B H28 G) as H131 by exact H88.
assert (* Cut *) (euclidean__defs.TP B E G F) as H132.
------------------------------------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B B E G F H130).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP A B H28 G) as H133.
-------------------------------------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B A B H28 G H131).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS G F B E) as H134.
--------------------------------------------------------------------------------- destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H132 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
exact H145.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS H28 G A B) as H135.
---------------------------------------------------------------------------------- destruct H133 as [H135 H136].
destruct H136 as [H137 H138].
destruct H138 as [H139 H140].
destruct H132 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
exact H140.
---------------------------------------------------------------------------------- assert (euclidean__axioms.Col A B E) as H136 by exact H92.
assert (* Cut *) (euclidean__axioms.neq A E) as H137.
----------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H137.
------------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal A B E H1).
------------------------------------------------------------------------------------ destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
exact H141.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS H28 G A E) as H138.
------------------------------------------------------------------------------------ apply (@lemma__samesidecollinear.lemma__samesidecollinear A B E H28 G H135 H136 H137).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.OS G F E B) as H139.
------------------------------------------------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip B E G F H134).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E B A) as H140.
-------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H140.
--------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B E H136).
--------------------------------------------------------------------------------------- destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
exact H148.
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E A) as H141.
--------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A E H137).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS G F E A) as H142.
---------------------------------------------------------------------------------------- apply (@lemma__samesidecollinear.lemma__samesidecollinear E B A G F H139 H140 H141).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS G F A E) as H143.
----------------------------------------------------------------------------------------- apply (@lemma__samesideflip.lemma__samesideflip E A G F H142).
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS H28 F A E) as H144.
------------------------------------------------------------------------------------------ apply (@lemma__samesidetransitive.lemma__samesidetransitive A E H28 G F H138 H143).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par H28 F A E) as H145.
------------------------------------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C D0, (euclidean__defs.Par A0 B0 C D0) -> ((euclidean__axioms.Cong A0 B0 C D0) -> ((euclidean__defs.OS A0 C B0 D0) -> (euclidean__defs.Par A0 C B0 D0)))) as H145.
-------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C.
intro D0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.Par A0 C B0 D0) /\ (euclidean__axioms.Cong A0 C B0 D0)) as __2.
--------------------------------------------------------------------------------------------- apply (@proposition__33B.proposition__33B A0 B0 C D0 __ __0 __1).
--------------------------------------------------------------------------------------------- destruct __2 as [__2 __3].
exact __2.
-------------------------------------------------------------------------------------------- apply (@H145 H28 A F E H125 H127 H144).
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H28 A E F) as H146.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par A H28 F E) /\ ((euclidean__defs.Par H28 A E F) /\ (euclidean__defs.Par A H28 E F))) as H146.
--------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip H28 A F E H125).
--------------------------------------------------------------------------------------------- destruct H146 as [H147 H148].
destruct H148 as [H149 H150].
exact H149.
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG H28 A E F) as H147.
--------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------- exact H146.
---------------------------------------------------------------------------------------------- exact H145.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H28 F E) as H148.
---------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H28 F A) /\ ((euclidean__axioms.nCol H28 A E) /\ ((euclidean__axioms.nCol F A E) /\ (euclidean__axioms.nCol H28 F E)))) as H148.
----------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC H28 F A E H145).
----------------------------------------------------------------------------------------------- destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
exact H154.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E F H28) as H149.
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol F H28 E) /\ ((euclidean__axioms.nCol F E H28) /\ ((euclidean__axioms.nCol E H28 F) /\ ((euclidean__axioms.nCol H28 E F) /\ (euclidean__axioms.nCol E F H28))))) as H149.
------------------------------------------------------------------------------------------------ apply (@lemma__NCorder.lemma__NCorder H28 F E H148).
------------------------------------------------------------------------------------------------ destruct H149 as [H150 H151].
destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
exact H157.
----------------------------------------------------------------------------------------------- assert (* Cut *) (exists t, (euclidean__defs.Midpoint H28 t E) /\ (euclidean__defs.Midpoint A t F)) as H150.
------------------------------------------------------------------------------------------------ apply (@lemma__diagonalsbisect.lemma__diagonalsbisect H28 A E F H147).
------------------------------------------------------------------------------------------------ destruct H150 as [t H151].
destruct H151 as [H152 H153].
assert (* Cut *) ((euclidean__axioms.BetS H28 t E) /\ (euclidean__axioms.Cong H28 t t E)) as H154.
------------------------------------------------------------------------------------------------- assert ((euclidean__axioms.BetS A t F) /\ (euclidean__axioms.Cong A t t F)) as H154 by exact H153.
assert ((euclidean__axioms.BetS A t F) /\ (euclidean__axioms.Cong A t t F)) as __TmpHyp by exact H154.
destruct __TmpHyp as [H155 H156].
assert ((euclidean__axioms.BetS H28 t E) /\ (euclidean__axioms.Cong H28 t t E)) as H157 by exact H152.
assert ((euclidean__axioms.BetS H28 t E) /\ (euclidean__axioms.Cong H28 t t E)) as __TmpHyp0 by exact H157.
destruct __TmpHyp0 as [H158 H159].
split.
-------------------------------------------------------------------------------------------------- exact H158.
-------------------------------------------------------------------------------------------------- exact H159.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS A t F) /\ (euclidean__axioms.Cong A t t F)) as H155.
-------------------------------------------------------------------------------------------------- assert ((euclidean__axioms.BetS H28 t E) /\ (euclidean__axioms.Cong H28 t t E)) as H155 by exact H154.
assert ((euclidean__axioms.BetS H28 t E) /\ (euclidean__axioms.Cong H28 t t E)) as __TmpHyp by exact H155.
destruct __TmpHyp as [H156 H157].
assert ((euclidean__axioms.BetS A t F) /\ (euclidean__axioms.Cong A t t F)) as H158 by exact H153.
assert ((euclidean__axioms.BetS A t F) /\ (euclidean__axioms.Cong A t t F)) as __TmpHyp0 by exact H158.
destruct __TmpHyp0 as [H159 H160].
assert ((euclidean__axioms.BetS H28 t E) /\ (euclidean__axioms.Cong H28 t t E)) as H161 by exact H152.
assert ((euclidean__axioms.BetS H28 t E) /\ (euclidean__axioms.Cong H28 t t E)) as __TmpHyp1 by exact H161.
destruct __TmpHyp1 as [H162 H163].
split.
--------------------------------------------------------------------------------------------------- exact H159.
--------------------------------------------------------------------------------------------------- exact H160.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A t F t) as H156.
--------------------------------------------------------------------------------------------------- destruct H155 as [H156 H157].
destruct H154 as [H158 H159].
assert (* Cut *) ((euclidean__axioms.Cong t A F t) /\ ((euclidean__axioms.Cong t A t F) /\ (euclidean__axioms.Cong A t F t))) as H160.
---------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A t t F H157).
---------------------------------------------------------------------------------------------------- destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
exact H164.
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong H28 t E t) as H157.
---------------------------------------------------------------------------------------------------- destruct H155 as [H157 H158].
destruct H154 as [H159 H160].
assert (* Cut *) ((euclidean__axioms.Cong t H28 E t) /\ ((euclidean__axioms.Cong t H28 t E) /\ (euclidean__axioms.Cong H28 t E t))) as H161.
----------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip H28 t t E H160).
----------------------------------------------------------------------------------------------------- destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
exact H165.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong t A t F) as H158.
----------------------------------------------------------------------------------------------------- destruct H155 as [H158 H159].
destruct H154 as [H160 H161].
assert (* Cut *) ((euclidean__axioms.Cong t A t F) /\ ((euclidean__axioms.Cong t A F t) /\ (euclidean__axioms.Cong A t t F))) as H162.
------------------------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip A t F t H156).
------------------------------------------------------------------------------------------------------ destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
exact H163.
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol H28 E F) as H159.
------------------------------------------------------------------------------------------------------ destruct H155 as [H159 H160].
destruct H154 as [H161 H162].
assert (* Cut *) ((euclidean__axioms.nCol F E H28) /\ ((euclidean__axioms.nCol F H28 E) /\ ((euclidean__axioms.nCol H28 E F) /\ ((euclidean__axioms.nCol E H28 F) /\ (euclidean__axioms.nCol H28 F E))))) as H163.
------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder E F H28 H149).
------------------------------------------------------------------------------------------------------- destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
exact H168.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (exists K, (euclidean__axioms.BetS H28 B K) /\ (euclidean__axioms.BetS F E K)) as H160.
------------------------------------------------------------------------------------------------------- destruct H155 as [H160 H161].
destruct H154 as [H162 H163].
apply (@euclidean__axioms.postulate__Euclid5 B H28 E A F t H160 H162 H1 H157 H158 H159).
------------------------------------------------------------------------------------------------------- destruct H160 as [K H161].
destruct H161 as [H162 H163].
destruct H155 as [H164 H165].
destruct H154 as [H166 H167].
assert (* Cut *) (euclidean__axioms.Col F E K) as H168.
-------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H163.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E F K) as H169.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E F K) /\ ((euclidean__axioms.Col E K F) /\ ((euclidean__axioms.Col K F E) /\ ((euclidean__axioms.Col F K E) /\ (euclidean__axioms.Col K E F))))) as H169.
---------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F E K H168).
---------------------------------------------------------------------------------------------------------- destruct H169 as [H170 H171].
destruct H171 as [H172 H173].
destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
exact H170.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F K) as H170.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E K) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F K))) as H170.
----------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal F E K H163).
----------------------------------------------------------------------------------------------------------- destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
exact H174.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq K F) as H171.
----------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric F K H170).
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H28 A K F) as H172.
------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel H28 A K E F H146 H169 H171).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par H28 A F K) as H173.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par A H28 K F) /\ ((euclidean__defs.Par H28 A F K) /\ (euclidean__defs.Par A H28 F K))) as H173.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip H28 A K F H172).
-------------------------------------------------------------------------------------------------------------- destruct H173 as [H174 H175].
destruct H175 as [H176 H177].
exact H176.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F K H28 A) as H174.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric H28 A F K H173).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F K A H28) as H175.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par K F H28 A) /\ ((euclidean__defs.Par F K A H28) /\ (euclidean__defs.Par K F A H28))) as H175.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip F K H28 A H174).
---------------------------------------------------------------------------------------------------------------- destruct H175 as [H176 H177].
destruct H177 as [H178 H179].
exact H178.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (H28 = H28) as H176.
---------------------------------------------------------------------------------------------------------------- apply (@logic.eq__refl Point H28).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H28 H28) as H177.
----------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H176.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists L, (euclidean__defs.PG H28 L K F) /\ (euclidean__axioms.Col A H28 L)) as H178.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram H28 K F A H28 H175 H177).
------------------------------------------------------------------------------------------------------------------ destruct H178 as [L H179].
destruct H179 as [H180 H181].
assert (* Cut *) (euclidean__defs.Par H28 L K F) as H182.
------------------------------------------------------------------------------------------------------------------- destruct H180 as [H182 H183].
destruct H147 as [H184 H185].
destruct H100 as [H186 H187].
destruct H4 as [H188 H189].
destruct H3 as [H190 H191].
destruct H2 as [H192 H193].
destruct H as [H194 H195].
exact H182.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol L K F) as H183.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H28 L K) /\ ((euclidean__axioms.nCol H28 K F) /\ ((euclidean__axioms.nCol L K F) /\ (euclidean__axioms.nCol H28 L F)))) as H183.
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC H28 L K F H182).
--------------------------------------------------------------------------------------------------------------------- destruct H183 as [H184 H185].
destruct H185 as [H186 H187].
destruct H187 as [H188 H189].
exact H188.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L K) as H184.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq L K) /\ ((euclidean__axioms.neq K F) /\ ((euclidean__axioms.neq L F) /\ ((euclidean__axioms.neq K L) /\ ((euclidean__axioms.neq F K) /\ (euclidean__axioms.neq F L)))))) as H184.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct L K F H183).
---------------------------------------------------------------------------------------------------------------------- destruct H184 as [H185 H186].
destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
exact H185.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq K L) as H185.
---------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric L K H184).
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G B E F) as H186.
----------------------------------------------------------------------------------------------------------------------- destruct H180 as [H186 H187].
destruct H147 as [H188 H189].
destruct H100 as [H190 H191].
destruct H4 as [H192 H193].
destruct H3 as [H194 H195].
destruct H2 as [H196 H197].
destruct H as [H198 H199].
exact H105.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G B F E) as H187.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par B G E F) /\ ((euclidean__defs.Par G B F E) /\ (euclidean__defs.Par B G F E))) as H187.
------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip G B E F H186).
------------------------------------------------------------------------------------------------------------------------- destruct H187 as [H188 H189].
destruct H189 as [H190 H191].
exact H190.
------------------------------------------------------------------------------------------------------------------------ assert (euclidean__axioms.Col F E E) as H188 by exact H117.
assert (euclidean__axioms.Col F E K) as H189 by exact H168.
assert (* Cut *) (euclidean__axioms.neq E K) as H190.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E K) /\ ((euclidean__axioms.neq F E) /\ (euclidean__axioms.neq F K))) as H190.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal F E K H163).
-------------------------------------------------------------------------------------------------------------------------- destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
exact H191.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G B E K) as H191.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel2.lemma__collinearparallel2 G B F E E K H187 H188 H189 H190).
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E K G B) as H192.
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric G B E K H191).
--------------------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.Col G B B) as H193 by exact H118.
assert (* Cut *) (exists M, (euclidean__defs.PG B M K E) /\ (euclidean__axioms.Col G B M)) as H194.
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__triangletoparallelogram.lemma__triangletoparallelogram B K E G B H192 H193).
---------------------------------------------------------------------------------------------------------------------------- destruct H194 as [M H195].
destruct H195 as [H196 H197].
assert (* Cut *) (euclidean__defs.PG L K F H28) as H198.
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate H28 L K F H180).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG K L H28 F) as H199.
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__PGflip.lemma__PGflip L K F H28 H198).
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.PG L H28 F K) as H200.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate K L H28 F H199).
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG H28 F K L) as H201.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate L H28 F K H200).
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG A H28 G B) as H202.
--------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGflip.lemma__PGflip H28 A B G H100).
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A H28 G B) as H203.
---------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H203 H204].
destruct H201 as [H205 H206].
destruct H200 as [H207 H208].
destruct H199 as [H209 H210].
destruct H198 as [H211 H212].
destruct H196 as [H213 H214].
destruct H180 as [H215 H216].
destruct H147 as [H217 H218].
destruct H100 as [H219 H220].
destruct H4 as [H221 H222].
destruct H3 as [H223 H224].
destruct H2 as [H225 H226].
destruct H as [H227 H228].
exact H203.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (K = K) as H204.
----------------------------------------------------------------------------------------------------------------------------------- apply (@logic.eq__refl Point K).
----------------------------------------------------------------------------------------------------------------------------------- assert (E = E) as H205 by exact H114.
assert (* Cut *) (F = F) as H206.
------------------------------------------------------------------------------------------------------------------------------------ apply (@logic.eq__refl Point F).
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par B E M K) as H207.
------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H207 H208].
destruct H201 as [H209 H210].
destruct H200 as [H211 H212].
destruct H199 as [H213 H214].
destruct H198 as [H215 H216].
destruct H196 as [H217 H218].
destruct H180 as [H219 H220].
destruct H147 as [H221 H222].
destruct H100 as [H223 H224].
destruct H4 as [H225 H226].
destruct H3 as [H227 H228].
destruct H2 as [H229 H230].
destruct H as [H231 H232].
exact H218.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M K B E) as H208.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric B E M K H207).
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par K M E B) as H209.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par K M B E) /\ ((euclidean__defs.Par M K E B) /\ (euclidean__defs.Par K M E B))) as H209.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip M K B E H208).
---------------------------------------------------------------------------------------------------------------------------------------- destruct H209 as [H210 H211].
destruct H211 as [H212 H213].
exact H213.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G F B E) as H210.
---------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H210 H211].
destruct H201 as [H212 H213].
destruct H200 as [H214 H215].
destruct H199 as [H216 H217].
destruct H198 as [H218 H219].
destruct H196 as [H220 H221].
destruct H180 as [H222 H223].
destruct H147 as [H224 H225].
destruct H100 as [H226 H227].
destruct H4 as [H228 H229].
destruct H3 as [H230 H231].
destruct H2 as [H232 H233].
destruct H as [H234 H235].
exact H128.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E M K) as H211.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol B E M) /\ ((euclidean__axioms.nCol B M K) /\ ((euclidean__axioms.nCol E M K) /\ (euclidean__axioms.nCol B E K)))) as H211.
------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC B E M K H207).
------------------------------------------------------------------------------------------------------------------------------------------ destruct H211 as [H212 H213].
destruct H213 as [H214 H215].
destruct H215 as [H216 H217].
exact H216.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B E K) as H212.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol B E M) /\ ((euclidean__axioms.nCol B M K) /\ ((euclidean__axioms.nCol E M K) /\ (euclidean__axioms.nCol B E K)))) as H212.
------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC B E M K H207).
------------------------------------------------------------------------------------------------------------------------------------------- destruct H212 as [H213 H214].
destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
exact H218.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol G F B) as H213.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol G F B) /\ ((euclidean__axioms.nCol G B E) /\ ((euclidean__axioms.nCol F B E) /\ (euclidean__axioms.nCol G F E)))) as H213.
-------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC G F B E H210).
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H213 as [H214 H215].
destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
exact H214.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M K B E) as H214.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par F G B E) /\ ((euclidean__defs.Par G F E B) /\ (euclidean__defs.Par F G E B))) as H214.
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip G F B E H210).
--------------------------------------------------------------------------------------------------------------------------------------------- destruct H214 as [H215 H216].
destruct H216 as [H217 H218].
exact H208.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par G F B E) as H215.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par K M B E) /\ ((euclidean__defs.Par M K E B) /\ (euclidean__defs.Par K M E B))) as H215.
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip M K B E H214).
---------------------------------------------------------------------------------------------------------------------------------------------- destruct H215 as [H216 H217].
destruct H217 as [H218 H219].
exact H210.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS K E F) as H216.
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry F E K H163).
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M K K) as H217.
----------------------------------------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H204.
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B E E) as H218.
------------------------------------------------------------------------------------------------------------------------------------------------ right.
right.
left.
exact H205.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col G F F) as H219.
------------------------------------------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H206.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M K) as H220.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq E M) /\ ((euclidean__axioms.neq M K) /\ ((euclidean__axioms.neq E K) /\ ((euclidean__axioms.neq M E) /\ ((euclidean__axioms.neq K M) /\ (euclidean__axioms.neq K E)))))) as H220.
--------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct E M K H211).
--------------------------------------------------------------------------------------------------------------------------------------------------- destruct H220 as [H221 H222].
destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
exact H223.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B E) as H221.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq E K) /\ ((euclidean__axioms.neq B K) /\ ((euclidean__axioms.neq E B) /\ ((euclidean__axioms.neq K E) /\ (euclidean__axioms.neq K B)))))) as H221.
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct B E K H212).
---------------------------------------------------------------------------------------------------------------------------------------------------- destruct H221 as [H222 H223].
destruct H223 as [H224 H225].
destruct H225 as [H226 H227].
destruct H227 as [H228 H229].
destruct H229 as [H230 H231].
exact H222.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq G F) as H222.
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq G B) /\ ((euclidean__axioms.neq F G) /\ ((euclidean__axioms.neq B F) /\ (euclidean__axioms.neq B G)))))) as H222.
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct G F B H213).
----------------------------------------------------------------------------------------------------------------------------------------------------- destruct H222 as [H223 H224].
destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
exact H223.
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M K G F) as H223.
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__30.proposition__30 M K G F B E K E F H214 H215 H216 H217 H218 H219 H220 H221 H222).
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par K M F G) as H224.
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par K M G F) /\ ((euclidean__defs.Par M K F G) /\ (euclidean__defs.Par K M F G))) as H224.
------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip M K G F H223).
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H224 as [H225 H226].
destruct H226 as [H227 H228].
exact H228.
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par F G K M) as H225.
------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric K M F G H224).
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H28 F L K) as H226.
-------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H226 H227].
destruct H201 as [H228 H229].
destruct H200 as [H230 H231].
destruct H199 as [H232 H233].
destruct H198 as [H234 H235].
destruct H196 as [H236 H237].
destruct H180 as [H238 H239].
destruct H147 as [H240 H241].
destruct H100 as [H242 H243].
destruct H4 as [H244 H245].
destruct H3 as [H246 H247].
destruct H2 as [H248 H249].
destruct H as [H250 H251].
exact H239.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par L K H28 F) as H227.
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric H28 F L K H226).
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par K L H28 F) as H228.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par K L H28 F) /\ ((euclidean__defs.Par L K F H28) /\ (euclidean__defs.Par K L F H28))) as H228.
----------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip L K H28 F H227).
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H228 as [H229 H230].
destruct H230 as [H231 H232].
exact H229.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H28 F G) as H229.
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H28 G F) /\ ((euclidean__axioms.Col H28 F G) /\ ((euclidean__axioms.Col F G H28) /\ ((euclidean__axioms.Col G F H28) /\ (euclidean__axioms.Col F H28 G))))) as H229.
------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder G H28 F H96).
------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H229 as [H230 H231].
destruct H231 as [H232 H233].
destruct H233 as [H234 H235].
destruct H235 as [H236 H237].
exact H232.
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par K L G F) as H230.
------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel K L G H28 F H228 H229 H222).
------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par K L F G) as H231.
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par L K G F) /\ ((euclidean__defs.Par K L F G) /\ (euclidean__defs.Par L K F G))) as H231.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip K L G F H230).
-------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H231 as [H232 H233].
destruct H233 as [H234 H235].
exact H234.
------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par F G K L) as H232.
-------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric K L F G H231).
-------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K M L) as H233.
--------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col K M L).
----------------------------------------------------------------------------------------------------------------------------------------------------------------intro H233.
apply (@euclidean__tactics.Col__nCol__False K M L H233).
-----------------------------------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__Playfair.lemma__Playfair F G K M L H225 H232).


--------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col M K L) as H234.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M K L) /\ ((euclidean__axioms.Col M L K) /\ ((euclidean__axioms.Col L K M) /\ ((euclidean__axioms.Col K L M) /\ (euclidean__axioms.Col L M K))))) as H234.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder K M L H233).
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H234 as [H235 H236].
destruct H236 as [H237 H238].
destruct H238 as [H239 H240].
destruct H240 as [H241 H242].
exact H235.
---------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par B E M K) as H235.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H235 H236].
destruct H201 as [H237 H238].
destruct H200 as [H239 H240].
destruct H199 as [H241 H242].
destruct H198 as [H243 H244].
destruct H196 as [H245 H246].
destruct H180 as [H247 H248].
destruct H147 as [H249 H250].
destruct H100 as [H251 H252].
destruct H4 as [H253 H254].
destruct H3 as [H255 H256].
destruct H2 as [H257 H258].
destruct H as [H259 H260].
exact H207.
----------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.neq L K) as H236 by exact H184.
assert (* Cut *) (euclidean__defs.Par B E L K) as H237.
------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel B E L M K H235 H234 H236).
------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par L K B E) as H238.
------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric B E L K H237).
------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par L K E B) as H239.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par K L B E) /\ ((euclidean__defs.Par L K E B) /\ (euclidean__defs.Par K L E B))) as H239.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip L K B E H238).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H239 as [H240 H241].
destruct H241 as [H242 H243].
exact H242.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.Col A B E) as H240 by exact H136.
assert (* Cut *) (euclidean__axioms.Col E B A) as H241.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H241.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B E H240).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H241 as [H242 H243].
destruct H243 as [H244 H245].
destruct H245 as [H246 H247].
destruct H247 as [H248 H249].
exact H249.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par L K A B) as H242.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel L K A E B H239 H241 H17).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B L K) as H243.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric L K A B H242).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B K L) as H244.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par B A L K) /\ ((euclidean__defs.Par A B K L) /\ (euclidean__defs.Par B A K L))) as H244.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip A B L K H243).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H244 as [H245 H246].
destruct H246 as [H247 H248].
exact H247.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS K B H28) as H245.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry H28 B K H162).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L A H28) as H246.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H28 A L) /\ ((euclidean__axioms.Col H28 L A) /\ ((euclidean__axioms.Col L A H28) /\ ((euclidean__axioms.Col A L H28) /\ (euclidean__axioms.Col L H28 A))))) as H246.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A H28 L H181).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H246 as [H247 H248].
destruct H248 as [H249 H250].
destruct H250 as [H251 H252].
destruct H252 as [H253 H254].
exact H251.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS L A H28) as H247.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelbetween.lemma__parallelbetween B K H28 L A H245 H244 H246).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS H28 A L) as H248.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry L A H28 H247).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H28 A G B) as H249.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par B A K L) /\ ((euclidean__defs.Par A B L K) /\ (euclidean__defs.Par B A L K))) as H249.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip A B K L H244).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H249 as [H250 H251].
destruct H251 as [H252 H253].
exact H76.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B M K) as H250.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol B E M) /\ ((euclidean__axioms.nCol B M K) /\ ((euclidean__axioms.nCol E M K) /\ (euclidean__axioms.nCol B E K)))) as H250.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC B E M K H235).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H250 as [H251 H252].
destruct H252 as [H253 H254].
destruct H254 as [H255 H256].
exact H253.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq M B) as H251.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B M) /\ ((euclidean__axioms.neq M K) /\ ((euclidean__axioms.neq B K) /\ ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq K M) /\ (euclidean__axioms.neq K B)))))) as H251.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct B M K H250).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H251 as [H252 H253].
destruct H253 as [H254 H255].
destruct H255 as [H256 H257].
destruct H257 as [H258 H259].
destruct H259 as [H260 H261].
exact H258.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H28 A M B) as H252.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel H28 A M G B H249 H197 H251).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M B H28 A) as H253.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric H28 A M B H252).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M B A H28) as H254.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par B M H28 A) /\ ((euclidean__defs.Par M B A H28) /\ (euclidean__defs.Par B M A H28))) as H254.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip M B H28 A H253).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H254 as [H255 H256].
destruct H256 as [H257 H258].
exact H257.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A H28 L) as H255.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A L H28) /\ ((euclidean__axioms.Col A H28 L) /\ ((euclidean__axioms.Col H28 L A) /\ ((euclidean__axioms.Col L H28 A) /\ (euclidean__axioms.Col H28 A L))))) as H255.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder L A H28 H246).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H255 as [H256 H257].
destruct H257 as [H258 H259].
destruct H259 as [H260 H261].
destruct H261 as [H262 H263].
exact H258.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H28 L K F) as H256.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H202 as [H256 H257].
destruct H201 as [H258 H259].
destruct H200 as [H260 H261].
destruct H199 as [H262 H263].
destruct H198 as [H264 H265].
destruct H196 as [H266 H267].
destruct H180 as [H268 H269].
destruct H147 as [H270 H271].
destruct H100 as [H272 H273].
destruct H4 as [H274 H275].
destruct H3 as [H276 H277].
destruct H2 as [H278 H279].
destruct H as [H280 H281].
exact H182.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol H28 L K) as H257.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H28 L K) /\ ((euclidean__axioms.nCol H28 K F) /\ ((euclidean__axioms.nCol L K F) /\ (euclidean__axioms.nCol H28 L F)))) as H257.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC H28 L K F H256).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H257 as [H258 H259].
destruct H259 as [H260 H261].
destruct H261 as [H262 H263].
exact H258.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq L H28) as H258.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H28 L) /\ ((euclidean__axioms.neq L K) /\ ((euclidean__axioms.neq H28 K) /\ ((euclidean__axioms.neq L H28) /\ ((euclidean__axioms.neq K L) /\ (euclidean__axioms.neq K H28)))))) as H258.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct H28 L K H257).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H258 as [H259 H260].
destruct H260 as [H261 H262].
destruct H262 as [H263 H264].
destruct H264 as [H265 H266].
destruct H266 as [H267 H268].
exact H265.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M B L H28) as H259.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel M B L A H28 H254 H255 H258).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par M B H28 L) as H260.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par B M L H28) /\ ((euclidean__defs.Par M B H28 L) /\ (euclidean__defs.Par B M H28 L))) as H260.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip M B L H28 H259).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H260 as [H261 H262].
destruct H262 as [H263 H264].
exact H263.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col L M K) as H261.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K M L) /\ ((euclidean__axioms.Col K L M) /\ ((euclidean__axioms.Col L M K) /\ ((euclidean__axioms.Col M L K) /\ (euclidean__axioms.Col L K M))))) as H261.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder M K L H234).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H261 as [H262 H263].
destruct H263 as [H264 H265].
destruct H265 as [H266 H267].
destruct H267 as [H268 H269].
exact H266.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS L M K) as H262.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelbetween.lemma__parallelbetween B H28 K L M H162 H260 H261).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par G B E F) as H263.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H202 as [H263 H264].
destruct H201 as [H265 H266].
destruct H200 as [H267 H268].
destruct H199 as [H269 H270].
destruct H198 as [H271 H272].
destruct H196 as [H273 H274].
destruct H180 as [H275 H276].
destruct H147 as [H277 H278].
destruct H100 as [H279 H280].
destruct H4 as [H281 H282].
destruct H3 as [H283 H284].
destruct H2 as [H285 H286].
destruct H as [H287 H288].
exact H186.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.Col F E K) as H264 by exact H189.
assert (* Cut *) (euclidean__axioms.Col E F K) as H265.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E F K) /\ ((euclidean__axioms.Col E K F) /\ ((euclidean__axioms.Col K F E) /\ ((euclidean__axioms.Col F K E) /\ (euclidean__axioms.Col K E F))))) as H265.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder F E K H264).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H265 as [H266 H267].
destruct H267 as [H268 H269].
destruct H269 as [H270 H271].
destruct H271 as [H272 H273].
exact H266.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F K) as H266.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M K) /\ ((euclidean__axioms.neq L M) /\ (euclidean__axioms.neq L K))) as H266.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal L M K H262).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H266 as [H267 H268].
destruct H268 as [H269 H270].
exact H170.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (euclidean__axioms.neq K F) as H267 by exact H171.
assert (* Cut *) (euclidean__defs.Par G B K F) as H268.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel G B K E F H263 H265 H267).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F G H28) as H269.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F H28 G) /\ ((euclidean__axioms.Col F G H28) /\ ((euclidean__axioms.Col G H28 F) /\ ((euclidean__axioms.Col H28 G F) /\ (euclidean__axioms.Col G F H28))))) as H269.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder H28 F G H229).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H269 as [H270 H271].
destruct H271 as [H272 H273].
destruct H273 as [H274 H275].
destruct H275 as [H276 H277].
exact H272.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F G H28) as H270.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelbetween.lemma__parallelbetween B K H28 F G H245 H268 H269).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS H28 G F) as H271.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry F G H28 H270).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG A B G H28) as H272.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate H28 A B G H100).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG B G H28 A) as H273.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate A B G H28 H272).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG G H28 A B) as H274.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate B G H28 A H273).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG M K E B) as H275.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate B M K E H196).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG K E B M) as H276.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__PGrotate.lemma__PGrotate M K E B H275).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.PG E B M K) as H277.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGrotate.lemma__PGrotate K E B M H276).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.EF B E F G L M B A) as H278.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__43.proposition__43 H28 F K L G M E A B H201 H248 H271 H262 H163 H162 H274 H277).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (euclidean__defs.PG A H28 G B) as H279 by exact H202.
assert (* Cut *) (euclidean__defs.PG M B E K) as H280.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__PGflip.lemma__PGflip B M K E H196).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG A B M L) as H281.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__43B.proposition__43B H28 L K F A E M G B H180 H271 H248 H163 H262 H279 H280).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col H28 G F) as H282.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col G F H28) /\ ((euclidean__axioms.Col G H28 F) /\ ((euclidean__axioms.Col H28 F G) /\ ((euclidean__axioms.Col F H28 G) /\ (euclidean__axioms.Col H28 G F))))) as H282.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder F G H28 H269).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H282 as [H283 H284].
destruct H284 as [H285 H286].
destruct H286 as [H287 H288].
destruct H288 as [H289 H290].
exact H290.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H28 F) as H283.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq H28 G) /\ (euclidean__axioms.neq H28 F))) as H283.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H28 G F H271).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H283 as [H284 H285].
destruct H285 as [H286 H287].
exact H287.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq L K) as H284.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq H28 G) /\ (euclidean__axioms.neq H28 F))) as H284.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H28 G F H271).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H284 as [H285 H286].
destruct H286 as [H287 H288].
exact H236.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H28 G) as H285.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq H28 G) /\ (euclidean__axioms.neq H28 F))) as H285.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H28 G F H271).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H285 as [H286 H287].
destruct H287 as [H288 H289].
exact H288.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M K) as H286.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq G F) /\ ((euclidean__axioms.neq H28 G) /\ (euclidean__axioms.neq H28 F))) as H286.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal H28 G F H271).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H286 as [H287 H288].
destruct H288 as [H289 H290].
exact H220.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H28 F L K) as H287.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H281 as [H287 H288].
destruct H280 as [H289 H290].
destruct H279 as [H291 H292].
destruct H277 as [H293 H294].
destruct H276 as [H295 H296].
destruct H275 as [H297 H298].
destruct H274 as [H299 H300].
destruct H273 as [H301 H302].
destruct H272 as [H303 H304].
destruct H202 as [H305 H306].
destruct H201 as [H307 H308].
destruct H200 as [H309 H310].
destruct H199 as [H311 H312].
destruct H198 as [H313 H314].
destruct H196 as [H315 H316].
destruct H180 as [H317 H318].
destruct H147 as [H319 H320].
destruct H100 as [H321 H322].
destruct H4 as [H323 H324].
destruct H3 as [H325 H326].
destruct H2 as [H327 H328].
destruct H as [H329 H330].
exact H226.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet H28 F L K)) as H288.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (exists U V u v X, (euclidean__axioms.neq H28 F) /\ ((euclidean__axioms.neq L K) /\ ((euclidean__axioms.Col H28 F U) /\ ((euclidean__axioms.Col H28 F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col L K u) /\ ((euclidean__axioms.Col L K v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H28 F L K)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H288 by exact H287.
assert (exists U V u v X, (euclidean__axioms.neq H28 F) /\ ((euclidean__axioms.neq L K) /\ ((euclidean__axioms.Col H28 F U) /\ ((euclidean__axioms.Col H28 F V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col L K u) /\ ((euclidean__axioms.Col L K v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet H28 F L K)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H288.
destruct __TmpHyp as [x H289].
destruct H289 as [x0 H290].
destruct H290 as [x1 H291].
destruct H291 as [x2 H292].
destruct H292 as [x3 H293].
destruct H293 as [H294 H295].
destruct H295 as [H296 H297].
destruct H297 as [H298 H299].
destruct H299 as [H300 H301].
destruct H301 as [H302 H303].
destruct H303 as [H304 H305].
destruct H305 as [H306 H307].
destruct H307 as [H308 H309].
destruct H309 as [H310 H311].
destruct H311 as [H312 H313].
exact H310.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col G M B) as H289.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B G M) /\ ((euclidean__axioms.Col B M G) /\ ((euclidean__axioms.Col M G B) /\ ((euclidean__axioms.Col G M B) /\ (euclidean__axioms.Col M B G))))) as H289.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G B M H197).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H289 as [H290 H291].
destruct H291 as [H292 H293].
destruct H293 as [H294 H295].
destruct H295 as [H296 H297].
exact H296.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS G B M) as H290.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween H28 F L K G M B H282 H261 H283 H284 H285 H286 H288 H162 H289).
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B M G B E) as H291.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (forall A0 B0 C D0 E0, (euclidean__axioms.BetS A0 E0 B0) -> ((euclidean__axioms.BetS C E0 D0) -> ((euclidean__axioms.nCol A0 E0 C) -> (euclidean__defs.CongA C E0 B0 A0 E0 D0)))) as H291.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C.
intro D0.
intro E0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.CongA A0 E0 C D0 E0 B0) /\ (euclidean__defs.CongA C E0 B0 A0 E0 D0)) as __2.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__15.proposition__15 A0 B0 C D0 E0 __ __0 __1).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct __2 as [__2 __3].
exact __3.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@H291 G M A E B H290 H1 H20).
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA G B E E B G) as H292.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA G B E H6).
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B M E B G) as H293.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B M G B E E B G H291 H292).
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B M J D N) as H294.
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B M E B G J D N H293 H0).
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exists M.
exists L.
split.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H281.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H294.
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H278.
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- exact H290.
Qed.
