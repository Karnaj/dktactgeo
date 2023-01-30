Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__PGsymmetric.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel2.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Require Export proposition__33.
Require Export proposition__34.
Require Export proposition__35.
Definition proposition__36A : forall A B C D E F G H M, (euclidean__defs.PG A B C D) -> ((euclidean__defs.PG E F G H) -> ((euclidean__axioms.Col A D E) -> ((euclidean__axioms.Col A D H) -> ((euclidean__axioms.Col B C F) -> ((euclidean__axioms.Col B C G) -> ((euclidean__axioms.Cong B C F G) -> ((euclidean__axioms.BetS B M H) -> ((euclidean__axioms.BetS C M E) -> (euclidean__axioms.EF A B C D E F G H))))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
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
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H9.
- assert ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H9 by exact H1.
assert ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as __TmpHyp by exact H9.
destruct __TmpHyp as [H10 H11].
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H12 by exact H0.
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp0 by exact H12.
destruct __TmpHyp0 as [H13 H14].
split.
-- exact H13.
-- exact H14.
- assert (* Cut *) ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H10.
-- assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H10 by exact H9.
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp by exact H10.
destruct __TmpHyp as [H11 H12].
assert ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as H13 by exact H1.
assert ((euclidean__defs.Par E F G H) /\ (euclidean__defs.Par E H F G)) as __TmpHyp0 by exact H13.
destruct __TmpHyp0 as [H14 H15].
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H16 by exact H0.
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp1 by exact H16.
destruct __TmpHyp1 as [H17 H18].
split.
--- exact H14.
--- exact H15.
-- assert (* Cut *) (euclidean__axioms.nCol A C D) as H11.
--- destruct H10 as [H11 H12].
destruct H9 as [H13 H14].
assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H15.
---- apply (@lemma__parallelNC.lemma__parallelNC A B C D H13).
---- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H18.
--- assert (* Cut *) (euclidean__axioms.neq A D) as H12.
---- destruct H10 as [H12 H13].
destruct H9 as [H14 H15].
assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))))) as H16.
----- apply (@lemma__NCdistinct.lemma__NCdistinct A C D H11).
----- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H21.
---- assert (* Cut *) (euclidean__axioms.Cong A D B C) as H13.
----- destruct H10 as [H13 H14].
destruct H9 as [H15 H16].
assert (* Cut *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H17.
------ apply (@proposition__34.proposition__34 A D B C H0).
------ destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H18.
----- assert (* Cut *) (euclidean__axioms.Cong E H F G) as H14.
------ destruct H10 as [H14 H15].
destruct H9 as [H16 H17].
assert (* Cut *) ((euclidean__axioms.Cong E H F G) /\ ((euclidean__axioms.Cong E F H G) /\ ((euclidean__defs.CongA F E H H G F) /\ ((euclidean__defs.CongA E H G G F E) /\ (euclidean__axioms.Cong__3 F E H H G F))))) as H18.
------- apply (@proposition__34.proposition__34 E H F G H1).
------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H19.
------ assert (* Cut *) (euclidean__axioms.Cong F G E H) as H15.
------- destruct H10 as [H15 H16].
destruct H9 as [H17 H18].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric F E H G H14).
------- assert (* Cut *) (euclidean__axioms.Cong B C E H) as H16.
-------- destruct H10 as [H16 H17].
destruct H9 as [H18 H19].
apply (@lemma__congruencetransitive.lemma__congruencetransitive B C F G E H H6 H15).
-------- assert (* Cut *) (euclidean__defs.Par B C A D) as H17.
--------- destruct H10 as [H17 H18].
destruct H9 as [H19 H20].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A D B C H20).
--------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H18.
---------- destruct H10 as [H18 H19].
destruct H9 as [H20 H21].
assert (* Cut *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol D B C) /\ (euclidean__axioms.nCol A D C)))) as H22.
----------- apply (@lemma__parallelNC.lemma__parallelNC A D B C H21).
----------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H25.
---------- assert (* Cut *) (euclidean__axioms.neq B C) as H19.
----------- destruct H10 as [H19 H20].
destruct H9 as [H21 H22].
assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H23.
------------ apply (@lemma__NCdistinct.lemma__NCdistinct A B C H18).
------------ destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H26.
----------- assert (* Cut *) (euclidean__axioms.neq E H) as H20.
------------ destruct H10 as [H20 H21].
destruct H9 as [H22 H23].
apply (@euclidean__axioms.axiom__nocollapse B C E H H19 H16).
------------ assert (* Cut *) (euclidean__defs.Par B C E H) as H21.
------------- destruct H10 as [H21 H22].
destruct H9 as [H23 H24].
apply (@lemma__collinearparallel2.lemma__collinearparallel2 B C A D E H H17 H2 H3 H20).
------------- assert (* Cut *) ((euclidean__defs.Par B E C H) /\ (euclidean__axioms.Cong B E C H)) as H22.
-------------- destruct H10 as [H22 H23].
destruct H9 as [H24 H25].
apply (@proposition__33.proposition__33 B C E H M H21 H16 H7 H8).
-------------- assert (* Cut *) (euclidean__defs.Par E B C H) as H23.
--------------- destruct H22 as [H23 H24].
destruct H10 as [H25 H26].
destruct H9 as [H27 H28].
assert (* Cut *) ((euclidean__defs.Par E B C H) /\ ((euclidean__defs.Par B E H C) /\ (euclidean__defs.Par E B H C))) as H29.
---------------- apply (@lemma__parallelflip.lemma__parallelflip B E C H H23).
---------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H30.
--------------- assert (* Cut *) (euclidean__defs.Par E H B C) as H24.
---------------- destruct H22 as [H24 H25].
destruct H10 as [H26 H27].
destruct H9 as [H28 H29].
apply (@lemma__parallelsymmetric.lemma__parallelsymmetric B C E H H21).
---------------- assert (* Cut *) (euclidean__defs.PG E B C H) as H25.
----------------- split.
------------------ exact H23.
------------------ exact H24.
----------------- assert (* Cut *) (euclidean__axioms.EF A B C D E B C H) as H26.
------------------ destruct H22 as [H26 H27].
destruct H10 as [H28 H29].
destruct H9 as [H30 H31].
apply (@proposition__35.proposition__35 A B C D E H H0 H25 H2 H3).
------------------ assert (* Cut *) (euclidean__axioms.Cong F G B C) as H27.
------------------- destruct H22 as [H27 H28].
destruct H10 as [H29 H30].
destruct H9 as [H31 H32].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric F B C G H6).
------------------- assert (* Cut *) (euclidean__axioms.Cong G F C B) as H28.
-------------------- destruct H22 as [H28 H29].
destruct H10 as [H30 H31].
destruct H9 as [H32 H33].
assert (* Cut *) ((euclidean__axioms.Cong G F C B) /\ ((euclidean__axioms.Cong G F B C) /\ (euclidean__axioms.Cong F G C B))) as H34.
--------------------- apply (@lemma__congruenceflip.lemma__congruenceflip F G B C H27).
--------------------- destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H35.
-------------------- assert (* Cut *) (euclidean__defs.PG C H E B) as H29.
--------------------- destruct H22 as [H29 H30].
destruct H10 as [H31 H32].
destruct H9 as [H33 H34].
apply (@lemma__PGsymmetric.lemma__PGsymmetric E B C H H25).
--------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H30.
---------------------- destruct H22 as [H30 H31].
destruct H10 as [H32 H33].
destruct H9 as [H34 H35].
assert (* Cut *) ((euclidean__axioms.nCol E H B) /\ ((euclidean__axioms.nCol E B C) /\ ((euclidean__axioms.nCol H B C) /\ (euclidean__axioms.nCol E H C)))) as H36.
----------------------- apply (@lemma__parallelNC.lemma__parallelNC E H B C H24).
----------------------- destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
exact H18.
---------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H31.
----------------------- destruct H22 as [H31 H32].
destruct H10 as [H33 H34].
destruct H9 as [H35 H36].
assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H37.
------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct A B C H30).
------------------------ destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H40.
----------------------- assert (* Cut *) (euclidean__axioms.neq C B) as H32.
------------------------ destruct H22 as [H32 H33].
destruct H10 as [H34 H35].
destruct H9 as [H36 H37].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B C H31).
------------------------ assert (* Cut *) (euclidean__axioms.Col C F G) as H33.
------------------------- destruct H22 as [H33 H34].
destruct H10 as [H35 H36].
destruct H9 as [H37 H38].
apply (@euclidean__tactics.not__nCol__Col C F G).
--------------------------intro H39.
apply (@euclidean__tactics.Col__nCol__False C F G H39).
---------------------------apply (@lemma__collinear4.lemma__collinear4 B C F G H4 H5 H31).


------------------------- assert (* Cut *) (euclidean__axioms.Col G F C) as H34.
-------------------------- destruct H22 as [H34 H35].
destruct H10 as [H36 H37].
destruct H9 as [H38 H39].
assert (* Cut *) ((euclidean__axioms.Col F C G) /\ ((euclidean__axioms.Col F G C) /\ ((euclidean__axioms.Col G C F) /\ ((euclidean__axioms.Col C G F) /\ (euclidean__axioms.Col G F C))))) as H40.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder C F G H33).
--------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H48.
-------------------------- assert (* Cut *) (euclidean__axioms.Col C B F) as H35.
--------------------------- destruct H22 as [H35 H36].
destruct H10 as [H37 H38].
destruct H9 as [H39 H40].
assert (* Cut *) ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col C F B) /\ ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col B F C) /\ (euclidean__axioms.Col F C B))))) as H41.
---------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C F H4).
---------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H42.
--------------------------- assert (* Cut *) (euclidean__axioms.Col C B G) as H36.
---------------------------- destruct H22 as [H36 H37].
destruct H10 as [H38 H39].
destruct H9 as [H40 H41].
assert (* Cut *) ((euclidean__axioms.Col C B G) /\ ((euclidean__axioms.Col C G B) /\ ((euclidean__axioms.Col G B C) /\ ((euclidean__axioms.Col B G C) /\ (euclidean__axioms.Col G C B))))) as H42.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C G H5).
----------------------------- destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H43.
---------------------------- assert (* Cut *) (euclidean__axioms.Col B F G) as H37.
----------------------------- destruct H22 as [H37 H38].
destruct H10 as [H39 H40].
destruct H9 as [H41 H42].
apply (@euclidean__tactics.not__nCol__Col B F G).
------------------------------intro H43.
apply (@euclidean__tactics.Col__nCol__False B F G H43).
-------------------------------apply (@lemma__collinear4.lemma__collinear4 C B F G H35 H36 H32).


----------------------------- assert (* Cut *) (euclidean__axioms.Col G F B) as H38.
------------------------------ destruct H22 as [H38 H39].
destruct H10 as [H40 H41].
destruct H9 as [H42 H43].
assert (* Cut *) ((euclidean__axioms.Col F B G) /\ ((euclidean__axioms.Col F G B) /\ ((euclidean__axioms.Col G B F) /\ ((euclidean__axioms.Col B G F) /\ (euclidean__axioms.Col G F B))))) as H44.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B F G H37).
------------------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H52.
------------------------------ assert (* Cut *) (euclidean__defs.PG G H E F) as H39.
------------------------------- destruct H22 as [H39 H40].
destruct H10 as [H41 H42].
destruct H9 as [H43 H44].
apply (@lemma__PGsymmetric.lemma__PGsymmetric E F G H H1).
------------------------------- assert (* Cut *) (euclidean__axioms.EF G H E F C H E B) as H40.
-------------------------------- destruct H22 as [H40 H41].
destruct H10 as [H42 H43].
destruct H9 as [H44 H45].
apply (@proposition__35.proposition__35 G H E F C B H39 H29 H34 H38).
-------------------------------- assert (* Cut *) (euclidean__axioms.EF G H E F E B C H) as H41.
--------------------------------- destruct H22 as [H41 H42].
destruct H10 as [H43 H44].
destruct H9 as [H45 H46].
assert (* Cut *) ((euclidean__axioms.EF G H E F H E B C) /\ ((euclidean__axioms.EF G H E F B E H C) /\ ((euclidean__axioms.EF G H E F E B C H) /\ ((euclidean__axioms.EF G H E F H C B E) /\ ((euclidean__axioms.EF G H E F B C H E) /\ ((euclidean__axioms.EF G H E F E H C B) /\ (euclidean__axioms.EF G H E F C B E H))))))) as H47.
---------------------------------- apply (@euclidean__axioms.axiom__EFpermutation G H E F C H E B H40).
---------------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H52.
--------------------------------- assert (* Cut *) (euclidean__axioms.EF E B C H G H E F) as H42.
---------------------------------- destruct H22 as [H42 H43].
destruct H10 as [H44 H45].
destruct H9 as [H46 H47].
apply (@euclidean__axioms.axiom__EFsymmetric G H E F E B C H H41).
---------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D G H E F) as H43.
----------------------------------- destruct H22 as [H43 H44].
destruct H10 as [H45 H46].
destruct H9 as [H47 H48].
apply (@euclidean__axioms.axiom__EFtransitive A B C D G H E F E B C H H26 H42).
----------------------------------- assert (* Cut *) (euclidean__axioms.EF A B C D E F G H) as H44.
------------------------------------ destruct H22 as [H44 H45].
destruct H10 as [H46 H47].
destruct H9 as [H48 H49].
assert (* Cut *) ((euclidean__axioms.EF A B C D H E F G) /\ ((euclidean__axioms.EF A B C D F E H G) /\ ((euclidean__axioms.EF A B C D E F G H) /\ ((euclidean__axioms.EF A B C D H G F E) /\ ((euclidean__axioms.EF A B C D F G H E) /\ ((euclidean__axioms.EF A B C D E H G F) /\ (euclidean__axioms.EF A B C D G F E H))))))) as H50.
------------------------------------- apply (@euclidean__axioms.axiom__EFpermutation A B C D G H E F H43).
------------------------------------- destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H55.
------------------------------------ exact H44.
Qed.
