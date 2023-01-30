Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__Euclid4.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennesspreserved.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearright.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__diagonalsbisect.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglessymmetric.
Require Export lemma__extension.
Require Export lemma__layoffunique.
Require Export lemma__oppositesideflip.
Require Export lemma__ray4.
Require Export lemma__rightangleNC.
Require Export lemma__righttogether.
Require Export logic.
Require Export proposition__04.
Require Export proposition__46.
Definition lemma__squareparallelogram : forall A B C D, (euclidean__defs.SQ A B C D) -> (euclidean__defs.PG A B C D).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H0.
- assert ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H0 by exact H.
assert ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as __TmpHyp by exact H0.
destruct __TmpHyp as [H1 H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
split.
-- exact H1.
-- split.
--- exact H3.
--- split.
---- exact H5.
---- split.
----- exact H7.
----- split.
------ exact H9.
------ split.
------- exact H11.
------- exact H12.
- assert (* Cut *) (euclidean__axioms.nCol D A B) as H1.
-- destruct H0 as [H1 H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
apply (@lemma__rightangleNC.lemma__rightangleNC D A B H7).
-- assert (* Cut *) (euclidean__axioms.neq D A) as H2.
--- destruct H0 as [H2 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
assert (* Cut *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B D)))))) as H14.
---- apply (@lemma__NCdistinct.lemma__NCdistinct D A B H1).
---- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H15.
--- assert (* Cut *) (exists R, (euclidean__axioms.BetS D A R) /\ (euclidean__axioms.Cong A R D A)) as H3.
---- destruct H0 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
apply (@lemma__extension.lemma__extension D A D A H2 H2).
---- destruct H3 as [R H4].
destruct H4 as [H5 H6].
destruct H0 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
assert (* Cut *) (euclidean__axioms.BetS R A D) as H19.
----- apply (@euclidean__axioms.axiom__betweennesssymmetry D A R H5).
----- assert (* Cut *) (euclidean__axioms.neq A B) as H20.
------ assert (* Cut *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B D)))))) as H20.
------- apply (@lemma__NCdistinct.lemma__NCdistinct D A B H1).
------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H23.
------ assert (* Cut *) (euclidean__axioms.Col D A R) as H21.
------- right.
right.
right.
right.
left.
exact H5.
------- assert (* Cut *) (A = A) as H22.
-------- apply (@logic.eq__refl Point A).
-------- assert (* Cut *) (euclidean__axioms.Col D A A) as H23.
--------- right.
right.
left.
exact H22.
--------- assert (* Cut *) (euclidean__axioms.neq R A) as H24.
---------- assert (* Cut *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq R A) /\ (euclidean__axioms.neq R D))) as H24.
----------- apply (@lemma__betweennotequal.lemma__betweennotequal R A D H19).
----------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H27.
---------- assert (* Cut *) (euclidean__axioms.nCol R A B) as H25.
----------- apply (@euclidean__tactics.nCol__notCol R A B).
------------apply (@euclidean__tactics.nCol__not__Col R A B).
-------------apply (@lemma__NChelper.lemma__NChelper D A B R A H1 H21 H23 H24).


----------- assert (* Cut *) (euclidean__axioms.nCol A B R) as H26.
------------ assert (* Cut *) ((euclidean__axioms.nCol A R B) /\ ((euclidean__axioms.nCol A B R) /\ ((euclidean__axioms.nCol B R A) /\ ((euclidean__axioms.nCol R B A) /\ (euclidean__axioms.nCol B A R))))) as H26.
------------- apply (@lemma__NCorder.lemma__NCorder R A B H25).
------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H29.
------------ assert (* Cut *) (exists c E, (euclidean__defs.SQ A B c E) /\ ((euclidean__axioms.TS E A B R) /\ (euclidean__defs.PG A B c E))) as H27.
------------- apply (@proposition__46.proposition__46 A B R H20 H26).
------------- destruct H27 as [c H28].
destruct H28 as [E H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
assert (* Cut *) ((euclidean__axioms.Cong A B c E) /\ ((euclidean__axioms.Cong A B B c) /\ ((euclidean__axioms.Cong A B E A) /\ ((euclidean__defs.Per E A B) /\ ((euclidean__defs.Per A B c) /\ ((euclidean__defs.Per B c E) /\ (euclidean__defs.Per c E A))))))) as H34.
-------------- assert ((euclidean__axioms.Cong A B c E) /\ ((euclidean__axioms.Cong A B B c) /\ ((euclidean__axioms.Cong A B E A) /\ ((euclidean__defs.Per E A B) /\ ((euclidean__defs.Per A B c) /\ ((euclidean__defs.Per B c E) /\ (euclidean__defs.Per c E A))))))) as H34 by exact H30.
assert ((euclidean__axioms.Cong A B c E) /\ ((euclidean__axioms.Cong A B B c) /\ ((euclidean__axioms.Cong A B E A) /\ ((euclidean__defs.Per E A B) /\ ((euclidean__defs.Per A B c) /\ ((euclidean__defs.Per B c E) /\ (euclidean__defs.Per c E A))))))) as __TmpHyp by exact H34.
destruct __TmpHyp as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
assert ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H47 by exact H.
assert ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as __TmpHyp0 by exact H47.
destruct __TmpHyp0 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
split.
--------------- exact H35.
--------------- split.
---------------- exact H37.
---------------- split.
----------------- exact H39.
----------------- split.
------------------ exact H41.
------------------ split.
------------------- exact H43.
------------------- split.
-------------------- exact H45.
-------------------- exact H46.
-------------- assert (* Cut *) (euclidean__axioms.Col R A D) as H35.
--------------- right.
right.
right.
right.
left.
exact H19.
--------------- assert (* Cut *) (euclidean__axioms.Col D A R) as H36.
---------------- destruct H34 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
assert (* Cut *) ((euclidean__axioms.Col A R D) /\ ((euclidean__axioms.Col A D R) /\ ((euclidean__axioms.Col D R A) /\ ((euclidean__axioms.Col R D A) /\ (euclidean__axioms.Col D A R))))) as H48.
----------------- apply (@lemma__collinearorder.lemma__collinearorder R A D H35).
----------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H56.
---------------- assert (* Cut *) (euclidean__defs.Per R A B) as H37.
----------------- destruct H34 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
apply (@lemma__collinearright.lemma__collinearright D A R B H13 H36 H24).
----------------- assert (* Cut *) (euclidean__defs.Per B A R) as H38.
------------------ destruct H34 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
apply (@lemma__8__2.lemma__8__2 R A B H37).
------------------ assert (* Cut *) (euclidean__axioms.TS E B A R) as H39.
------------------- destruct H34 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
apply (@lemma__oppositesideflip.lemma__oppositesideflip A B E R H32).
------------------- assert (* Cut *) (euclidean__axioms.BetS E A R) as H40.
-------------------- destruct H34 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
assert (* Cut *) (forall A0 B0 C0 G, (euclidean__defs.Per G A0 B0) -> ((euclidean__defs.Per B0 A0 C0) -> ((euclidean__axioms.TS G B0 A0 C0) -> (euclidean__axioms.BetS G A0 C0)))) as H52.
--------------------- intro A0.
intro B0.
intro C0.
intro G.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__defs.RT G A0 B0 B0 A0 C0) /\ (euclidean__axioms.BetS G A0 C0)) as __2.
---------------------- apply (@lemma__righttogether.lemma__righttogether A0 B0 C0 G __ __0 __1).
---------------------- destruct __2 as [__2 __3].
exact __3.
--------------------- apply (@H52 A B R E H46 H38 H39).
-------------------- assert (* Cut *) (euclidean__axioms.BetS R A E) as H41.
--------------------- destruct H34 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
apply (@euclidean__axioms.axiom__betweennesssymmetry E A R H40).
--------------------- assert (* Cut *) (euclidean__defs.Out A D E) as H42.
---------------------- exists R.
split.
----------------------- exact H41.
----------------------- exact H19.
---------------------- assert (* Cut *) (euclidean__axioms.Cong A B E A) as H43.
----------------------- destruct H34 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H30 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H47.
----------------------- assert (* Cut *) (euclidean__axioms.Cong E A A B) as H44.
------------------------ destruct H34 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric E A B A H43).
------------------------ assert (* Cut *) (euclidean__axioms.Cong E A D A) as H45.
------------------------- destruct H34 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
apply (@lemma__congruencetransitive.lemma__congruencetransitive E A A B D A H44 H11).
------------------------- assert (* Cut *) (euclidean__axioms.Cong A E A D) as H46.
-------------------------- destruct H34 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
assert (* Cut *) ((euclidean__axioms.Cong A E A D) /\ ((euclidean__axioms.Cong A E D A) /\ (euclidean__axioms.Cong E A A D))) as H58.
--------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip E A D A H45).
--------------------------- destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H59.
-------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H47.
--------------------------- destruct H34 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
assert (* Cut *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq R A) /\ (euclidean__axioms.neq R D))) as H59.
---------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal R A D H19).
---------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H60.
--------------------------- assert (* Cut *) (D = D) as H48.
---------------------------- destruct H34 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
apply (@logic.eq__refl Point D).
---------------------------- assert (* Cut *) (euclidean__defs.Out A D D) as H49.
----------------------------- destruct H34 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
apply (@lemma__ray4.lemma__ray4 A D D).
------------------------------right.
left.
exact H48.

------------------------------ exact H47.
----------------------------- assert (* Cut *) (E = D) as H50.
------------------------------ destruct H34 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
apply (@lemma__layoffunique.lemma__layoffunique A D E D H42 H49 H46).
------------------------------ assert (* Cut *) (euclidean__defs.PG A B c D) as H51.
------------------------------- destruct H34 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
apply (@eq__ind__r euclidean__axioms.Point D (fun E0 => (euclidean__defs.SQ A B c E0) -> ((euclidean__axioms.TS E0 A B R) -> ((euclidean__defs.PG A B c E0) -> ((euclidean__axioms.Cong A B c E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__defs.Per E0 A B) -> ((euclidean__defs.Per B c E0) -> ((euclidean__defs.Per c E0 A) -> ((euclidean__axioms.TS E0 B A R) -> ((euclidean__axioms.BetS E0 A R) -> ((euclidean__axioms.BetS R A E0) -> ((euclidean__defs.Out A D E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__axioms.Cong E0 A A B) -> ((euclidean__axioms.Cong E0 A D A) -> ((euclidean__axioms.Cong A E0 A D) -> (euclidean__defs.PG A B c D)))))))))))))))))) with (x := E).
--------------------------------intro H63.
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
exact H65.

-------------------------------- exact H50.
-------------------------------- exact H30.
-------------------------------- exact H32.
-------------------------------- exact H33.
-------------------------------- exact H51.
-------------------------------- exact H55.
-------------------------------- exact H57.
-------------------------------- exact H61.
-------------------------------- exact H62.
-------------------------------- exact H39.
-------------------------------- exact H40.
-------------------------------- exact H41.
-------------------------------- exact H42.
-------------------------------- exact H43.
-------------------------------- exact H44.
-------------------------------- exact H45.
-------------------------------- exact H46.
------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B C D) as H52.
-------------------------------- destruct H34 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H30 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
exact H7.
-------------------------------- assert (* Cut *) (euclidean__defs.SQ A B c D) as H53.
--------------------------------- destruct H34 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
apply (@eq__ind__r euclidean__axioms.Point D (fun E0 => (euclidean__defs.SQ A B c E0) -> ((euclidean__axioms.TS E0 A B R) -> ((euclidean__defs.PG A B c E0) -> ((euclidean__axioms.Cong A B c E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__defs.Per E0 A B) -> ((euclidean__defs.Per B c E0) -> ((euclidean__defs.Per c E0 A) -> ((euclidean__axioms.TS E0 B A R) -> ((euclidean__axioms.BetS E0 A R) -> ((euclidean__axioms.BetS R A E0) -> ((euclidean__defs.Out A D E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__axioms.Cong E0 A A B) -> ((euclidean__axioms.Cong E0 A D A) -> ((euclidean__axioms.Cong A E0 A D) -> (euclidean__defs.SQ A B c D)))))))))))))))))) with (x := E).
----------------------------------intro H65.
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
exact H65.

---------------------------------- exact H50.
---------------------------------- exact H30.
---------------------------------- exact H32.
---------------------------------- exact H33.
---------------------------------- exact H53.
---------------------------------- exact H57.
---------------------------------- exact H59.
---------------------------------- exact H63.
---------------------------------- exact H64.
---------------------------------- exact H39.
---------------------------------- exact H40.
---------------------------------- exact H41.
---------------------------------- exact H42.
---------------------------------- exact H43.
---------------------------------- exact H44.
---------------------------------- exact H45.
---------------------------------- exact H46.
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B c D) as H54.
---------------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H34 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H30 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
exact H54.
---------------------------------- assert (* Cut *) (euclidean__axioms.Cong c D A B) as H55.
----------------------------------- destruct H34 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric c A B D H54).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong c D C D) as H56.
------------------------------------ destruct H34 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
apply (@lemma__congruencetransitive.lemma__congruencetransitive c D A B C D H55 H52).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A B B C) as H57.
------------------------------------- destruct H53 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H34 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H30 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
exact H9.
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A B B c) as H58.
-------------------------------------- destruct H53 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H34 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H30 as [H82 H83].
destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H as [H94 H95].
destruct H95 as [H96 H97].
destruct H97 as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
exact H60.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B c A B) as H59.
--------------------------------------- destruct H34 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric B A B c H58).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B c B C) as H60.
---------------------------------------- destruct H34 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
apply (@lemma__congruencetransitive.lemma__congruencetransitive B c A B B C H59 H57).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Cong c B C B) as H61.
----------------------------------------- destruct H34 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
assert (* Cut *) ((euclidean__axioms.Cong c B C B) /\ ((euclidean__axioms.Cong c B B C) /\ (euclidean__axioms.Cong B c C B))) as H73.
------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip B c B C H60).
------------------------------------------ destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H74.
----------------------------------------- assert (* Cut *) (euclidean__defs.Per B C D) as H62.
------------------------------------------ destruct H53 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H34 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
destruct H30 as [H86 H87].
destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
destruct H95 as [H96 H97].
destruct H as [H98 H99].
destruct H99 as [H100 H101].
destruct H101 as [H102 H103].
destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
exact H17.
------------------------------------------ assert (* Cut *) (euclidean__defs.Per B c D) as H63.
------------------------------------------- destruct H53 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H34 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H30 as [H87 H88].
destruct H88 as [H89 H90].
destruct H90 as [H91 H92].
destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
destruct H as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
exact H73.
------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B c D B C D) as H64.
-------------------------------------------- destruct H34 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
apply (@lemma__Euclid4.lemma__Euclid4 B c D B C D H63 H62).
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B D B D) /\ ((euclidean__defs.CongA c B D C B D) /\ (euclidean__defs.CongA c D B C D B))) as H65.
--------------------------------------------- destruct H34 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
apply (@proposition__04.proposition__04 c B D C B D H61 H56 H64).
--------------------------------------------- assert (* Cut *) (exists m, (euclidean__defs.Midpoint A m c) /\ (euclidean__defs.Midpoint B m D)) as H66.
---------------------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H34 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
apply (@lemma__diagonalsbisect.lemma__diagonalsbisect A B c D H51).
---------------------------------------------- destruct H66 as [m H67].
destruct H67 as [H68 H69].
destruct H65 as [H70 H71].
destruct H71 as [H72 H73].
destruct H34 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
assert (* Cut *) ((euclidean__axioms.BetS A m c) /\ (euclidean__axioms.Cong A m m c)) as H86.
----------------------------------------------- assert ((euclidean__axioms.BetS B m D) /\ (euclidean__axioms.Cong B m m D)) as H86 by exact H69.
assert ((euclidean__axioms.BetS B m D) /\ (euclidean__axioms.Cong B m m D)) as __TmpHyp by exact H86.
destruct __TmpHyp as [H87 H88].
assert ((euclidean__axioms.BetS A m c) /\ (euclidean__axioms.Cong A m m c)) as H89 by exact H68.
assert ((euclidean__axioms.BetS A m c) /\ (euclidean__axioms.Cong A m m c)) as __TmpHyp0 by exact H89.
destruct __TmpHyp0 as [H90 H91].
split.
------------------------------------------------ exact H90.
------------------------------------------------ exact H91.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS B m D) /\ (euclidean__axioms.Cong B m m D)) as H87.
------------------------------------------------ assert ((euclidean__axioms.BetS A m c) /\ (euclidean__axioms.Cong A m m c)) as H87 by exact H86.
assert ((euclidean__axioms.BetS A m c) /\ (euclidean__axioms.Cong A m m c)) as __TmpHyp by exact H87.
destruct __TmpHyp as [H88 H89].
assert ((euclidean__axioms.BetS B m D) /\ (euclidean__axioms.Cong B m m D)) as H90 by exact H69.
assert ((euclidean__axioms.BetS B m D) /\ (euclidean__axioms.Cong B m m D)) as __TmpHyp0 by exact H90.
destruct __TmpHyp0 as [H91 H92].
assert ((euclidean__axioms.BetS A m c) /\ (euclidean__axioms.Cong A m m c)) as H93 by exact H68.
assert ((euclidean__axioms.BetS A m c) /\ (euclidean__axioms.Cong A m m c)) as __TmpHyp1 by exact H93.
destruct __TmpHyp1 as [H94 H95].
split.
------------------------------------------------- exact H91.
------------------------------------------------- exact H92.
------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA C D B c D B) as H88.
------------------------------------------------- destruct H87 as [H88 H89].
destruct H86 as [H90 H91].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric c D B C D B H73).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D m D m) as H89.
-------------------------------------------------- destruct H87 as [H89 H90].
destruct H86 as [H91 H92].
apply (@euclidean__axioms.cn__congruencereflexive D m).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D c D C) as H90.
--------------------------------------------------- destruct H87 as [H90 H91].
destruct H86 as [H92 H93].
assert (* Cut *) ((euclidean__axioms.Cong D c D C) /\ ((euclidean__axioms.Cong D c C D) /\ (euclidean__axioms.Cong c D D C))) as H94.
---------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip c D C D H56).
---------------------------------------------------- destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
exact H95.
--------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C D A) as H91.
---------------------------------------------------- destruct H87 as [H91 H92].
destruct H86 as [H93 H94].
apply (@lemma__rightangleNC.lemma__rightangleNC C D A H18).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Per c D A) as H92.
----------------------------------------------------- destruct H87 as [H92 H93].
destruct H86 as [H94 H95].
apply (@eq__ind__r euclidean__axioms.Point D (fun E0 => (euclidean__defs.SQ A B c E0) -> ((euclidean__axioms.TS E0 A B R) -> ((euclidean__defs.PG A B c E0) -> ((euclidean__axioms.Cong A B c E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__defs.Per E0 A B) -> ((euclidean__defs.Per B c E0) -> ((euclidean__defs.Per c E0 A) -> ((euclidean__axioms.TS E0 B A R) -> ((euclidean__axioms.BetS E0 A R) -> ((euclidean__axioms.BetS R A E0) -> ((euclidean__defs.Out A D E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__axioms.Cong E0 A A B) -> ((euclidean__axioms.Cong E0 A D A) -> ((euclidean__axioms.Cong A E0 A D) -> (euclidean__defs.Per c D A)))))))))))))))))) with (x := E).
------------------------------------------------------intro H96.
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
exact H103.

------------------------------------------------------ exact H50.
------------------------------------------------------ exact H30.
------------------------------------------------------ exact H32.
------------------------------------------------------ exact H33.
------------------------------------------------------ exact H74.
------------------------------------------------------ exact H78.
------------------------------------------------------ exact H80.
------------------------------------------------------ exact H84.
------------------------------------------------------ exact H85.
------------------------------------------------------ exact H39.
------------------------------------------------------ exact H40.
------------------------------------------------------ exact H41.
------------------------------------------------------ exact H42.
------------------------------------------------------ exact H43.
------------------------------------------------------ exact H44.
------------------------------------------------------ exact H45.
------------------------------------------------------ exact H46.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol c D A) as H93.
------------------------------------------------------ destruct H87 as [H93 H94].
destruct H86 as [H95 H96].
apply (@lemma__rightangleNC.lemma__rightangleNC c D A H92).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A c D) as H94.
------------------------------------------------------- destruct H87 as [H94 H95].
destruct H86 as [H96 H97].
assert (* Cut *) ((euclidean__axioms.nCol D c A) /\ ((euclidean__axioms.nCol D A c) /\ ((euclidean__axioms.nCol A c D) /\ ((euclidean__axioms.nCol c A D) /\ (euclidean__axioms.nCol A D c))))) as H98.
-------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder c D A H93).
-------------------------------------------------------- destruct H98 as [H99 H100].
destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
exact H103.
------------------------------------------------------- assert (* Cut *) (c = c) as H95.
-------------------------------------------------------- destruct H87 as [H95 H96].
destruct H86 as [H97 H98].
apply (@logic.eq__refl Point c).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A c c) as H96.
--------------------------------------------------------- right.
right.
left.
exact H95.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A m c) as H97.
---------------------------------------------------------- destruct H86 as [H97 H98].
destruct H87 as [H99 H100].
right.
right.
right.
right.
left.
exact H97.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A c m) as H98.
----------------------------------------------------------- destruct H87 as [H98 H99].
destruct H86 as [H100 H101].
assert (* Cut *) ((euclidean__axioms.Col m A c) /\ ((euclidean__axioms.Col m c A) /\ ((euclidean__axioms.Col c A m) /\ ((euclidean__axioms.Col A c m) /\ (euclidean__axioms.Col c m A))))) as H102.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A m c H97).
------------------------------------------------------------ destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
exact H109.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq m c) as H99.
------------------------------------------------------------ destruct H87 as [H99 H100].
destruct H86 as [H101 H102].
assert (* Cut *) ((euclidean__axioms.neq m c) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A c))) as H103.
------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A m c H101).
------------------------------------------------------------- destruct H103 as [H104 H105].
destruct H105 as [H106 H107].
exact H104.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol m c D) as H100.
------------------------------------------------------------- destruct H87 as [H100 H101].
destruct H86 as [H102 H103].
apply (@euclidean__tactics.nCol__notCol m c D).
--------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col m c D).
---------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper A c D m c H94 H98 H96 H99).


------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol c D m) as H101.
-------------------------------------------------------------- destruct H87 as [H101 H102].
destruct H86 as [H103 H104].
assert (* Cut *) ((euclidean__axioms.nCol c m D) /\ ((euclidean__axioms.nCol c D m) /\ ((euclidean__axioms.nCol D m c) /\ ((euclidean__axioms.nCol m D c) /\ (euclidean__axioms.nCol D c m))))) as H105.
--------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder m c D H100).
--------------------------------------------------------------- destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
exact H108.
-------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col C D m)) as H102.
--------------------------------------------------------------- intro H102.
assert (* Cut *) (euclidean__axioms.Col B m D) as H103.
---------------------------------------------------------------- destruct H86 as [H103 H104].
destruct H87 as [H105 H106].
right.
right.
right.
right.
left.
exact H105.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m D B) as H104.
----------------------------------------------------------------- destruct H87 as [H104 H105].
destruct H86 as [H106 H107].
assert (* Cut *) ((euclidean__axioms.Col m B D) /\ ((euclidean__axioms.Col m D B) /\ ((euclidean__axioms.Col D B m) /\ ((euclidean__axioms.Col B D m) /\ (euclidean__axioms.Col D m B))))) as H108.
------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder B m D H103).
------------------------------------------------------------------ destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
exact H111.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col m D C) as H105.
------------------------------------------------------------------ destruct H87 as [H105 H106].
destruct H86 as [H107 H108].
assert (* Cut *) ((euclidean__axioms.Col D C m) /\ ((euclidean__axioms.Col D m C) /\ ((euclidean__axioms.Col m C D) /\ ((euclidean__axioms.Col C m D) /\ (euclidean__axioms.Col m D C))))) as H109.
------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D m H102).
------------------------------------------------------------------- destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
destruct H113 as [H114 H115].
destruct H115 as [H116 H117].
exact H117.
------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq m D) as H106.
------------------------------------------------------------------- destruct H87 as [H106 H107].
destruct H86 as [H108 H109].
assert (* Cut *) ((euclidean__axioms.neq m D) /\ ((euclidean__axioms.neq B m) /\ (euclidean__axioms.neq B D))) as H110.
-------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal B m D H106).
-------------------------------------------------------------------- destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
exact H111.
------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B C) as H107.
-------------------------------------------------------------------- destruct H87 as [H107 H108].
destruct H86 as [H109 H110].
apply (@euclidean__tactics.not__nCol__Col D B C).
---------------------------------------------------------------------intro H111.
apply (@euclidean__tactics.Col__nCol__False D B C H111).
----------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 m D B C H104 H105 H106).


-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H108.
--------------------------------------------------------------------- destruct H87 as [H108 H109].
destruct H86 as [H110 H111].
assert (* Cut *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D))))) as H112.
---------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D B C H107).
---------------------------------------------------------------------- destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
exact H115.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B C D) as H109.
---------------------------------------------------------------------- destruct H87 as [H109 H110].
destruct H86 as [H111 H112].
apply (@lemma__rightangleNC.lemma__rightangleNC B C D H62).
---------------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False B C D H109 H108).
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA c D B C D B) as H103.
---------------------------------------------------------------- destruct H87 as [H103 H104].
destruct H86 as [H105 H106].
apply (@eq__ind__r euclidean__axioms.Point D (fun E0 => (euclidean__defs.SQ A B c E0) -> ((euclidean__axioms.TS E0 A B R) -> ((euclidean__defs.PG A B c E0) -> ((euclidean__axioms.Cong A B c E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__defs.Per E0 A B) -> ((euclidean__defs.Per B c E0) -> ((euclidean__defs.Per c E0 A) -> ((euclidean__axioms.TS E0 B A R) -> ((euclidean__axioms.BetS E0 A R) -> ((euclidean__axioms.BetS R A E0) -> ((euclidean__defs.Out A D E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__axioms.Cong E0 A A B) -> ((euclidean__axioms.Cong E0 A D A) -> ((euclidean__axioms.Cong A E0 A D) -> (euclidean__defs.CongA c D B C D B)))))))))))))))))) with (x := E).
-----------------------------------------------------------------intro H107.
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
exact H73.

----------------------------------------------------------------- exact H50.
----------------------------------------------------------------- exact H30.
----------------------------------------------------------------- exact H32.
----------------------------------------------------------------- exact H33.
----------------------------------------------------------------- exact H74.
----------------------------------------------------------------- exact H78.
----------------------------------------------------------------- exact H80.
----------------------------------------------------------------- exact H84.
----------------------------------------------------------------- exact H85.
----------------------------------------------------------------- exact H39.
----------------------------------------------------------------- exact H40.
----------------------------------------------------------------- exact H41.
----------------------------------------------------------------- exact H42.
----------------------------------------------------------------- exact H43.
----------------------------------------------------------------- exact H44.
----------------------------------------------------------------- exact H45.
----------------------------------------------------------------- exact H46.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D m B) as H104.
----------------------------------------------------------------- destruct H87 as [H104 H105].
destruct H86 as [H106 H107].
apply (@euclidean__axioms.axiom__betweennesssymmetry B m D H104).
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H105.
------------------------------------------------------------------ destruct H87 as [H105 H106].
destruct H86 as [H107 H108].
assert (* Cut *) ((euclidean__axioms.neq m B) /\ ((euclidean__axioms.neq D m) /\ (euclidean__axioms.neq D B))) as H109.
------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D m B H104).
------------------------------------------------------------------- destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
exact H113.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out D B m) as H106.
------------------------------------------------------------------- destruct H87 as [H106 H107].
destruct H86 as [H108 H109].
apply (@lemma__ray4.lemma__ray4 D B m).
--------------------------------------------------------------------left.
exact H104.

-------------------------------------------------------------------- exact H105.
------------------------------------------------------------------- assert (* Cut *) (C = C) as H107.
-------------------------------------------------------------------- destruct H87 as [H107 H108].
destruct H86 as [H109 H110].
apply (@logic.eq__refl Point C).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H108.
--------------------------------------------------------------------- destruct H87 as [H108 H109].
destruct H86 as [H110 H111].
assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)))))) as H112.
---------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct C D A H91).
---------------------------------------------------------------------- destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
destruct H116 as [H117 H118].
destruct H118 as [H119 H120].
destruct H120 as [H121 H122].
exact H119.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out D C C) as H109.
---------------------------------------------------------------------- destruct H87 as [H109 H110].
destruct H86 as [H111 H112].
apply (@lemma__ray4.lemma__ray4 D C C).
-----------------------------------------------------------------------right.
left.
exact H107.

----------------------------------------------------------------------- exact H108.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA c D B C D m) as H110.
----------------------------------------------------------------------- destruct H87 as [H110 H111].
destruct H86 as [H112 H113].
apply (@lemma__equalangleshelper.lemma__equalangleshelper c D B C D B C m H103 H109 H106).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C D m c D B) as H111.
------------------------------------------------------------------------ destruct H87 as [H111 H112].
destruct H86 as [H113 H114].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric c D B C D m H110).
------------------------------------------------------------------------ assert (* Cut *) (c = c) as H112.
------------------------------------------------------------------------- destruct H87 as [H112 H113].
destruct H86 as [H114 H115].
apply (@eq__ind__r euclidean__axioms.Point D (fun E0 => (euclidean__defs.SQ A B c E0) -> ((euclidean__axioms.TS E0 A B R) -> ((euclidean__defs.PG A B c E0) -> ((euclidean__axioms.Cong A B c E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__defs.Per E0 A B) -> ((euclidean__defs.Per B c E0) -> ((euclidean__defs.Per c E0 A) -> ((euclidean__axioms.TS E0 B A R) -> ((euclidean__axioms.BetS E0 A R) -> ((euclidean__axioms.BetS R A E0) -> ((euclidean__defs.Out A D E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__axioms.Cong E0 A A B) -> ((euclidean__axioms.Cong E0 A D A) -> ((euclidean__axioms.Cong A E0 A D) -> (c = c)))))))))))))))))) with (x := E).
--------------------------------------------------------------------------intro H116.
intro H117.
intro H118.
intro H119.
intro H120.
intro H121.
intro H122.
intro H123.
intro H124.
intro H125.
intro H126.
intro H127.
intro H128.
intro H129.
intro H130.
intro H131.
exact H95.

-------------------------------------------------------------------------- exact H50.
-------------------------------------------------------------------------- exact H30.
-------------------------------------------------------------------------- exact H32.
-------------------------------------------------------------------------- exact H33.
-------------------------------------------------------------------------- exact H74.
-------------------------------------------------------------------------- exact H78.
-------------------------------------------------------------------------- exact H80.
-------------------------------------------------------------------------- exact H84.
-------------------------------------------------------------------------- exact H85.
-------------------------------------------------------------------------- exact H39.
-------------------------------------------------------------------------- exact H40.
-------------------------------------------------------------------------- exact H41.
-------------------------------------------------------------------------- exact H42.
-------------------------------------------------------------------------- exact H43.
-------------------------------------------------------------------------- exact H44.
-------------------------------------------------------------------------- exact H45.
-------------------------------------------------------------------------- exact H46.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D c) as H113.
-------------------------------------------------------------------------- destruct H87 as [H113 H114].
destruct H86 as [H115 H116].
assert (* Cut *) ((euclidean__axioms.neq c D) /\ ((euclidean__axioms.neq D m) /\ ((euclidean__axioms.neq c m) /\ ((euclidean__axioms.neq D c) /\ ((euclidean__axioms.neq m D) /\ (euclidean__axioms.neq m c)))))) as H117.
--------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct c D m H101).
--------------------------------------------------------------------------- destruct H117 as [H118 H119].
destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H124.
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out D c c) as H114.
--------------------------------------------------------------------------- destruct H87 as [H114 H115].
destruct H86 as [H116 H117].
apply (@lemma__ray4.lemma__ray4 D c c).
----------------------------------------------------------------------------right.
left.
exact H112.

---------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA C D m c D m) as H115.
---------------------------------------------------------------------------- destruct H87 as [H115 H116].
destruct H86 as [H117 H118].
apply (@lemma__equalangleshelper.lemma__equalangleshelper C D m c D B c m H111 H114 H106).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA c D m C D m) as H116.
----------------------------------------------------------------------------- destruct H87 as [H116 H117].
destruct H86 as [H118 H119].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric C D m c D m H115).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong c m C m) as H117.
------------------------------------------------------------------------------ destruct H87 as [H117 H118].
destruct H86 as [H119 H120].
assert (* Cut *) (forall A0 B0 C0 a b c0, (euclidean__axioms.Cong A0 B0 a b) -> ((euclidean__axioms.Cong A0 C0 a c0) -> ((euclidean__defs.CongA B0 A0 C0 b a c0) -> (euclidean__axioms.Cong B0 C0 b c0)))) as H121.
------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro a.
intro b.
intro c0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b c0) /\ ((euclidean__defs.CongA A0 B0 C0 a b c0) /\ (euclidean__defs.CongA A0 C0 B0 a c0 b))) as __2.
-------------------------------------------------------------------------------- apply (@proposition__04.proposition__04 A0 B0 C0 a b c0 __ __0 __1).
-------------------------------------------------------------------------------- destruct __2 as [__2 __3].
exact __2.
------------------------------------------------------------------------------- apply (@H121 D c m D C m H90 H89 H116).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong m c m C) as H118.
------------------------------------------------------------------------------- destruct H87 as [H118 H119].
destruct H86 as [H120 H121].
assert (* Cut *) ((euclidean__axioms.Cong m c m C) /\ ((euclidean__axioms.Cong m c C m) /\ (euclidean__axioms.Cong c m m C))) as H122.
-------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip c m C m H117).
-------------------------------------------------------------------------------- destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
exact H123.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A m A m) as H119.
-------------------------------------------------------------------------------- destruct H87 as [H119 H120].
destruct H86 as [H121 H122].
apply (@euclidean__axioms.cn__congruencereflexive A m).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D A D A) as H120.
--------------------------------------------------------------------------------- destruct H87 as [H120 H121].
destruct H86 as [H122 H123].
apply (@eq__ind__r euclidean__axioms.Point D (fun E0 => (euclidean__defs.SQ A B c E0) -> ((euclidean__axioms.TS E0 A B R) -> ((euclidean__defs.PG A B c E0) -> ((euclidean__axioms.Cong A B c E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__defs.Per E0 A B) -> ((euclidean__defs.Per B c E0) -> ((euclidean__defs.Per c E0 A) -> ((euclidean__axioms.TS E0 B A R) -> ((euclidean__axioms.BetS E0 A R) -> ((euclidean__axioms.BetS R A E0) -> ((euclidean__defs.Out A D E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__axioms.Cong E0 A A B) -> ((euclidean__axioms.Cong E0 A D A) -> ((euclidean__axioms.Cong A E0 A D) -> (euclidean__axioms.Cong D A D A)))))))))))))))))) with (x := E).
----------------------------------------------------------------------------------intro H124.
intro H125.
intro H126.
intro H127.
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
exact H138.

---------------------------------------------------------------------------------- exact H50.
---------------------------------------------------------------------------------- exact H30.
---------------------------------------------------------------------------------- exact H32.
---------------------------------------------------------------------------------- exact H33.
---------------------------------------------------------------------------------- exact H74.
---------------------------------------------------------------------------------- exact H78.
---------------------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------------------- exact H84.
---------------------------------------------------------------------------------- exact H85.
---------------------------------------------------------------------------------- exact H39.
---------------------------------------------------------------------------------- exact H40.
---------------------------------------------------------------------------------- exact H41.
---------------------------------------------------------------------------------- exact H42.
---------------------------------------------------------------------------------- exact H43.
---------------------------------------------------------------------------------- exact H44.
---------------------------------------------------------------------------------- exact H45.
---------------------------------------------------------------------------------- exact H46.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per c D A) as H121.
---------------------------------------------------------------------------------- destruct H87 as [H121 H122].
destruct H86 as [H123 H124].
apply (@eq__ind__r euclidean__axioms.Point D (fun E0 => (euclidean__defs.SQ A B c E0) -> ((euclidean__axioms.TS E0 A B R) -> ((euclidean__defs.PG A B c E0) -> ((euclidean__axioms.Cong A B c E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__defs.Per E0 A B) -> ((euclidean__defs.Per B c E0) -> ((euclidean__defs.Per c E0 A) -> ((euclidean__axioms.TS E0 B A R) -> ((euclidean__axioms.BetS E0 A R) -> ((euclidean__axioms.BetS R A E0) -> ((euclidean__defs.Out A D E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__axioms.Cong E0 A A B) -> ((euclidean__axioms.Cong E0 A D A) -> ((euclidean__axioms.Cong A E0 A D) -> (euclidean__defs.Per c D A)))))))))))))))))) with (x := E).
-----------------------------------------------------------------------------------intro H125.
intro H126.
intro H127.
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
exact H92.

----------------------------------------------------------------------------------- exact H50.
----------------------------------------------------------------------------------- exact H30.
----------------------------------------------------------------------------------- exact H32.
----------------------------------------------------------------------------------- exact H33.
----------------------------------------------------------------------------------- exact H74.
----------------------------------------------------------------------------------- exact H78.
----------------------------------------------------------------------------------- exact H80.
----------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------- exact H85.
----------------------------------------------------------------------------------- exact H39.
----------------------------------------------------------------------------------- exact H40.
----------------------------------------------------------------------------------- exact H41.
----------------------------------------------------------------------------------- exact H42.
----------------------------------------------------------------------------------- exact H43.
----------------------------------------------------------------------------------- exact H44.
----------------------------------------------------------------------------------- exact H45.
----------------------------------------------------------------------------------- exact H46.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per A D c) as H122.
----------------------------------------------------------------------------------- destruct H87 as [H122 H123].
destruct H86 as [H124 H125].
apply (@lemma__8__2.lemma__8__2 c D A H121).
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Per A D C) as H123.
------------------------------------------------------------------------------------ destruct H87 as [H123 H124].
destruct H86 as [H125 H126].
apply (@lemma__8__2.lemma__8__2 C D A H18).
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A D C A D c) as H124.
------------------------------------------------------------------------------------- destruct H87 as [H124 H125].
destruct H86 as [H126 H127].
apply (@lemma__Euclid4.lemma__Euclid4 A D C A D c H123 H122).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D C D c) as H125.
-------------------------------------------------------------------------------------- destruct H87 as [H125 H126].
destruct H86 as [H127 H128].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D D c C H90).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A C A c) as H126.
--------------------------------------------------------------------------------------- destruct H87 as [H126 H127].
destruct H86 as [H128 H129].
assert (* Cut *) (forall A0 B0 C0 a b c0, (euclidean__axioms.Cong A0 B0 a b) -> ((euclidean__axioms.Cong A0 C0 a c0) -> ((euclidean__defs.CongA B0 A0 C0 b a c0) -> (euclidean__axioms.Cong B0 C0 b c0)))) as H130.
---------------------------------------------------------------------------------------- intro A0.
intro B0.
intro C0.
intro a.
intro b.
intro c0.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b c0) /\ ((euclidean__defs.CongA A0 B0 C0 a b c0) /\ (euclidean__defs.CongA A0 C0 B0 a c0 b))) as __2.
----------------------------------------------------------------------------------------- apply (@proposition__04.proposition__04 A0 B0 C0 a b c0 __ __0 __1).
----------------------------------------------------------------------------------------- destruct __2 as [__2 __3].
exact __2.
---------------------------------------------------------------------------------------- apply (@H130 D A C D A c H120 H125 H124).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A c A C) as H127.
---------------------------------------------------------------------------------------- destruct H87 as [H127 H128].
destruct H86 as [H129 H130].
apply (@lemma__congruencesymmetric.lemma__congruencesymmetric A A C c H126).
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A m C) as H128.
----------------------------------------------------------------------------------------- destruct H87 as [H128 H129].
destruct H86 as [H130 H131].
apply (@lemma__betweennesspreserved.lemma__betweennesspreserved A m c A m C H119 H127 H118 H130).
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq A m) as H129.
------------------------------------------------------------------------------------------ destruct H87 as [H129 H130].
destruct H86 as [H131 H132].
assert (* Cut *) ((euclidean__axioms.neq m C) /\ ((euclidean__axioms.neq A m) /\ (euclidean__axioms.neq A C))) as H133.
------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A m C H128).
------------------------------------------------------------------------------------------- destruct H133 as [H134 H135].
destruct H135 as [H136 H137].
exact H136.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out A m c) as H130.
------------------------------------------------------------------------------------------- destruct H87 as [H130 H131].
destruct H86 as [H132 H133].
apply (@lemma__ray4.lemma__ray4 A m c).
--------------------------------------------------------------------------------------------right.
right.
exact H132.

-------------------------------------------------------------------------------------------- exact H129.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out A m C) as H131.
-------------------------------------------------------------------------------------------- destruct H87 as [H131 H132].
destruct H86 as [H133 H134].
apply (@lemma__ray4.lemma__ray4 A m C).
---------------------------------------------------------------------------------------------right.
right.
exact H128.

--------------------------------------------------------------------------------------------- exact H129.
-------------------------------------------------------------------------------------------- assert (* Cut *) (c = C) as H132.
--------------------------------------------------------------------------------------------- destruct H87 as [H132 H133].
destruct H86 as [H134 H135].
apply (@lemma__layoffunique.lemma__layoffunique A m c C H130 H131 H127).
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.PG A B C D) as H133.
---------------------------------------------------------------------------------------------- destruct H87 as [H133 H134].
destruct H86 as [H135 H136].
apply (@eq__ind__r euclidean__axioms.Point C (fun c0 => (euclidean__defs.SQ A B c0 E) -> ((euclidean__defs.PG A B c0 E) -> ((euclidean__axioms.Cong A B c0 E) -> ((euclidean__axioms.Cong A B B c0) -> ((euclidean__defs.Per A B c0) -> ((euclidean__defs.Per B c0 E) -> ((euclidean__defs.Per c0 E A) -> ((euclidean__defs.PG A B c0 D) -> ((euclidean__defs.SQ A B c0 D) -> ((euclidean__axioms.Cong A B c0 D) -> ((euclidean__axioms.Cong c0 D A B) -> ((euclidean__axioms.Cong c0 D C D) -> ((euclidean__axioms.Cong A B B c0) -> ((euclidean__axioms.Cong B c0 A B) -> ((euclidean__axioms.Cong B c0 B C) -> ((euclidean__axioms.Cong c0 B C B) -> ((euclidean__defs.Per B c0 D) -> ((euclidean__defs.CongA B c0 D B C D) -> ((euclidean__defs.CongA c0 B D C B D) -> ((euclidean__defs.CongA c0 D B C D B) -> ((euclidean__defs.Midpoint A m c0) -> ((euclidean__axioms.BetS A m c0) -> ((euclidean__axioms.Cong A m m c0) -> ((euclidean__defs.CongA C D B c0 D B) -> ((euclidean__axioms.Cong D c0 D C) -> ((euclidean__defs.Per c0 D A) -> ((euclidean__axioms.nCol c0 D A) -> ((euclidean__axioms.nCol A c0 D) -> ((c0 = c0) -> ((euclidean__axioms.Col A c0 c0) -> ((euclidean__axioms.Col A m c0) -> ((euclidean__axioms.Col A c0 m) -> ((euclidean__axioms.neq m c0) -> ((euclidean__axioms.nCol m c0 D) -> ((euclidean__axioms.nCol c0 D m) -> ((euclidean__defs.CongA c0 D B C D B) -> ((euclidean__defs.CongA c0 D B C D m) -> ((euclidean__defs.CongA C D m c0 D B) -> ((c0 = c0) -> ((euclidean__axioms.neq D c0) -> ((euclidean__defs.Out D c0 c0) -> ((euclidean__defs.CongA C D m c0 D m) -> ((euclidean__defs.CongA c0 D m C D m) -> ((euclidean__axioms.Cong c0 m C m) -> ((euclidean__axioms.Cong m c0 m C) -> ((euclidean__defs.Per c0 D A) -> ((euclidean__defs.Per A D c0) -> ((euclidean__defs.CongA A D C A D c0) -> ((euclidean__axioms.Cong D C D c0) -> ((euclidean__axioms.Cong A C A c0) -> ((euclidean__axioms.Cong A c0 A C) -> ((euclidean__defs.Out A m c0) -> (euclidean__defs.PG A B C D)))))))))))))))))))))))))))))))))))))))))))))))))))))) with (x := c).
-----------------------------------------------------------------------------------------------intro H137.
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
intro H149.
intro H150.
intro H151.
intro H152.
intro H153.
intro H154.
intro H155.
intro H156.
intro H157.
intro H158.
intro H159.
intro H160.
intro H161.
intro H162.
intro H163.
intro H164.
intro H165.
intro H166.
intro H167.
intro H168.
intro H169.
intro H170.
intro H171.
intro H172.
intro H173.
intro H174.
intro H175.
intro H176.
intro H177.
intro H178.
intro H179.
intro H180.
intro H181.
intro H182.
intro H183.
intro H184.
intro H185.
intro H186.
intro H187.
intro H188.
apply (@eq__ind__r euclidean__axioms.Point D (fun E0 => (euclidean__defs.SQ A B C E0) -> ((euclidean__axioms.TS E0 A B R) -> ((euclidean__axioms.Cong A B C E0) -> ((euclidean__defs.PG A B C E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__defs.Per E0 A B) -> ((euclidean__defs.Per C E0 A) -> ((euclidean__defs.Per B C E0) -> ((euclidean__axioms.TS E0 B A R) -> ((euclidean__axioms.BetS E0 A R) -> ((euclidean__axioms.BetS R A E0) -> ((euclidean__defs.Out A D E0) -> ((euclidean__axioms.Cong A B E0 A) -> ((euclidean__axioms.Cong E0 A A B) -> ((euclidean__axioms.Cong E0 A D A) -> ((euclidean__axioms.Cong A E0 A D) -> (euclidean__defs.PG A B C D)))))))))))))))))) with (x := E).
------------------------------------------------------------------------------------------------intro H189.
intro H190.
intro H191.
intro H192.
intro H193.
intro H194.
intro H195.
intro H196.
intro H197.
intro H198.
intro H199.
intro H200.
intro H201.
intro H202.
intro H203.
intro H204.
exact H144.

------------------------------------------------------------------------------------------------ exact H50.
------------------------------------------------------------------------------------------------ exact H137.
------------------------------------------------------------------------------------------------ exact H32.
------------------------------------------------------------------------------------------------ exact H139.
------------------------------------------------------------------------------------------------ exact H138.
------------------------------------------------------------------------------------------------ exact H78.
------------------------------------------------------------------------------------------------ exact H80.
------------------------------------------------------------------------------------------------ exact H143.
------------------------------------------------------------------------------------------------ exact H142.
------------------------------------------------------------------------------------------------ exact H39.
------------------------------------------------------------------------------------------------ exact H40.
------------------------------------------------------------------------------------------------ exact H41.
------------------------------------------------------------------------------------------------ exact H42.
------------------------------------------------------------------------------------------------ exact H43.
------------------------------------------------------------------------------------------------ exact H44.
------------------------------------------------------------------------------------------------ exact H45.
------------------------------------------------------------------------------------------------ exact H46.

----------------------------------------------------------------------------------------------- exact H132.
----------------------------------------------------------------------------------------------- exact H30.
----------------------------------------------------------------------------------------------- exact H33.
----------------------------------------------------------------------------------------------- exact H74.
----------------------------------------------------------------------------------------------- exact H76.
----------------------------------------------------------------------------------------------- exact H82.
----------------------------------------------------------------------------------------------- exact H84.
----------------------------------------------------------------------------------------------- exact H85.
----------------------------------------------------------------------------------------------- exact H51.
----------------------------------------------------------------------------------------------- exact H53.
----------------------------------------------------------------------------------------------- exact H54.
----------------------------------------------------------------------------------------------- exact H55.
----------------------------------------------------------------------------------------------- exact H56.
----------------------------------------------------------------------------------------------- exact H58.
----------------------------------------------------------------------------------------------- exact H59.
----------------------------------------------------------------------------------------------- exact H60.
----------------------------------------------------------------------------------------------- exact H61.
----------------------------------------------------------------------------------------------- exact H63.
----------------------------------------------------------------------------------------------- exact H64.
----------------------------------------------------------------------------------------------- exact H72.
----------------------------------------------------------------------------------------------- exact H73.
----------------------------------------------------------------------------------------------- exact H68.
----------------------------------------------------------------------------------------------- exact H135.
----------------------------------------------------------------------------------------------- exact H136.
----------------------------------------------------------------------------------------------- exact H88.
----------------------------------------------------------------------------------------------- exact H90.
----------------------------------------------------------------------------------------------- exact H92.
----------------------------------------------------------------------------------------------- exact H93.
----------------------------------------------------------------------------------------------- exact H94.
----------------------------------------------------------------------------------------------- exact H95.
----------------------------------------------------------------------------------------------- exact H96.
----------------------------------------------------------------------------------------------- exact H97.
----------------------------------------------------------------------------------------------- exact H98.
----------------------------------------------------------------------------------------------- exact H99.
----------------------------------------------------------------------------------------------- exact H100.
----------------------------------------------------------------------------------------------- exact H101.
----------------------------------------------------------------------------------------------- exact H103.
----------------------------------------------------------------------------------------------- exact H110.
----------------------------------------------------------------------------------------------- exact H111.
----------------------------------------------------------------------------------------------- exact H112.
----------------------------------------------------------------------------------------------- exact H113.
----------------------------------------------------------------------------------------------- exact H114.
----------------------------------------------------------------------------------------------- exact H115.
----------------------------------------------------------------------------------------------- exact H116.
----------------------------------------------------------------------------------------------- exact H117.
----------------------------------------------------------------------------------------------- exact H118.
----------------------------------------------------------------------------------------------- exact H121.
----------------------------------------------------------------------------------------------- exact H122.
----------------------------------------------------------------------------------------------- exact H124.
----------------------------------------------------------------------------------------------- exact H125.
----------------------------------------------------------------------------------------------- exact H126.
----------------------------------------------------------------------------------------------- exact H127.
----------------------------------------------------------------------------------------------- exact H130.
---------------------------------------------------------------------------------------------- exact H133.
Qed.
