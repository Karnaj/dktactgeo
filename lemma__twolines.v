Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear1.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export logic.
Definition lemma__twolines : forall A B C D E F, (euclidean__defs.Cut A B C D E) -> ((euclidean__defs.Cut A B C D F) -> ((euclidean__axioms.nCol B C D) -> (E = F))).
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
assert (* Cut *) ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H2.
- assert ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H2 by exact H0.
assert ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as __TmpHyp by exact H2.
destruct __TmpHyp as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
assert ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H9 by exact H.
assert ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as __TmpHyp0 by exact H9.
destruct __TmpHyp0 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
split.
-- exact H10.
-- split.
--- exact H12.
--- split.
---- exact H14.
---- exact H15.
- assert (* Cut *) ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H3.
-- assert ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H3 by exact H2.
assert ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as __TmpHyp by exact H3.
destruct __TmpHyp as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
assert ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H10 by exact H0.
assert ((euclidean__axioms.BetS A F B) /\ ((euclidean__axioms.BetS C F D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as __TmpHyp0 by exact H10.
destruct __TmpHyp0 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
assert ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as H17 by exact H.
assert ((euclidean__axioms.BetS A E B) /\ ((euclidean__axioms.BetS C E D) /\ ((euclidean__axioms.nCol A B C) /\ (euclidean__axioms.nCol A B D)))) as __TmpHyp1 by exact H17.
destruct __TmpHyp1 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
split.
--- exact H11.
--- split.
---- exact H13.
---- split.
----- exact H22.
----- exact H23.
-- assert (* Cut *) (euclidean__axioms.Col A E B) as H4.
--- destruct H2 as [H4 H5].
destruct H3 as [H6 H7].
destruct H5 as [H8 H9].
destruct H7 as [H10 H11].
destruct H9 as [H12 H13].
destruct H11 as [H14 H15].
right.
right.
right.
right.
left.
exact H4.
--- assert (* Cut *) (euclidean__axioms.Col A B E) as H5.
---- destruct H3 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H2 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H17.
----- apply (@lemma__collinearorder.lemma__collinearorder A E B H4).
----- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H24.
---- assert (* Cut *) (euclidean__axioms.Col A F B) as H6.
----- destruct H2 as [H6 H7].
destruct H3 as [H8 H9].
destruct H7 as [H10 H11].
destruct H9 as [H12 H13].
destruct H11 as [H14 H15].
destruct H13 as [H16 H17].
right.
right.
right.
right.
left.
exact H8.
----- assert (* Cut *) (euclidean__axioms.Col A B F) as H7.
------ destruct H3 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H2 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
assert (* Cut *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col F B A) /\ ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col A B F) /\ (euclidean__axioms.Col B F A))))) as H19.
------- apply (@lemma__collinearorder.lemma__collinearorder A F B H6).
------- destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H26.
------ assert (* Cut *) (euclidean__axioms.neq A B) as H8.
------- destruct H3 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H2 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
assert (* Cut *) ((euclidean__axioms.neq F B) /\ ((euclidean__axioms.neq A F) /\ (euclidean__axioms.neq A B))) as H20.
-------- apply (@lemma__betweennotequal.lemma__betweennotequal A F B H8).
-------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H24.
------- assert (* Cut *) (euclidean__axioms.Col B E F) as H9.
-------- destruct H3 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H2 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
apply (@euclidean__tactics.not__nCol__Col B E F).
---------intro H21.
apply (@euclidean__tactics.Col__nCol__False B E F H21).
----------apply (@lemma__collinear4.lemma__collinear4 A B E F H5 H7 H8).


-------- assert (* Cut *) (euclidean__axioms.Col E F B) as H10.
--------- destruct H3 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H2 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
assert (* Cut *) ((euclidean__axioms.Col E B F) /\ ((euclidean__axioms.Col E F B) /\ ((euclidean__axioms.Col F B E) /\ ((euclidean__axioms.Col B F E) /\ (euclidean__axioms.Col F E B))))) as H22.
---------- apply (@lemma__collinearorder.lemma__collinearorder B E F H9).
---------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H25.
--------- assert (* Cut *) (euclidean__axioms.Col C E D) as H11.
---------- destruct H2 as [H11 H12].
destruct H3 as [H13 H14].
destruct H12 as [H15 H16].
destruct H14 as [H17 H18].
destruct H16 as [H19 H20].
destruct H18 as [H21 H22].
right.
right.
right.
right.
left.
exact H15.
---------- assert (* Cut *) (euclidean__axioms.Col C F D) as H12.
----------- destruct H2 as [H12 H13].
destruct H3 as [H14 H15].
destruct H13 as [H16 H17].
destruct H15 as [H18 H19].
destruct H17 as [H20 H21].
destruct H19 as [H22 H23].
right.
right.
right.
right.
left.
exact H18.
----------- assert (* Cut *) (euclidean__axioms.Col C D F) as H13.
------------ destruct H3 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H2 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
assert (* Cut *) ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col D C F) /\ ((euclidean__axioms.Col C D F) /\ (euclidean__axioms.Col D F C))))) as H25.
------------- apply (@lemma__collinearorder.lemma__collinearorder C F D H12).
------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H32.
------------ assert (* Cut *) (euclidean__axioms.Col C D E) as H14.
------------- destruct H3 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H2 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
assert (* Cut *) ((euclidean__axioms.Col E C D) /\ ((euclidean__axioms.Col E D C) /\ ((euclidean__axioms.Col D C E) /\ ((euclidean__axioms.Col C D E) /\ (euclidean__axioms.Col D E C))))) as H26.
-------------- apply (@lemma__collinearorder.lemma__collinearorder C E D H11).
-------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H33.
------------- assert (* Cut *) (euclidean__axioms.neq C D) as H15.
-------------- destruct H3 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H2 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H27.
--------------- apply (@lemma__betweennotequal.lemma__betweennotequal C F D H17).
--------------- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H31.
-------------- assert (* Cut *) (euclidean__axioms.Col D E F) as H16.
--------------- destruct H3 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H2 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
apply (@euclidean__tactics.not__nCol__Col D E F).
----------------intro H28.
apply (@euclidean__tactics.Col__nCol__False D E F H28).
-----------------apply (@lemma__collinear4.lemma__collinear4 C D E F H14 H13 H15).


--------------- assert (* Cut *) (euclidean__axioms.Col E F D) as H17.
---------------- destruct H3 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H2 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
assert (* Cut *) ((euclidean__axioms.Col E D F) /\ ((euclidean__axioms.Col E F D) /\ ((euclidean__axioms.Col F D E) /\ ((euclidean__axioms.Col D F E) /\ (euclidean__axioms.Col F E D))))) as H29.
----------------- apply (@lemma__collinearorder.lemma__collinearorder D E F H16).
----------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H32.
---------------- assert (* Cut *) (euclidean__axioms.Col D C E) as H18.
----------------- destruct H3 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H2 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
apply (@lemma__collinear1.lemma__collinear1 C D E H14).
----------------- assert (* Cut *) (euclidean__axioms.Col D C F) as H19.
------------------ destruct H3 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H2 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
apply (@lemma__collinear1.lemma__collinear1 C D F H13).
------------------ assert (* Cut *) (euclidean__axioms.BetS D E C) as H20.
------------------- destruct H3 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H2 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
apply (@euclidean__axioms.axiom__betweennesssymmetry C E D H28).
------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H21.
-------------------- destruct H3 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H2 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
assert (* Cut *) ((euclidean__axioms.neq E C) /\ ((euclidean__axioms.neq D E) /\ (euclidean__axioms.neq D C))) as H33.
--------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D E C H20).
--------------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H37.
-------------------- assert (* Cut *) (euclidean__axioms.Col C E F) as H22.
--------------------- destruct H3 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H2 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
apply (@euclidean__tactics.not__nCol__Col C E F).
----------------------intro H34.
apply (@euclidean__tactics.Col__nCol__False C E F H34).
-----------------------apply (@lemma__collinear4.lemma__collinear4 D C E F H18 H19 H21).


--------------------- assert (* Cut *) (euclidean__axioms.Col E F C) as H23.
---------------------- destruct H3 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H2 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
assert (* Cut *) ((euclidean__axioms.Col E C F) /\ ((euclidean__axioms.Col E F C) /\ ((euclidean__axioms.Col F C E) /\ ((euclidean__axioms.Col C F E) /\ (euclidean__axioms.Col F E C))))) as H35.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder C E F H22).
----------------------- destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H38.
---------------------- assert (* Cut *) (~(euclidean__axioms.neq E F)) as H24.
----------------------- intro H24.
assert (* Cut *) (euclidean__axioms.Col F B C) as H25.
------------------------ destruct H3 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H2 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
apply (@euclidean__tactics.not__nCol__Col F B C).
-------------------------intro H37.
apply (@euclidean__tactics.Col__nCol__False F B C H37).
--------------------------apply (@lemma__collinear4.lemma__collinear4 E F B C H10 H23 H24).


------------------------ assert (* Cut *) (euclidean__axioms.Col F B D) as H26.
------------------------- destruct H3 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H2 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
apply (@euclidean__tactics.not__nCol__Col F B D).
--------------------------intro H38.
apply (@euclidean__tactics.Col__nCol__False F B D H38).
---------------------------apply (@lemma__collinear4.lemma__collinear4 E F B D H10 H17 H24).


------------------------- assert (* Cut *) (~(F = B)) as H27.
-------------------------- intro H27.
assert (* Cut *) (euclidean__axioms.Col F C D) as H28.
--------------------------- destruct H2 as [H28 H29].
destruct H3 as [H30 H31].
destruct H29 as [H32 H33].
destruct H31 as [H34 H35].
destruct H33 as [H36 H37].
destruct H35 as [H38 H39].
right.
right.
right.
left.
exact H34.
--------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H29.
---------------------------- destruct H3 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H2 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
apply (@eq__ind__r euclidean__axioms.Point B (fun F0 => (euclidean__defs.Cut A B C D F0) -> ((euclidean__axioms.BetS A F0 B) -> ((euclidean__axioms.BetS C F0 D) -> ((euclidean__axioms.Col A F0 B) -> ((euclidean__axioms.Col A B F0) -> ((euclidean__axioms.Col B E F0) -> ((euclidean__axioms.Col E F0 B) -> ((euclidean__axioms.Col C F0 D) -> ((euclidean__axioms.Col C D F0) -> ((euclidean__axioms.Col D E F0) -> ((euclidean__axioms.Col E F0 D) -> ((euclidean__axioms.Col D C F0) -> ((euclidean__axioms.Col C E F0) -> ((euclidean__axioms.Col E F0 C) -> ((euclidean__axioms.neq E F0) -> ((euclidean__axioms.Col F0 B C) -> ((euclidean__axioms.Col F0 B D) -> ((euclidean__axioms.Col F0 C D) -> (euclidean__axioms.Col B C D)))))))))))))))))))) with (x := F).
-----------------------------intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
exact H58.

----------------------------- exact H27.
----------------------------- exact H0.
----------------------------- exact H29.
----------------------------- exact H31.
----------------------------- exact H6.
----------------------------- exact H7.
----------------------------- exact H9.
----------------------------- exact H10.
----------------------------- exact H12.
----------------------------- exact H13.
----------------------------- exact H16.
----------------------------- exact H17.
----------------------------- exact H19.
----------------------------- exact H22.
----------------------------- exact H23.
----------------------------- exact H24.
----------------------------- exact H25.
----------------------------- exact H26.
----------------------------- exact H28.
---------------------------- apply (@euclidean__tactics.Col__nCol__False B C D H1 H29).
-------------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H28.
--------------------------- destruct H3 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H2 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
apply (@euclidean__tactics.not__nCol__Col B C D).
----------------------------intro H40.
apply (@euclidean__tactics.Col__nCol__False B C D H40).
-----------------------------apply (@lemma__collinear4.lemma__collinear4 F B C D H25 H26 H27).


--------------------------- apply (@euclidean__tactics.Col__nCol__False B C D H1 H28).
----------------------- apply (@euclidean__tactics.NNPP (E = F)).
------------------------intro H25.
destruct H1 as [H26 H27].
destruct H2 as [H28 H29].
destruct H3 as [H30 H31].
destruct H27 as [H32 H33].
destruct H29 as [H34 H35].
destruct H31 as [H36 H37].
destruct H33 as [H38 H39].
destruct H35 as [H40 H41].
destruct H37 as [H42 H43].
destruct H39 as [H44 H45].
destruct H40 as [H46 H47].
destruct H41 as [H48 H49].
destruct H42 as [H50 H51].
destruct H43 as [H52 H53].
destruct H45 as [H54 H55].
destruct H47 as [H56 H57].
destruct H49 as [H58 H59].
destruct H51 as [H60 H61].
destruct H53 as [H62 H63].
destruct H57 as [H64 H65].
destruct H59 as [H66 H67].
destruct H61 as [H68 H69].
destruct H63 as [H70 H71].
destruct H65 as [H72 H73].
destruct H67 as [H74 H75].
destruct H69 as [H76 H77].
destruct H71 as [H78 H79].
destruct H73 as [H80 H81].
destruct H75 as [H82 H83].
destruct H77 as [H84 H85].
destruct H79 as [H86 H87].
assert (* Cut *) (False) as H88.
------------------------- apply (@H24 H25).
------------------------- contradiction H88.

Qed.
