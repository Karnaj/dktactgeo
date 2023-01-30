Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__angleordertransitive.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__05.
Require Export proposition__16.
Definition proposition__18 : forall A B C, (euclidean__axioms.Triangle A B C) -> ((euclidean__defs.Lt A B A C) -> (euclidean__defs.LtA B C A A B C)).
Proof.
intro A.
intro B.
intro C.
intro H.
intro H0.
assert (euclidean__axioms.nCol A B C) as H1 by exact H.
assert (* Cut *) (~(A = B)) as H2.
- intro H2.
assert (* Cut *) (euclidean__axioms.Col A B C) as H3.
-- left.
exact H2.
-- apply (@euclidean__tactics.Col__nCol__False A B C H1 H3).
- assert (* Cut *) (euclidean__axioms.neq B A) as H3.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H2).
-- assert (* Cut *) (~(A = C)) as H4.
--- intro H4.
assert (* Cut *) (euclidean__axioms.Col A B C) as H5.
---- right.
left.
exact H4.
---- apply (@euclidean__tactics.Col__nCol__False A B C H1 H5).
--- assert (* Cut *) (euclidean__axioms.neq C A) as H5.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A C H4).
---- assert (* Cut *) (euclidean__axioms.Cong A C A C) as H6.
----- apply (@euclidean__axioms.cn__congruencereflexive A C).
----- assert (exists D, (euclidean__axioms.BetS A D C) /\ (euclidean__axioms.Cong A D A B)) as H7 by exact H0.
destruct H7 as [D H8].
destruct H8 as [H9 H10].
assert (* Cut *) (~(euclidean__axioms.Col B C D)) as H11.
------ intro H11.
assert (* Cut *) (euclidean__axioms.Col D C B) as H12.
------- assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H12.
-------- apply (@lemma__collinearorder.lemma__collinearorder B C D H11).
-------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H20.
------- assert (* Cut *) (euclidean__axioms.Col A D C) as H13.
-------- right.
right.
right.
right.
left.
exact H9.
-------- assert (* Cut *) (euclidean__axioms.Col D C A) as H14.
--------- assert (* Cut *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A C D) /\ (euclidean__axioms.Col C D A))))) as H14.
---------- apply (@lemma__collinearorder.lemma__collinearorder A D C H13).
---------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H17.
--------- assert (* Cut *) (euclidean__axioms.neq D C) as H15.
---------- assert (* Cut *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C))) as H15.
----------- apply (@lemma__betweennotequal.lemma__betweennotequal A D C H9).
----------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H16.
---------- assert (* Cut *) (euclidean__axioms.Col C B A) as H16.
----------- apply (@euclidean__tactics.not__nCol__Col C B A).
------------intro H16.
apply (@euclidean__tactics.Col__nCol__False C B A H16).
-------------apply (@lemma__collinear4.lemma__collinear4 D C B A H12 H14 H15).


----------- assert (* Cut *) (euclidean__axioms.Col A B C) as H17.
------------ assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H17.
------------- apply (@lemma__collinearorder.lemma__collinearorder C B A H16).
------------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H25.
------------ apply (@euclidean__tactics.Col__nCol__False A B C H1 H17).
------ assert (* Cut *) (euclidean__axioms.Triangle B C D) as H12.
------- apply (@euclidean__tactics.nCol__notCol B C D H11).
------- assert (* Cut *) (euclidean__axioms.BetS C D A) as H13.
-------- apply (@euclidean__axioms.axiom__betweennesssymmetry A D C H9).
-------- assert (* Cut *) (euclidean__defs.LtA D C B B D A) as H14.
--------- assert (* Cut *) (forall A0 B0 C0 D0, (euclidean__axioms.Triangle A0 B0 C0) -> ((euclidean__axioms.BetS B0 C0 D0) -> (euclidean__defs.LtA C0 B0 A0 A0 C0 D0))) as H14.
---------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
intro __0.
assert (* AndElim *) ((euclidean__defs.LtA B0 A0 C0 A0 C0 D0) /\ (euclidean__defs.LtA C0 B0 A0 A0 C0 D0)) as __1.
----------- apply (@proposition__16.proposition__16 A0 B0 C0 D0 __ __0).
----------- destruct __1 as [__1 __2].
exact __2.
---------- apply (@H14 B C D A H12 H13).
--------- assert (* Cut *) (~(B = C)) as H15.
---------- intro H15.
assert (* Cut *) (euclidean__axioms.Col B C D) as H16.
----------- left.
exact H15.
----------- apply (@H11 H16).
---------- assert (* Cut *) (euclidean__axioms.neq C B) as H16.
----------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B C H15).
----------- assert (* Cut *) (~(euclidean__axioms.Col A D B)) as H17.
------------ intro H17.
assert (* Cut *) (euclidean__axioms.Col A D C) as H18.
------------- right.
right.
right.
right.
left.
exact H9.
------------- assert (* Cut *) (euclidean__axioms.Col D A C) as H19.
-------------- assert (* Cut *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A C D) /\ (euclidean__axioms.Col C D A))))) as H19.
--------------- apply (@lemma__collinearorder.lemma__collinearorder A D C H18).
--------------- destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H20.
-------------- assert (* Cut *) (euclidean__axioms.Col D A B) as H20.
--------------- assert (* Cut *) ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A))))) as H20.
---------------- apply (@lemma__collinearorder.lemma__collinearorder A D B H17).
---------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H21.
--------------- assert (* Cut *) (euclidean__axioms.neq A D) as H21.
---------------- assert (* Cut *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C))) as H21.
----------------- apply (@lemma__betweennotequal.lemma__betweennotequal A D C H9).
----------------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H24.
---------------- assert (* Cut *) (euclidean__axioms.neq D A) as H22.
----------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A D H21).
----------------- assert (* Cut *) (euclidean__axioms.Col A C B) as H23.
------------------ apply (@euclidean__tactics.not__nCol__Col A C B).
-------------------intro H23.
apply (@euclidean__tactics.Col__nCol__False A C B H23).
--------------------apply (@lemma__collinear4.lemma__collinear4 D A C B H19 H20 H22).


------------------ assert (* Cut *) (euclidean__axioms.Col A B C) as H24.
------------------- assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H24.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder A C B H23).
-------------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H31.
------------------- apply (@H11).
--------------------apply (@euclidean__tactics.not__nCol__Col B C D).
---------------------intro H25.
apply (@euclidean__tactics.Col__nCol__False A B C H1 H24).


------------ assert (* Cut *) (euclidean__axioms.Triangle A D B) as H18.
------------- apply (@euclidean__tactics.nCol__notCol A D B H17).
------------- assert (* Cut *) (euclidean__defs.isosceles A D B) as H19.
-------------- split.
--------------- exact H18.
--------------- exact H10.
-------------- assert (* Cut *) (euclidean__defs.CongA A D B A B D) as H20.
--------------- apply (@proposition__05.proposition__05 A D B H19).
--------------- assert (* Cut *) (euclidean__defs.Out C A D) as H21.
---------------- apply (@lemma__ray4.lemma__ray4 C A D).
-----------------left.
exact H13.

----------------- exact H5.
---------------- assert (* Cut *) (B = B) as H22.
----------------- apply (@logic.eq__refl Point B).
----------------- assert (* Cut *) (euclidean__defs.Out C B B) as H23.
------------------ apply (@lemma__ray4.lemma__ray4 C B B).
-------------------right.
left.
exact H22.

------------------- exact H16.
------------------ assert (* Cut *) (~(euclidean__axioms.Col A C B)) as H24.
------------------- intro H24.
assert (* Cut *) (euclidean__axioms.Col A B C) as H25.
-------------------- assert (* Cut *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A B C) /\ (euclidean__axioms.Col B C A))))) as H25.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder A C B H24).
--------------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H32.
-------------------- apply (@H11).
---------------------apply (@euclidean__tactics.not__nCol__Col B C D).
----------------------intro H26.
apply (@euclidean__tactics.Col__nCol__False A B C H1 H25).


------------------- assert (* Cut *) (euclidean__defs.CongA A C B A C B) as H25.
-------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive A C B).
---------------------apply (@euclidean__tactics.nCol__notCol A C B H24).

-------------------- assert (* Cut *) (euclidean__defs.CongA A C B D C B) as H26.
--------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper A C B A C B D B H25 H21 H23).
--------------------- assert (* Cut *) (euclidean__defs.LtA A C B B D A) as H27.
---------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 D C B B D A A C B H14 H26).
---------------------- assert (* Cut *) (euclidean__defs.CongA A D B B D A) as H28.
----------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A D B H18).
----------------------- assert (* Cut *) (euclidean__defs.LtA A C B A D B) as H29.
------------------------ apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence A C B B D A A D B H27 H28).
------------------------ assert (* Cut *) (euclidean__defs.CongA A B D A D B) as H30.
------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A D B A B D H20).
------------------------- assert (* Cut *) (euclidean__defs.LtA A C B A B D) as H31.
-------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence A C B A D B A B D H29 H30).
-------------------------- assert (* Cut *) (~(euclidean__axioms.Col B C A)) as H32.
--------------------------- intro H32.
assert (* Cut *) (euclidean__axioms.Col A B C) as H33.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H33.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C A H32).
----------------------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H38.
---------------------------- apply (@H11).
-----------------------------apply (@euclidean__tactics.not__nCol__Col B C D).
------------------------------intro H34.
apply (@euclidean__tactics.Col__nCol__False A B C H1 H33).


--------------------------- assert (* Cut *) (euclidean__defs.CongA B C A A C B) as H33.
---------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B C A).
-----------------------------apply (@euclidean__tactics.nCol__notCol B C A H32).

---------------------------- assert (* Cut *) (euclidean__defs.LtA B C A A B D) as H34.
----------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 A C B A B D B C A H31 H33).
----------------------------- assert (* Cut *) (C = C) as H35.
------------------------------ apply (@logic.eq__refl Point C).
------------------------------ assert (* Cut *) (A = A) as H36.
------------------------------- apply (@logic.eq__refl Point A).
------------------------------- assert (* Cut *) (euclidean__defs.Out B C C) as H37.
-------------------------------- apply (@lemma__ray4.lemma__ray4 B C C).
---------------------------------right.
left.
exact H35.

--------------------------------- exact H15.
-------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H38.
--------------------------------- apply (@lemma__ray4.lemma__ray4 B A A).
----------------------------------right.
left.
exact H36.

---------------------------------- exact H3.
--------------------------------- assert (* Cut *) (~(euclidean__axioms.Col A B D)) as H39.
---------------------------------- intro H39.
assert (* Cut *) (euclidean__axioms.Col A D B) as H40.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A))))) as H40.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder A B D H39).
------------------------------------ destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H47.
----------------------------------- apply (@H11).
------------------------------------apply (@euclidean__tactics.not__nCol__Col B C D).
-------------------------------------intro H41.
apply (@H17 H40).


---------------------------------- assert (* Cut *) (euclidean__defs.CongA A B D A B D) as H40.
----------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive A B D).
------------------------------------apply (@euclidean__tactics.nCol__notCol A B D H39).

----------------------------------- assert (* Cut *) (euclidean__defs.LtA A B D A B C) as H41.
------------------------------------ exists A.
exists D.
exists C.
split.
------------------------------------- exact H9.
------------------------------------- split.
-------------------------------------- exact H38.
-------------------------------------- split.
--------------------------------------- exact H37.
--------------------------------------- exact H40.
------------------------------------ assert (* Cut *) (euclidean__defs.LtA B C A A B C) as H42.
------------------------------------- apply (@lemma__angleordertransitive.lemma__angleordertransitive B C A A B D A B C H34 H41).
------------------------------------- exact H42.
Qed.
