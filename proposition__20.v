Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__05.
Require Export proposition__19.
Definition proposition__20 : forall A B C, (euclidean__axioms.Triangle A B C) -> (euclidean__defs.TG B A A C B C).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (euclidean__axioms.nCol A B C) as H0 by exact H.
assert (* Cut *) (~(B = A)) as H1.
- intro H1.
assert (* Cut *) (euclidean__axioms.Col B A C) as H2.
-- left.
exact H1.
-- assert (* Cut *) (euclidean__axioms.Col A B C) as H3.
--- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H3.
---- apply (@lemma__collinearorder.lemma__collinearorder B A C H2).
---- destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H4.
--- apply (@euclidean__tactics.Col__nCol__False A B C H0 H3).
- assert (* Cut *) (~(B = C)) as H2.
-- intro H2.
assert (* Cut *) (euclidean__axioms.Col A B C) as H3.
--- right.
right.
left.
exact H2.
--- apply (@euclidean__tactics.Col__nCol__False A B C H0 H3).
-- assert (* Cut *) (euclidean__axioms.neq C B) as H3.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B C H2).
--- assert (* Cut *) (~(C = A)) as H4.
---- intro H4.
assert (* Cut *) (euclidean__axioms.Col B C A) as H5.
----- right.
right.
left.
exact H4.
----- assert (* Cut *) (euclidean__axioms.Col A B C) as H6.
------ assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H6.
------- apply (@lemma__collinearorder.lemma__collinearorder B C A H5).
------- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H11.
------ apply (@euclidean__tactics.Col__nCol__False A B C H0 H6).
---- assert (* Cut *) (exists D, (euclidean__axioms.BetS B A D) /\ (euclidean__axioms.Cong A D C A)) as H5.
----- apply (@lemma__extension.lemma__extension B A C A H1 H4).
----- destruct H5 as [D H6].
destruct H6 as [H7 H8].
assert (* Cut *) (euclidean__axioms.neq A D) as H9.
------ assert (* Cut *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B D))) as H9.
------- apply (@lemma__betweennotequal.lemma__betweennotequal B A D H7).
------- destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
exact H10.
------ assert (* Cut *) (euclidean__axioms.neq D A) as H10.
------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A D H9).
------- assert (* Cut *) (euclidean__axioms.neq B D) as H11.
-------- assert (* Cut *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B D))) as H11.
--------- apply (@lemma__betweennotequal.lemma__betweennotequal B A D H7).
--------- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H15.
-------- assert (* Cut *) (euclidean__axioms.neq D B) as H12.
--------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B D H11).
--------- assert (* Cut *) (euclidean__axioms.Cong A D A C) as H13.
---------- assert (* Cut *) ((euclidean__axioms.Cong D A A C) /\ ((euclidean__axioms.Cong D A C A) /\ (euclidean__axioms.Cong A D A C))) as H13.
----------- apply (@lemma__congruenceflip.lemma__congruenceflip A D C A H8).
----------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H17.
---------- assert (* Cut *) (~(euclidean__axioms.Col A D C)) as H14.
----------- intro H14.
assert (* Cut *) (euclidean__axioms.Col B A D) as H15.
------------ right.
right.
right.
right.
left.
exact H7.
------------ assert (* Cut *) (euclidean__axioms.Col D A B) as H16.
------------- assert (* Cut *) ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col A D B) /\ ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col B D A) /\ (euclidean__axioms.Col D A B))))) as H16.
-------------- apply (@lemma__collinearorder.lemma__collinearorder B A D H15).
-------------- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H24.
------------- assert (* Cut *) (euclidean__axioms.Col D A C) as H17.
-------------- assert (* Cut *) ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col A C D) /\ (euclidean__axioms.Col C D A))))) as H17.
--------------- apply (@lemma__collinearorder.lemma__collinearorder A D C H14).
--------------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H18.
-------------- assert (* Cut *) (euclidean__axioms.neq A D) as H18.
--------------- assert (* Cut *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B A) /\ (euclidean__axioms.neq B D))) as H18.
---------------- apply (@lemma__betweennotequal.lemma__betweennotequal B A D H7).
---------------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H9.
--------------- assert (euclidean__axioms.neq D A) as H19 by exact H10.
assert (* Cut *) (euclidean__axioms.Col A B C) as H20.
---------------- apply (@euclidean__tactics.not__nCol__Col A B C).
-----------------intro H20.
apply (@euclidean__tactics.Col__nCol__False A B C H20).
------------------apply (@lemma__collinear4.lemma__collinear4 D A B C H16 H17 H19).


---------------- apply (@euclidean__tactics.Col__nCol__False A B C H0 H20).
----------- assert (* Cut *) (~(D = C)) as H15.
------------ intro H15.
assert (* Cut *) (euclidean__axioms.Col A D C) as H16.
------------- right.
right.
left.
exact H15.
------------- apply (@H14 H16).
------------ assert (* Cut *) (euclidean__axioms.Triangle A D C) as H16.
------------- apply (@euclidean__tactics.nCol__notCol A D C H14).
------------- assert (* Cut *) (euclidean__defs.isosceles A D C) as H17.
-------------- split.
--------------- exact H16.
--------------- exact H13.
-------------- assert (* Cut *) (euclidean__defs.CongA A D C A C D) as H18.
--------------- apply (@proposition__05.proposition__05 A D C H17).
--------------- assert (* Cut *) (~(euclidean__axioms.Col A C D)) as H19.
---------------- intro H19.
assert (* Cut *) (euclidean__axioms.Col A D C) as H20.
----------------- assert (* Cut *) ((euclidean__axioms.Col C A D) /\ ((euclidean__axioms.Col C D A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A D C) /\ (euclidean__axioms.Col D C A))))) as H20.
------------------ apply (@lemma__collinearorder.lemma__collinearorder A C D H19).
------------------ destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H27.
----------------- apply (@H14 H20).
---------------- assert (* Cut *) (euclidean__defs.CongA A C D D C A) as H20.
----------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA A C D).
------------------apply (@euclidean__tactics.nCol__notCol A C D H19).

----------------- assert (* Cut *) (euclidean__defs.CongA A D C D C A) as H21.
------------------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A D C A C D D C A H18 H20).
------------------ assert (* Cut *) (D = D) as H22.
------------------- apply (@logic.eq__refl Point D).
------------------- assert (* Cut *) (B = B) as H23.
-------------------- apply (@logic.eq__refl Point B).
-------------------- assert (* Cut *) (C = C) as H24.
--------------------- apply (@logic.eq__refl Point C).
--------------------- assert (* Cut *) (~(C = D)) as H25.
---------------------- intro H25.
assert (* Cut *) (euclidean__axioms.Col A C D) as H26.
----------------------- right.
right.
left.
exact H25.
----------------------- apply (@H14).
------------------------apply (@euclidean__tactics.not__nCol__Col A D C).
-------------------------intro H27.
apply (@H19 H26).


---------------------- assert (* Cut *) (euclidean__defs.Out C D D) as H26.
----------------------- apply (@lemma__ray4.lemma__ray4 C D D).
------------------------right.
left.
exact H22.

------------------------ exact H25.
----------------------- assert (* Cut *) (euclidean__defs.Out C B B) as H27.
------------------------ apply (@lemma__ray4.lemma__ray4 C B B).
-------------------------right.
left.
exact H23.

------------------------- exact H3.
------------------------ assert (* Cut *) (euclidean__axioms.BetS D A B) as H28.
------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B A D H7).
------------------------- assert (* Cut *) (euclidean__defs.LtA A D C D C B) as H29.
-------------------------- exists D.
exists A.
exists B.
split.
--------------------------- exact H28.
--------------------------- split.
---------------------------- exact H26.
---------------------------- split.
----------------------------- exact H27.
----------------------------- exact H21.
-------------------------- assert (* Cut *) (euclidean__defs.Out D A B) as H30.
--------------------------- apply (@lemma__ray4.lemma__ray4 D A B).
----------------------------right.
right.
exact H28.

---------------------------- exact H10.
--------------------------- assert (* Cut *) (euclidean__defs.Out D C C) as H31.
---------------------------- apply (@lemma__ray4.lemma__ray4 D C C).
-----------------------------right.
left.
exact H24.

----------------------------- exact H15.
---------------------------- assert (* Cut *) (euclidean__defs.Out D B B) as H32.
----------------------------- apply (@lemma__ray4.lemma__ray4 D B B).
------------------------------right.
left.
exact H23.

------------------------------ exact H12.
----------------------------- assert (* Cut *) (euclidean__axioms.Cong D B D B) as H33.
------------------------------ apply (@euclidean__axioms.cn__congruencereflexive D B).
------------------------------ assert (* Cut *) (euclidean__axioms.Cong D C D C) as H34.
------------------------------- apply (@euclidean__axioms.cn__congruencereflexive D C).
------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C B C) as H35.
-------------------------------- apply (@euclidean__axioms.cn__congruencereflexive B C).
-------------------------------- assert (* Cut *) (euclidean__defs.CongA A D C B D C) as H36.
--------------------------------- exists B.
exists C.
exists B.
exists C.
split.
---------------------------------- exact H30.
---------------------------------- split.
----------------------------------- exact H31.
----------------------------------- split.
------------------------------------ exact H32.
------------------------------------ split.
------------------------------------- exact H31.
------------------------------------- split.
-------------------------------------- exact H33.
-------------------------------------- split.
--------------------------------------- exact H34.
--------------------------------------- split.
---------------------------------------- exact H35.
---------------------------------------- exact H16.
--------------------------------- assert (* Cut *) (euclidean__defs.CongA B D C A D C) as H37.
---------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A D C B D C H36).
---------------------------------- assert (* Cut *) (euclidean__defs.LtA B D C D C B) as H38.
----------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 A D C D C B B D C H29 H37).
----------------------------------- assert (* Cut *) (~(euclidean__axioms.Col B C D)) as H39.
------------------------------------ intro H39.
assert (* Cut *) (euclidean__axioms.Col B A D) as H40.
------------------------------------- right.
right.
right.
right.
left.
exact H7.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B A) as H41.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B D) /\ ((euclidean__axioms.Col A D B) /\ ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col B D A) /\ (euclidean__axioms.Col D A B))))) as H41.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A D H40).
--------------------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H46.
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B C) as H42.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H42.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C D H39).
---------------------------------------- destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H47.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H43.
---------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D A) /\ (euclidean__axioms.neq D B))) as H43.
----------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal D A B H28).
----------------------------------------- destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H11.
---------------------------------------- assert (euclidean__axioms.neq D B) as H44 by exact H12.
assert (* Cut *) (euclidean__axioms.Col B A C) as H45.
----------------------------------------- apply (@euclidean__tactics.not__nCol__Col B A C).
------------------------------------------intro H45.
apply (@euclidean__tactics.Col__nCol__False B A C H45).
-------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D B A C H41 H42 H44).


----------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H46.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H46.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A C H45).
------------------------------------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H47.
------------------------------------------ apply (@H14).
-------------------------------------------apply (@euclidean__tactics.not__nCol__Col A D C).
--------------------------------------------intro H47.
apply (@euclidean__tactics.Col__nCol__False A B C H0 H46).


------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col C D B)) as H40.
------------------------------------- intro H40.
assert (* Cut *) (euclidean__axioms.Col B C D) as H41.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C B D) /\ (euclidean__axioms.Col B D C))))) as H41.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D B H40).
--------------------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H46.
-------------------------------------- apply (@H14).
---------------------------------------apply (@euclidean__tactics.not__nCol__Col A D C).
----------------------------------------intro H42.
apply (@H39 H41).


------------------------------------- assert (* Cut *) (euclidean__defs.CongA C D B B D C) as H41.
-------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA C D B).
---------------------------------------apply (@euclidean__tactics.nCol__notCol C D B H40).

-------------------------------------- assert (* Cut *) (euclidean__defs.CongA B C D D C B) as H42.
--------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA B C D).
----------------------------------------apply (@euclidean__tactics.nCol__notCol B C D H39).

--------------------------------------- assert (* Cut *) (euclidean__defs.LtA C D B D C B) as H43.
---------------------------------------- apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 B D C D C B C D B H38 H41).
---------------------------------------- assert (* Cut *) (euclidean__defs.LtA C D B B C D) as H44.
----------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence C D B D C B B C D H43 H42).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle B C D) as H45.
------------------------------------------ apply (@euclidean__tactics.nCol__notCol B C D H39).
------------------------------------------ assert (* Cut *) (euclidean__defs.Lt B C B D) as H46.
------------------------------------------- apply (@proposition__19.proposition__19 B C D H45 H44).
------------------------------------------- assert (* Cut *) (euclidean__defs.TG B A A C B C) as H47.
-------------------------------------------- exists D.
split.
--------------------------------------------- exact H7.
--------------------------------------------- split.
---------------------------------------------- exact H13.
---------------------------------------------- exact H46.
-------------------------------------------- exact H47.
Qed.
