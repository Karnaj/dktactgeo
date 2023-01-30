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
Require Export lemma__congruenceflip.
Require Export lemma__crossimpliesopposite.
Require Export lemma__diagonalsmeet.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__ray4.
Require Export logic.
Require Export proposition__26A.
Require Export proposition__29B.
Require Export proposition__34.
Definition lemma__diagonalsbisect : forall A B C D, (euclidean__defs.PG A B C D) -> (exists X, (euclidean__defs.Midpoint A X C) /\ (euclidean__defs.Midpoint B X D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (exists M, (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H0.
- apply (@lemma__diagonalsmeet.lemma__diagonalsmeet A B C D H).
- destruct H0 as [M H1].
destruct H1 as [H2 H3].
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H4.
-- assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as H4 by exact H.
assert ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par A D B C)) as __TmpHyp by exact H4.
destruct __TmpHyp as [H5 H6].
split.
--- exact H5.
--- exact H6.
-- assert (* Cut *) (euclidean__axioms.neq A C) as H5.
--- destruct H4 as [H5 H6].
assert (* Cut *) ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A C))) as H7.
---- apply (@lemma__betweennotequal.lemma__betweennotequal A M C H2).
---- destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H11.
--- assert (* Cut *) (euclidean__axioms.neq B D) as H6.
---- destruct H4 as [H6 H7].
assert (* Cut *) ((euclidean__axioms.neq M D) /\ ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B D))) as H8.
----- apply (@lemma__betweennotequal.lemma__betweennotequal B M D H3).
----- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
exact H12.
---- assert (* Cut *) (euclidean__defs.CR A C B D) as H7.
----- exists M.
split.
------ exact H2.
------ exact H3.
----- assert (* Cut *) (euclidean__defs.Par A B C D) as H8.
------ destruct H4 as [H8 H9].
destruct H as [H10 H11].
exact H8.
------ assert (* Cut *) (euclidean__defs.Par A B D C) as H9.
------- destruct H4 as [H9 H10].
assert (* Cut *) ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))) as H11.
-------- apply (@lemma__parallelflip.lemma__parallelflip A B C D H8).
-------- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H14.
------- assert (* Cut *) (euclidean__axioms.nCol A B D) as H10.
-------- destruct H4 as [H10 H11].
assert (* Cut *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)))) as H12.
--------- apply (@lemma__parallelNC.lemma__parallelNC A B D C H9).
--------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H13.
-------- assert (* Cut *) (euclidean__axioms.TS A B D C) as H11.
--------- destruct H4 as [H11 H12].
assert (* Cut *) ((euclidean__axioms.TS A B D C) /\ ((euclidean__axioms.TS A D B C) /\ ((euclidean__axioms.TS C B D A) /\ (euclidean__axioms.TS C D B A)))) as H13.
---------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite A C B D H7 H10).
---------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H14.
--------- assert (* Cut *) (euclidean__defs.Par B A D C) as H12.
---------- destruct H4 as [H12 H13].
assert (* Cut *) ((euclidean__defs.Par B A D C) /\ ((euclidean__defs.Par A B C D) /\ (euclidean__defs.Par B A C D))) as H14.
----------- apply (@lemma__parallelflip.lemma__parallelflip A B D C H9).
----------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H15.
---------- assert (* Cut *) (euclidean__axioms.BetS C M A) as H13.
----------- destruct H4 as [H13 H14].
apply (@euclidean__axioms.axiom__betweennesssymmetry A M C H2).
----------- assert (* Cut *) (euclidean__axioms.BetS D M B) as H14.
------------ destruct H4 as [H14 H15].
apply (@euclidean__axioms.axiom__betweennesssymmetry B M D H3).
------------ assert (* Cut *) (euclidean__defs.CR B D A C) as H15.
------------- exists M.
split.
-------------- exact H3.
-------------- exact H2.
------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H16.
-------------- destruct H4 as [H16 H17].
assert (* Cut *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)))) as H18.
--------------- apply (@lemma__parallelNC.lemma__parallelNC A B D C H9).
--------------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H24.
-------------- assert (* Cut *) (euclidean__axioms.nCol B A C) as H17.
--------------- destruct H4 as [H17 H18].
assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H19.
---------------- apply (@lemma__NCorder.lemma__NCorder A B C H16).
---------------- destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H20.
--------------- assert (* Cut *) (euclidean__axioms.TS B A C D) as H18.
---------------- destruct H4 as [H18 H19].
assert (* Cut *) ((euclidean__axioms.TS B A C D) /\ ((euclidean__axioms.TS B C A D) /\ ((euclidean__axioms.TS D A C B) /\ (euclidean__axioms.TS D C A B)))) as H20.
----------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite B D A C H15 H17).
----------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H21.
---------------- assert (* Cut *) (euclidean__axioms.Cong A B D C) as H19.
----------------- destruct H4 as [H19 H20].
assert (* Cut *) ((euclidean__axioms.Cong A D B C) /\ ((euclidean__axioms.Cong A B D C) /\ ((euclidean__defs.CongA B A D D C B) /\ ((euclidean__defs.CongA A D C C B A) /\ (euclidean__axioms.Cong__3 B A D D C B))))) as H21.
------------------ apply (@proposition__34.proposition__34 A D B C H).
------------------ destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H24.
----------------- assert (* Cut *) (euclidean__axioms.Cong A B C D) as H20.
------------------ destruct H4 as [H20 H21].
assert (* Cut *) ((euclidean__axioms.Cong B A C D) /\ ((euclidean__axioms.Cong B A D C) /\ (euclidean__axioms.Cong A B C D))) as H22.
------------------- apply (@lemma__congruenceflip.lemma__congruenceflip A B D C H19).
------------------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H26.
------------------ assert (* Cut *) (~(euclidean__axioms.Col M A B)) as H21.
------------------- intro H21.
assert (* Cut *) (euclidean__axioms.Col A M C) as H22.
-------------------- right.
right.
right.
right.
left.
exact H2.
-------------------- assert (* Cut *) (euclidean__axioms.Col M A C) as H23.
--------------------- destruct H4 as [H23 H24].
assert (* Cut *) ((euclidean__axioms.Col M A C) /\ ((euclidean__axioms.Col M C A) /\ ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A))))) as H25.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder A M C H22).
---------------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H26.
--------------------- assert (* Cut *) (euclidean__axioms.neq A M) as H24.
---------------------- destruct H4 as [H24 H25].
assert (* Cut *) ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A C))) as H26.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A M C H2).
----------------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H29.
---------------------- assert (* Cut *) (euclidean__axioms.neq M A) as H25.
----------------------- destruct H4 as [H25 H26].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A M H24).
----------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H26.
------------------------ destruct H4 as [H26 H27].
apply (@euclidean__tactics.not__nCol__Col A B C).
-------------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False A B C H28).
--------------------------apply (@lemma__collinear4.lemma__collinear4 M A B C H21 H23 H25).


------------------------ assert (* Cut *) (euclidean__axioms.nCol A B C) as H27.
------------------------- destruct H4 as [H27 H28].
assert (* Cut *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol B D C) /\ ((euclidean__axioms.nCol A D C) /\ (euclidean__axioms.nCol B A C)))) as H29.
-------------------------- apply (@lemma__parallelNC.lemma__parallelNC B A D C H12).
-------------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H16.
------------------------- apply (@euclidean__tactics.Col__nCol__False A B C H27 H26).
------------------- assert (* Cut *) (euclidean__axioms.Triangle M A B) as H22.
-------------------- apply (@euclidean__tactics.nCol__notCol M A B H21).
-------------------- assert (* Cut *) (~(euclidean__axioms.Col M C D)) as H23.
--------------------- intro H23.
assert (* Cut *) (euclidean__axioms.Col A M C) as H24.
---------------------- right.
right.
right.
right.
left.
exact H2.
---------------------- assert (* Cut *) (euclidean__axioms.Col M C A) as H25.
----------------------- destruct H4 as [H25 H26].
assert (* Cut *) ((euclidean__axioms.Col M A C) /\ ((euclidean__axioms.Col M C A) /\ ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A))))) as H27.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder A M C H24).
------------------------ destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H30.
----------------------- assert (* Cut *) (euclidean__axioms.neq M C) as H26.
------------------------ destruct H4 as [H26 H27].
assert (* Cut *) ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A C))) as H28.
------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A M C H2).
------------------------- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H29.
------------------------ assert (* Cut *) (euclidean__axioms.Col C D A) as H27.
------------------------- destruct H4 as [H27 H28].
apply (@euclidean__tactics.not__nCol__Col C D A).
--------------------------intro H29.
apply (@euclidean__tactics.Col__nCol__False C D A H29).
---------------------------apply (@lemma__collinear4.lemma__collinear4 M C D A H23 H25 H26).


------------------------- assert (* Cut *) (euclidean__axioms.Col A C D) as H28.
-------------------------- destruct H4 as [H28 H29].
assert (* Cut *) ((euclidean__axioms.Col D C A) /\ ((euclidean__axioms.Col D A C) /\ ((euclidean__axioms.Col A C D) /\ ((euclidean__axioms.Col C A D) /\ (euclidean__axioms.Col A D C))))) as H30.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D A H27).
--------------------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H35.
-------------------------- assert (* Cut *) (euclidean__axioms.nCol A C D) as H29.
--------------------------- destruct H4 as [H29 H30].
assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H31.
---------------------------- apply (@lemma__parallelNC.lemma__parallelNC A B C D H8).
---------------------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H34.
--------------------------- apply (@H21).
----------------------------apply (@euclidean__tactics.not__nCol__Col M A B).
-----------------------------intro H30.
apply (@euclidean__tactics.Col__nCol__False A C D H29 H28).


--------------------- assert (* Cut *) (euclidean__axioms.Triangle M C D) as H24.
---------------------- apply (@euclidean__tactics.nCol__notCol M C D H23).
---------------------- assert (* Cut *) (euclidean__defs.Par B A C D) as H25.
----------------------- destruct H4 as [H25 H26].
assert (* Cut *) ((euclidean__defs.Par A B D C) /\ ((euclidean__defs.Par B A C D) /\ (euclidean__defs.Par A B C D))) as H27.
------------------------ apply (@lemma__parallelflip.lemma__parallelflip B A D C H12).
------------------------ destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H30.
----------------------- assert (* Cut *) (euclidean__defs.CongA B A C A C D) as H26.
------------------------ destruct H4 as [H26 H27].
apply (@proposition__29B.proposition__29B B D A C H25 H18).
------------------------ assert (* Cut *) (euclidean__defs.CongA B A C B A C) as H27.
------------------------- destruct H4 as [H27 H28].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive B A C H17).
------------------------- assert (* Cut *) (euclidean__defs.Out A C M) as H28.
-------------------------- destruct H4 as [H28 H29].
apply (@lemma__ray4.lemma__ray4 A C M).
---------------------------left.
exact H2.

--------------------------- exact H5.
-------------------------- assert (* Cut *) (B = B) as H29.
--------------------------- destruct H4 as [H29 H30].
apply (@logic.eq__refl Point B).
--------------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H30.
---------------------------- destruct H4 as [H30 H31].
assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol A C D) /\ (euclidean__axioms.nCol B A D)))) as H32.
----------------------------- apply (@lemma__parallelNC.lemma__parallelNC B A C D H25).
----------------------------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H16.
---------------------------- assert (* Cut *) (euclidean__axioms.neq A B) as H31.
----------------------------- destruct H4 as [H31 H32].
assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H33.
------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct A B C H30).
------------------------------ destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H34.
----------------------------- assert (* Cut *) (euclidean__defs.Out A B B) as H32.
------------------------------ destruct H4 as [H32 H33].
apply (@lemma__ray4.lemma__ray4 A B B).
-------------------------------right.
left.
exact H29.

------------------------------- exact H31.
------------------------------ assert (* Cut *) (euclidean__defs.CongA B A C B A M) as H33.
------------------------------- destruct H4 as [H33 H34].
apply (@lemma__equalangleshelper.lemma__equalangleshelper B A C B A C B M H27 H32 H28).
------------------------------- assert (* Cut *) (euclidean__defs.CongA B A M B A C) as H34.
-------------------------------- destruct H4 as [H34 H35].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric B A C B A M H33).
-------------------------------- assert (* Cut *) (euclidean__defs.CongA B A M A C D) as H35.
--------------------------------- destruct H4 as [H35 H36].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive B A M B A C A C D H34 H26).
--------------------------------- assert (* Cut *) (D = D) as H36.
---------------------------------- destruct H4 as [H36 H37].
apply (@logic.eq__refl Point D).
---------------------------------- assert (* Cut *) (euclidean__axioms.nCol A C D) as H37.
----------------------------------- destruct H4 as [H37 H38].
assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol A C D) /\ (euclidean__axioms.nCol B A D)))) as H39.
------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC B A C D H25).
------------------------------------ destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H44.
----------------------------------- assert (* Cut *) (euclidean__axioms.neq C D) as H38.
------------------------------------ destruct H4 as [H38 H39].
assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))))) as H40.
------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct A C D H37).
------------------------------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H43.
------------------------------------ assert (* Cut *) (euclidean__axioms.neq C A) as H39.
------------------------------------- destruct H4 as [H39 H40].
assert (* Cut *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D A)))))) as H41.
-------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct A C D H37).
-------------------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
exact H48.
------------------------------------- assert (* Cut *) (euclidean__defs.Out C D D) as H40.
-------------------------------------- destruct H4 as [H40 H41].
apply (@lemma__ray4.lemma__ray4 C D D).
---------------------------------------right.
left.
exact H36.

--------------------------------------- exact H38.
-------------------------------------- assert (* Cut *) (euclidean__defs.Out C A M) as H41.
--------------------------------------- destruct H4 as [H41 H42].
apply (@lemma__ray4.lemma__ray4 C A M).
----------------------------------------left.
exact H13.

---------------------------------------- exact H39.
--------------------------------------- assert (* Cut *) (euclidean__defs.CongA A C D A C D) as H42.
---------------------------------------- destruct H4 as [H42 H43].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive A C D H37).
---------------------------------------- assert (* Cut *) (euclidean__defs.CongA A C D M C D) as H43.
----------------------------------------- destruct H4 as [H43 H44].
apply (@lemma__equalangleshelper.lemma__equalangleshelper A C D A C D M D H42 H41 H40).
----------------------------------------- assert (* Cut *) (euclidean__defs.CongA B A M M C D) as H44.
------------------------------------------ destruct H4 as [H44 H45].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive B A M A C D M C D H35 H43).
------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A C D) as H45.
------------------------------------------- destruct H4 as [H45 H46].
assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol A C D) /\ (euclidean__axioms.nCol B A D)))) as H47.
-------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC B A C D H25).
-------------------------------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H37.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A M C) as H46.
-------------------------------------------- right.
right.
right.
right.
left.
exact H2.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C M) as H47.
--------------------------------------------- destruct H4 as [H47 H48].
assert (* Cut *) ((euclidean__axioms.Col M A C) /\ ((euclidean__axioms.Col M C A) /\ ((euclidean__axioms.Col C A M) /\ ((euclidean__axioms.Col A C M) /\ (euclidean__axioms.Col C M A))))) as H49.
---------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A M C H46).
---------------------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H56.
--------------------------------------------- assert (* Cut *) (C = C) as H48.
---------------------------------------------- destruct H4 as [H48 H49].
apply (@logic.eq__refl Point C).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A C C) as H49.
----------------------------------------------- right.
right.
left.
exact H48.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M C) as H50.
------------------------------------------------ destruct H4 as [H50 H51].
assert (* Cut *) ((euclidean__axioms.neq M C) /\ ((euclidean__axioms.neq A M) /\ (euclidean__axioms.neq A C))) as H52.
------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal A M C H2).
------------------------------------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H53.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol M C D) as H51.
------------------------------------------------- destruct H4 as [H51 H52].
exact H24.
------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA M C D D C M) as H52.
-------------------------------------------------- destruct H4 as [H52 H53].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA M C D H51).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B A M D C M) as H53.
--------------------------------------------------- destruct H4 as [H53 H54].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive B A M M C D D C M H44 H52).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B D C) as H54.
---------------------------------------------------- destruct H4 as [H54 H55].
assert (* Cut *) ((euclidean__defs.Par A B C D) /\ ((euclidean__defs.Par B A D C) /\ (euclidean__defs.Par A B D C))) as H56.
----------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip B A C D H25).
----------------------------------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H60.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B D B D C) as H55.
----------------------------------------------------- destruct H4 as [H55 H56].
apply (@proposition__29B.proposition__29B A C B D H54 H11).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B D A B D) as H56.
------------------------------------------------------ destruct H4 as [H56 H57].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive A B D H10).
------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B D M) as H57.
------------------------------------------------------- destruct H4 as [H57 H58].
apply (@lemma__ray4.lemma__ray4 B D M).
--------------------------------------------------------left.
exact H3.

-------------------------------------------------------- exact H6.
------------------------------------------------------- assert (* Cut *) (A = A) as H58.
-------------------------------------------------------- destruct H4 as [H58 H59].
apply (@logic.eq__refl Point A).
-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B A D) as H59.
--------------------------------------------------------- destruct H4 as [H59 H60].
assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C D) /\ ((euclidean__axioms.nCol A C D) /\ (euclidean__axioms.nCol B A D)))) as H61.
---------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC B A C D H25).
---------------------------------------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
exact H67.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H60.
---------------------------------------------------------- destruct H4 as [H60 H61].
assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D A) /\ (euclidean__axioms.neq D B)))))) as H62.
----------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct B A D H59).
----------------------------------------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H63.
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B A A) as H61.
----------------------------------------------------------- destruct H4 as [H61 H62].
apply (@lemma__ray4.lemma__ray4 B A A).
------------------------------------------------------------right.
left.
exact H58.

------------------------------------------------------------ exact H60.
----------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B D A B M) as H62.
------------------------------------------------------------ destruct H4 as [H62 H63].
apply (@lemma__equalangleshelper.lemma__equalangleshelper A B D A B D A M H56 H61 H57).
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA A B M A B D) as H63.
------------------------------------------------------------- destruct H4 as [H63 H64].
apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A B D A B M H62).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B M B D C) as H64.
-------------------------------------------------------------- destruct H4 as [H64 H65].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B M A B D B D C H63 H55).
-------------------------------------------------------------- assert (* Cut *) (C = C) as H65.
--------------------------------------------------------------- destruct H4 as [H65 H66].
exact H48.
--------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B D C) as H66.
---------------------------------------------------------------- destruct H4 as [H66 H67].
assert (* Cut *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)))) as H68.
----------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC A B D C H54).
----------------------------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H73.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H67.
----------------------------------------------------------------- destruct H4 as [H67 H68].
assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C B)))))) as H69.
------------------------------------------------------------------ apply (@lemma__NCdistinct.lemma__NCdistinct B D C H66).
------------------------------------------------------------------ destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H72.
----------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H68.
------------------------------------------------------------------ destruct H4 as [H68 H69].
assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C B)))))) as H70.
------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct B D C H66).
------------------------------------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H77.
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Out D C C) as H69.
------------------------------------------------------------------- destruct H4 as [H69 H70].
apply (@lemma__ray4.lemma__ray4 D C C).
--------------------------------------------------------------------right.
left.
exact H65.

-------------------------------------------------------------------- exact H67.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out D B M) as H70.
-------------------------------------------------------------------- destruct H4 as [H70 H71].
apply (@lemma__ray4.lemma__ray4 D B M).
---------------------------------------------------------------------left.
exact H14.

--------------------------------------------------------------------- exact H68.
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B D C B D C) as H71.
--------------------------------------------------------------------- destruct H4 as [H71 H72].
apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive B D C H66).
--------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA B D C M D C) as H72.
---------------------------------------------------------------------- destruct H4 as [H72 H73].
apply (@lemma__equalangleshelper.lemma__equalangleshelper B D C B D C M C H71 H70 H69).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B M M D C) as H73.
----------------------------------------------------------------------- destruct H4 as [H73 H74].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B M B D C M D C H64 H72).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol B D C) as H74.
------------------------------------------------------------------------ destruct H4 as [H74 H75].
assert (* Cut *) ((euclidean__axioms.nCol A B D) /\ ((euclidean__axioms.nCol A D C) /\ ((euclidean__axioms.nCol B D C) /\ (euclidean__axioms.nCol A B C)))) as H76.
------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC A B D C H54).
------------------------------------------------------------------------- destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
exact H66.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col B M D) as H75.
------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H3.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B D M) as H76.
-------------------------------------------------------------------------- destruct H4 as [H76 H77].
assert (* Cut *) ((euclidean__axioms.Col M B D) /\ ((euclidean__axioms.Col M D B) /\ ((euclidean__axioms.Col D B M) /\ ((euclidean__axioms.Col B D M) /\ (euclidean__axioms.Col D M B))))) as H78.
--------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B M D H75).
--------------------------------------------------------------------------- destruct H78 as [H79 H80].
destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
exact H85.
-------------------------------------------------------------------------- assert (* Cut *) (D = D) as H77.
--------------------------------------------------------------------------- destruct H4 as [H77 H78].
exact H36.
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B D D) as H78.
---------------------------------------------------------------------------- right.
right.
left.
exact H77.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq M D) as H79.
----------------------------------------------------------------------------- destruct H4 as [H79 H80].
assert (* Cut *) ((euclidean__axioms.neq M D) /\ ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B D))) as H81.
------------------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal B M D H3).
------------------------------------------------------------------------------ destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H82.
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol M D C) as H80.
------------------------------------------------------------------------------ destruct H4 as [H80 H81].
apply (@euclidean__tactics.nCol__notCol M D C).
-------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col M D C).
--------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper B D C M D H74 H76 H78 H79).


------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.CongA M D C C D M) as H81.
------------------------------------------------------------------------------- destruct H4 as [H81 H82].
apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA M D C H80).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA A B M C D M) as H82.
-------------------------------------------------------------------------------- destruct H4 as [H82 H83].
apply (@lemma__equalanglestransitive.lemma__equalanglestransitive A B M M D C C D M H73 H81).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA M A B M C D) as H83.
--------------------------------------------------------------------------------- destruct H4 as [H83 H84].
apply (@lemma__equalanglesflip.lemma__equalanglesflip B A M D C M H53).
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong M A M C) /\ ((euclidean__axioms.Cong M B M D) /\ (euclidean__defs.CongA A M B C M D))) as H84.
---------------------------------------------------------------------------------- destruct H4 as [H84 H85].
apply (@proposition__26A.proposition__26A M A B M C D H22 H51 H83 H82 H20).
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A M M C) as H85.
----------------------------------------------------------------------------------- destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H4 as [H89 H90].
assert (* Cut *) ((euclidean__axioms.Cong A M C M) /\ ((euclidean__axioms.Cong A M M C) /\ (euclidean__axioms.Cong M A C M))) as H91.
------------------------------------------------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip M A M C H85).
------------------------------------------------------------------------------------ destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H94.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B M M D) as H86.
------------------------------------------------------------------------------------ destruct H84 as [H86 H87].
destruct H87 as [H88 H89].
destruct H4 as [H90 H91].
assert (* Cut *) ((euclidean__axioms.Cong B M D M) /\ ((euclidean__axioms.Cong B M M D) /\ (euclidean__axioms.Cong M B D M))) as H92.
------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip M B M D H88).
------------------------------------------------------------------------------------- destruct H92 as [H93 H94].
destruct H94 as [H95 H96].
exact H95.
------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Midpoint A M C) as H87.
------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------- exact H2.
-------------------------------------------------------------------------------------- exact H85.
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Midpoint B M D) as H88.
-------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------- exact H3.
--------------------------------------------------------------------------------------- exact H86.
-------------------------------------------------------------------------------------- exists M.
split.
--------------------------------------------------------------------------------------- exact H87.
--------------------------------------------------------------------------------------- exact H88.
Qed.
