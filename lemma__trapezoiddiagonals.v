Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__diagonalsbisect.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__trapezoiddiagonals : forall A B C D E, (euclidean__defs.PG A B C D) -> ((euclidean__axioms.BetS A E D) -> (exists X, (euclidean__axioms.BetS B X D) /\ (euclidean__axioms.BetS C X E))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
assert (* Cut *) (euclidean__defs.Par A B C D) as H1.
- destruct H as [H1 H2].
exact H1.
- assert (* Cut *) (euclidean__defs.Par A D B C) as H2.
-- destruct H as [H2 H3].
exact H3.
-- assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H3.
--- assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H3 by exact H2.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H3.
destruct __TmpHyp as [x H4].
destruct H4 as [x0 H5].
destruct H5 as [x1 H6].
destruct H6 as [x2 H7].
destruct H7 as [x3 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H29 by exact H1.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H29.
destruct __TmpHyp0 as [x4 H30].
destruct H30 as [x5 H31].
destruct H31 as [x6 H32].
destruct H32 as [x7 H33].
destruct H33 as [x8 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H51.
--- assert (* Cut *) (euclidean__axioms.neq A B) as H4.
---- assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H4 by exact H2.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H4.
destruct __TmpHyp as [x H5].
destruct H5 as [x0 H6].
destruct H6 as [x1 H7].
destruct H7 as [x2 H8].
destruct H8 as [x3 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H30 by exact H1.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H30.
destruct __TmpHyp0 as [x4 H31].
destruct H31 as [x5 H32].
destruct H32 as [x6 H33].
destruct H33 as [x7 H34].
destruct H34 as [x8 H35].
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
exact H36.
---- assert (* Cut *) (euclidean__axioms.neq C D) as H5.
----- assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H5 by exact H2.
assert (exists U V u v X, (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D U) /\ ((euclidean__axioms.Col A D V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col B C u) /\ ((euclidean__axioms.Col B C v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A D B C)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H5.
destruct __TmpHyp as [x H6].
destruct H6 as [x0 H7].
destruct H7 as [x1 H8].
destruct H8 as [x2 H9].
destruct H9 as [x3 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H31 by exact H1.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp0 by exact H31.
destruct __TmpHyp0 as [x4 H32].
destruct H32 as [x5 H33].
destruct H33 as [x6 H34].
destruct H34 as [x7 H35].
destruct H35 as [x8 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H39.
----- assert (* Cut *) (exists M, (euclidean__defs.Midpoint A M C) /\ (euclidean__defs.Midpoint B M D)) as H6.
------ apply (@lemma__diagonalsbisect.lemma__diagonalsbisect A B C D H).
------ destruct H6 as [M H7].
destruct H7 as [H8 H9].
assert (* Cut *) (euclidean__axioms.BetS A M C) as H10.
------- destruct H9 as [H10 H11].
destruct H8 as [H12 H13].
exact H12.
------- assert (* Cut *) (euclidean__axioms.Cong A M M C) as H11.
-------- destruct H9 as [H11 H12].
destruct H8 as [H13 H14].
exact H14.
-------- assert (* Cut *) (euclidean__axioms.BetS B M D) as H12.
--------- destruct H9 as [H12 H13].
destruct H8 as [H14 H15].
exact H12.
--------- assert (* Cut *) (euclidean__axioms.Cong B M M D) as H13.
---------- destruct H9 as [H13 H14].
destruct H8 as [H15 H16].
exact H14.
---------- assert (* Cut *) (euclidean__axioms.Cong B M D M) as H14.
----------- assert (* Cut *) ((euclidean__axioms.Cong M B D M) /\ ((euclidean__axioms.Cong M B M D) /\ (euclidean__axioms.Cong B M D M))) as H14.
------------ apply (@lemma__congruenceflip.lemma__congruenceflip B M M D H13).
------------ destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H18.
----------- assert (* Cut *) (B = B) as H15.
------------ apply (@logic.eq__refl Point B).
------------ assert (* Cut *) (~(euclidean__axioms.Col B D C)) as H16.
------------- intro H16.
assert (* Cut *) (euclidean__axioms.Col C D B) as H17.
-------------- assert (* Cut *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B))))) as H17.
--------------- apply (@lemma__collinearorder.lemma__collinearorder B D C H16).
--------------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H25.
-------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H18.
--------------- right.
right.
left.
exact H15.
--------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H19.
---------------- exists B.
split.
----------------- exact H4.
----------------- split.
------------------ exact H5.
------------------ split.
------------------- exact H18.
------------------- exact H17.
---------------- apply (@H3 H19).
------------- assert (* Cut *) (euclidean__axioms.Cong M A M C) as H17.
-------------- assert (* Cut *) ((euclidean__axioms.Cong M A C M) /\ ((euclidean__axioms.Cong M A M C) /\ (euclidean__axioms.Cong A M C M))) as H17.
--------------- apply (@lemma__congruenceflip.lemma__congruenceflip A M M C H11).
--------------- destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H20.
-------------- assert (* Cut *) (exists P, (euclidean__axioms.BetS B E P) /\ (euclidean__axioms.BetS C D P)) as H18.
--------------- apply (@euclidean__axioms.postulate__Euclid5 E B D A C M H10 H12 H0 H14 H17).
----------------apply (@euclidean__tactics.nCol__notCol B D C H16).

--------------- destruct H18 as [P H19].
destruct H19 as [H20 H21].
assert (* Cut *) (~(euclidean__axioms.Col B P C)) as H22.
---------------- intro H22.
assert (* Cut *) (euclidean__axioms.Col P C B) as H23.
----------------- assert (* Cut *) ((euclidean__axioms.Col P B C) /\ ((euclidean__axioms.Col P C B) /\ ((euclidean__axioms.Col C B P) /\ ((euclidean__axioms.Col B C P) /\ (euclidean__axioms.Col C P B))))) as H23.
------------------ apply (@lemma__collinearorder.lemma__collinearorder B P C H22).
------------------ destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H26.
----------------- assert (* Cut *) (euclidean__axioms.Col C D P) as H24.
------------------ right.
right.
right.
right.
left.
exact H21.
------------------ assert (* Cut *) (euclidean__axioms.Col P C D) as H25.
------------------- assert (* Cut *) ((euclidean__axioms.Col D C P) /\ ((euclidean__axioms.Col D P C) /\ ((euclidean__axioms.Col P C D) /\ ((euclidean__axioms.Col C P D) /\ (euclidean__axioms.Col P D C))))) as H25.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder C D P H24).
-------------------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H30.
------------------- assert (* Cut *) (euclidean__axioms.neq C P) as H26.
-------------------- assert (* Cut *) ((euclidean__axioms.neq D P) /\ ((euclidean__axioms.neq C D) /\ (euclidean__axioms.neq C P))) as H26.
--------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C D P H21).
--------------------- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H30.
-------------------- assert (* Cut *) (euclidean__axioms.neq P C) as H27.
--------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C P H26).
--------------------- assert (* Cut *) (euclidean__axioms.Col C B D) as H28.
---------------------- apply (@euclidean__tactics.not__nCol__Col C B D).
-----------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False C B D H28).
------------------------apply (@lemma__collinear4.lemma__collinear4 P C B D H23 H25 H27).


---------------------- assert (* Cut *) (euclidean__axioms.Col C D B) as H29.
----------------------- assert (* Cut *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H29.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder C B D H28).
------------------------ destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H36.
----------------------- assert (* Cut *) (euclidean__axioms.Col A B B) as H30.
------------------------ right.
right.
left.
exact H15.
------------------------ assert (* Cut *) (euclidean__defs.Meet A B C D) as H31.
------------------------- exists B.
split.
-------------------------- exact H4.
-------------------------- split.
--------------------------- exact H5.
--------------------------- split.
---------------------------- exact H30.
---------------------------- exact H29.
------------------------- apply (@H3 H31).
---------------- assert (* Cut *) (exists H', (euclidean__axioms.BetS B H' D) /\ (euclidean__axioms.BetS C H' E)) as H23.
----------------- apply (@euclidean__axioms.postulate__Pasch__inner B C P E D H20 H21).
------------------apply (@euclidean__tactics.nCol__notCol B P C H22).

----------------- destruct H23 as [H' H24].
destruct H24 as [H25 H26].
exists H'.
split.
------------------ exact H25.
------------------ exact H26.
Qed.
